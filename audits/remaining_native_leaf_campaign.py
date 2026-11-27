"""Checkpoint disjoint first- and second-operation rectangles for the residual native leaf census."""

import argparse
import fcntl
import json
import re
import subprocess
import time
from collections import defaultdict
from pathlib import Path

import numpy as np

from clocked_native_path import ALU, Catalog, primitive
from clocked_native_path_campaign import hash_file, save

MODES = {'store': (1, 2), 'last-read': (4, 5, 6), 'last-alu': (1, 2, 3)}
NATIVE = re.compile(r'FULL PATH (last-read|last-alu) (\d+) (\d+) ([\d,]+) ([\d,]+) ([\d,]+) ([\d,]+) support (\d+)')
RELAXED = re.compile(r'RELAXED STORE (\d+),(\d+) op ([\d,]+) ([\d,]+) guard ([\d,]+) store (\d+) before ([01]) avoided (\d+) support (\d+)')


def unpack(text):
    return tuple(map(int, text.split(',')))


def check_witness(output, threshold=37):
    raw = output.strip()
    final = NATIVE.fullmatch(raw)
    store = RELAXED.fullmatch(raw)
    if final:
        mode = final[1]
        direct, access = map(int, final.group(2, 3))
        ops = final.group(4, 5, 6)
        guard = unpack(final[7])
        claimed = int(final[8])
    elif store:
        mode = 'store'
        direct, access = map(int, store.group(1, 2))
        ops = store.group(3, 4)
        guard = unpack(store[5])
        claimed = int(store[9])
    else:
        raise ValueError('unrecognized candidate report')
    cat = Catalog()
    shape = cat.sat.shape
    regs = {**{j: j for j in range(16)},
            **{16+j: cat.original[j] for j in range(4) if direct >> j & 1}}
    fresh = np.ones(shape, dtype=bool)
    pointers = []
    for i, code in enumerate(ops):
        op, a, b = unpack(code)
        base = 20 + 2*i
        value = np.broadcast_to(primitive(ALU[op], regs[a], regs[b]), shape)
        regs[base] = value
        if access >> i & 1:
            fresh &= value < 4
            for j in range(4):
                if direct >> j & 1:
                    fresh &= value != j
            for prior in pointers:
                fresh &= value != prior
            pointers.append(value)
            regs[base+1] = np.select([value == j for j in range(4)], cat.original, default=0)
    a, b, kind, inverse = guard
    if kind in (2, 4):
        a, b = b, a
    test = ('eq', 'lt', 'lt', 'slt', 'slt')[kind]
    passed = np.broadcast_to(np.asarray(primitive(test, regs[a], regs[b]), dtype=bool), shape).copy()
    passed ^= bool(inverse)
    if store:
        addr, before, avoided = map(int, store.group(6, 7, 8))
        assert len(pointers) == 1 and not (avoided & ~direct)
        if before:
            passed &= regs[addr] != pointers[0]
        for j in range(4):
            if avoided >> j & 1:
                passed &= regs[addr] != j
    p, q, m, n = cat.original
    targets = (p >= 4) & (p < 12) & (q >= 4) & (q < 12) & (p+m == 15) & (q+n == 15)
    actual = int(np.count_nonzero(passed & targets & fresh))
    assert actual == claimed and actual >= threshold and not np.any(passed & ~cat.sat)
    return {'kind': 'relaxed-store' if store else 'native-path', 'mode': mode,
            'support': actual, 'report': raw}


def run(binary, job, timeout=None):
    return subprocess.run([str(binary), *map(str, job)], text=True, capture_output=True, check=False, timeout=timeout)


def parse_receipt(line, job):
    items = line.strip().split()
    if len(items) != 18 or items[:2] != ['CHECKED', job[0]]:
        raise ValueError(f'unrecognized receipt: {line[:250]}')
    vals = list(map(int, items[2:]))
    if vals[:6] != list(job[1:]):
        raise ValueError(f'wrong rectangle in receipt: {line[:250]}')
    return vals[6:8]


def make_plan(binary, width, part, parts):
    all_jobs = []
    bounds = {}
    for mode, accesses in MODES.items():
        for access in accesses:
            for direct in range(16):
                if direct.bit_count()+access.bit_count() != 4:
                    continue
                key = (direct, bool(access & 1))
                if key not in bounds:
                    blank = (mode, direct, access, 0, 0, 0, 0)
                    probe = run(binary, blank)
                    probe.check_returncode()
                    bounds[key] = parse_receipt(probe.stdout, blank)
                n, m = bounds[key]
                for chunk, lo in enumerate(range(0, n, width)):
                    if chunk % parts == part:
                        all_jobs.append([mode, direct, access, lo, min(n,lo+width), 0, m])
    return all_jobs


def area(job):
    return (job[4]-job[3])*(job[6]-job[5])


def verify_coverage(state, plan):
    # Project every rectangle onto each individual first-operation table.
    # The remaining intervals on the second axis must tile its full domain.
    expected = {}
    for mode, direct, access, lo, hi, left, right in plan:
        for first in range(lo, hi):
            expected[mode, direct, access, first] = (left, right)
    current = defaultdict(list)
    for job in [*state['todo'], *(r['job'] for r in state['records'])]:
        mode, direct, access, lo, hi, left, right = job
        assert lo < hi and left < right
        for first in range(lo, hi):
            current[mode, direct, access, first].append((left, right))
    assert current.keys() == expected.keys()
    for key, intervals in current.items():
        left, right = expected[key]
        for begin, end in sorted(intervals):
            assert begin == left
            left = end
        assert left == right
    assert state['total'] == sum(map(area, plan))
    assert state['visited'] == sum(area(r['job']) for r in state['records'])
    assert state['refuted'] == sum(area(r['job']) for r in state['records'] if r['kind'] == 'refuted')


def checkpoint(folder, state):
    save(folder/'state.json', state)
    modes = {}
    for mode in MODES:
        records = [r for r in state['records'] if r['job'][0] == mode]
        total = sum(area(j) for j in state['todo'] if j[0] == mode) + sum(area(r['job']) for r in records)
        modes[mode] = {'total': total, 'refuted':sum(area(r['job']) for r in records if r['kind']=='refuted')}
    save(folder/'progress.json', {**{k:state[k] for k in ('status','total','visited','refuted')},
                                  'modes':modes,'receipts':len(state['records']),
                                  'candidates':[r for r in state['records'] if r['kind']!='refuted']})


def campaign(args):
    binary=args.binary.resolve()
    folder=args.state
    folder.mkdir(parents=True,exist_ok=True)
    lock=(folder/'lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX|fcntl.LOCK_NB)
    spec={'binary':hash_file(binary), 'part':args.part, 'parts':args.parts, 'width':args.width, 'minimum':37}
    path=folder/'state.json'
    plan=make_plan(binary,args.width,args.part,args.parts)
    if path.exists():
        state=json.loads(path.read_text())
        if state['spec']!=spec:
            raise ValueError('saved binary or partition settings differ')
    else:
        state={'spec':spec,'status':'running','todo':plan.copy(),'records':[], 'total':sum(map(area,plan)),
               'visited':0,'refuted':0}
    verify_coverage(state,plan)
    if args.verify:
        for r in state['records']:
            if r['kind']=='refuted':
                parse_receipt(r['receipt'],r['job'])
            else:
                check_witness(r['receipt'])
        print(f'Verified {len(state["records"])} receipts and the exact remaining partition.')
        return
    checkpoint(folder,state)
    until=time.monotonic()+args.seconds
    while state['todo'] and state['status']=='running':
        remain=until-time.monotonic()
        if remain<=0:
            return
        j=state['todo'][0]
        try:
            r=run(binary,j,min(remain,args.timeout))
        except subprocess.TimeoutExpired:
            if remain<args.timeout:
                return
            k=3 if j[4]-j[3]>1 else 5
            if j[k+1]-j[k]<2:
                raise RuntimeError(f'a single fully pinned rectangle exceeded the timeout: {j}')
            mid=(j[k]+j[k+1])//2
            one,two=j.copy(),j.copy()
            one[k+1],two[k]=mid,mid
            state['todo'][:1]=[one,two]
            checkpoint(folder,state)
            continue
        if r.returncode==0:
            parse_receipt(r.stdout,j)
            kind='refuted'
            state['refuted']+=area(j)
        elif r.returncode==1:
            kind=check_witness(r.stdout)['kind']
        else:
            raise RuntimeError(f'native worker exited {r.returncode}: {r.stderr[:450]}')
        state['todo'].pop(0)
        state['records'].append({'job':j,'kind':kind,'receipt':r.stdout.strip()})
        state['visited']+=area(j)
        if not state['todo']:
            verify_coverage(state,plan)
            state['status']='exhausted' if state['visited']==state['refuted'] else 'candidates'
        checkpoint(folder,state)
        print(f'{j[0]} {kind}, {state["visited"]}/{state["total"]} rectangle area',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary',required=True,type=Path)
    p.add_argument('--state',required=True,type=Path)
    p.add_argument('--part',type=int,default=0)
    p.add_argument('--parts',type=int,default=1)
    p.add_argument('--width',type=int,default=8)
    p.add_argument('--seconds',type=int,default=3600)
    p.add_argument('--timeout',type=int,default=60)
    p.add_argument('--verify',action='store_true')
    a=p.parse_args()
    if not 0<=a.part<a.parts or min(a.width,a.seconds,a.timeout)<=0:
        p.error('invalid partition, width or budget')
    campaign(a)
