"""Resume exact two-ALU/four-load support checks across word-RAM addressing layouts."""

import argparse
import fcntl
import json
import re
import subprocess
import time
from pathlib import Path

import numpy as np

from clocked_native_path import ALU, Catalog, primitive
from clocked_native_path_campaign import hash_file, save

RECEIPT = re.compile(r'EXHAUSTED direct (\d+) access (\d+) first range (\d+)\.\.(\d+) of (\d+),')
PATH = re.compile(
    r'FULL PATH direct=(\d+) access=(\d+) ALUs ([\d,]+) ([\d,]+) '
    r'\[([\d,]+)\] \[([\d,]+)\] support (\d+)'
)


def verify_path(report, minimum):
    match = PATH.fullmatch(report.strip())
    if not match:
        raise ValueError('unrecognized native path')
    direct, access = map(int, match.group(1, 2))
    catalog = Catalog()
    codes = np.arange(65536)
    registers = {**{i: i for i in range(16)},
                 **{16 + j: catalog.original[j] for j in range(4) if direct >> j & 1}}
    fresh = np.ones(65536, dtype=bool)
    previous = []
    for i, group in enumerate(match.group(3, 4)):
        op, a, b = map(int, group.split(','))
        key = 20 + 2 * i
        value = np.broadcast_to(primitive(ALU[op], registers[a], registers[b]), codes.shape)
        registers[key] = value
        if access >> i & 1:
            fresh &= value < 4
            for j in range(4):
                if direct >> j & 1:
                    fresh &= value != j
            for old in previous:
                fresh &= value != old
            previous.append(value)
            registers[key + 1] = np.select([value == j for j in range(4)],
                                           catalog.original, default=0)
    accepted = np.ones(65536, dtype=bool)
    for group in match.group(5, 6):
        a, b, kind, inverse = map(int, group.split(','))
        if kind in (2, 4):
            a, b = b, a
        name = ('eq', 'lt', 'lt', 'slt', 'slt')[kind]
        outcome = np.asarray(primitive(name, registers[a], registers[b]), dtype=bool)
        accepted &= outcome ^ bool(inverse)
    assert not np.any(accepted & ~catalog.sat)
    p, q, m, n = catalog.original
    targets = (p >= 4) & (p < 12) & (q >= 4) & (q < 12) & (p + m == 15) & (q + n == 15)
    actual = int(np.count_nonzero(targets & accepted & fresh))
    assert actual == int(match[7]) and actual >= minimum
    return {'direct': direct, 'access': access, 'support': actual, 'path': report.strip()}


def receipt(output, direct, access, lo, hi):
    match = RECEIPT.match(output.strip())
    if not match or tuple(map(int, match.groups()[:4])) != (direct, access, lo, hi):
        raise RuntimeError(f'invalid native result: {output[:300]}')
    return int(match[5])


def run(binary, args, timeout=None):
    return subprocess.run([str(binary), *map(str, args)], capture_output=True,
                          check=False, text=True, timeout=timeout)


def smoke(binary):
    control = run(binary, (14, 1, 843, 844, 8))
    assert control.returncode == 1
    assert verify_path(control.stdout, 8)['support'] == 8
    empty = run(binary, (14, 1, 843, 844, 19))
    assert empty.returncode == 0
    assert receipt(empty.stdout, 14, 1, 843, 844) == 952
    print('Complete catalog replay of the eight-target positive control passed.')
    print(empty.stdout.strip())


def campaign(binary, folder, seconds, width, per_shard):
    folder.mkdir(parents=True, exist_ok=True)
    lock = (folder/'lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    spec = {'binary': hash_file(binary), 'minimum': 19, 'width': width}
    state_path = folder/'state.json'
    start = time.monotonic()
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if state['spec'] != spec:
            raise ValueError('binary fingerprint, threshold or width differ from the saved search')
    else:
        groups = []
        for access in (1, 2, 3):
            for direct in range(16):
                if direct.bit_count() + access.bit_count() != 4:
                    continue
                result = run(binary, (direct, access, 0, 0))
                result.check_returncode()
                count = receipt(result.stdout, direct, access, 0, 0)
                groups.append([(direct, access, lo, min(lo + width, count))
                               for lo in range(0, count, width)])
        # Round-robin across layouts so every prefix appears early.
        pending = [group[i] for i in range(max(map(len, groups))) for group in groups if i < len(group)]
        state = {'spec': spec, 'total': sum(hi-lo for _, _, lo, hi in pending),
                 'done': 0, 'pending': pending, 'receipts': [], 'status': 'running'}
        save(state_path, state)
    while state['pending'] and state['status'] == 'running':
        remaining = seconds - (time.monotonic() - start)
        if remaining <= 0:
            break
        direct, access, lo, hi = state['pending'][0]
        try:
            result = run(binary, (direct, access, lo, hi), min(per_shard, remaining))
        except subprocess.TimeoutExpired:
            if remaining < per_shard:
                break
            if hi - lo < 2:
                raise RuntimeError(f'one first table timed out; resume with a larger --shard-timeout: {lo}')
            mid = (lo + hi) // 2
            state['pending'][:1] = [[direct, access, lo, mid], [direct, access, mid, hi]]
            save(state_path, state)
            continue
        if result.returncode == 1:
            state['path'] = verify_path(result.stdout, 19)
            state['status'] = 'path'
        elif result.returncode == 0:
            receipt(result.stdout, direct, access, lo, hi)
            state['pending'].pop(0)
            state['done'] += hi - lo
            state['receipts'].append(result.stdout.strip())
            if not state['pending']:
                assert state['done'] == state['total']
                state['status'] = 'exhausted'
        else:
            raise RuntimeError(f'native census exit {result.returncode}: {result.stderr[:500]}')
        save(state_path, state)
        print(f'{state["status"]} {state["done"]}/{state["total"]} first tables', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--state', type=Path)
    parser.add_argument('--seconds', type=int, default=3600)
    parser.add_argument('--shard-width', type=int, default=16)
    parser.add_argument('--shard-timeout', type=int, default=120)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        smoke(args.binary.resolve())
    else:
        if not args.state or min(args.seconds, args.shard_width, args.shard_timeout) <= 0:
            parser.error('supply state and positive time/width bounds')
        campaign(args.binary.resolve(), args.state, args.seconds, args.shard_width, args.shard_timeout)
