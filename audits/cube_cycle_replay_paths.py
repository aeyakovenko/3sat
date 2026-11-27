"""Cube-cycle catalog: replay the sound paths printed by cube_cycle_leaf_capacity with the independent
Python semantics of cube_cycle_native_model.py.

Each line  "sound d=D steps=S capacity=C : <path>"  is parsed, executed on all
65,536 inputs, and checked: the leaf set (inputs that satisfy all comparison
outcomes) contains exactly C inputs, all of them covers, and the path has S
instructions.  This confirms the capacities as LOWER bounds (the maximality is
the C++ enumeration).

usage: python3 cube_cycle_replay_paths.py LOG [LOG ...]
"""

import re
import sys

from cube_cycle_native_model import alu, branch, is_cover, words_of, ALU, BRANCH

INS = re.compile(r'^(?:r(\d+)=)?(LOAD|STORE|[a-z]+)[\[\(]([^\]\)]*)[\]\)](?:<-(\w+))?$')
CMP = re.compile(r'^(not )?(eq|lt|slt)\((\w+),(\w+)\)$')


def parse(text):
    data, cmps = [], []
    parts = [p.strip() for p in text.split(';')]
    for p in parts[:-1]:
        m = INS.match(p)
        assert m, p
        dst, name, args, src = m.groups()
        if name == 'LOAD':
            data.append(('load', args))
        elif name == 'STORE':
            data.append(('store', args, src))
        else:
            assert name in ALU, name
            a, b = args.split(',')
            data.append((name, a, b))
    for c in parts[-1].split(' & '):
        m = CMP.match(c.strip())
        assert m, c
        neg, rel, a, b = m.groups()
        cmps.append((rel, a, b, not neg))
    return data, cmps


def leaf_set(data, cmps):
    members = []
    for mask in range(65536):
        mem = words_of(mask) + [0] * 12
        reg = []

        def val(x):
            return reg[int(x[1:])] if x.startswith('r') else int(x)

        for ins in data:
            if ins[0] == 'load':
                reg.append(mem[val(ins[1])])
            elif ins[0] == 'store':
                mem[val(ins[1])] = val(ins[2])
            else:
                reg.append(alu(ins[0], val(ins[1]), val(ins[2])))
        if all(branch(rel, val(a), val(b)) == want for rel, a, b, want in cmps):
            members.append(mask)
    return members


def main():
    best = {}
    n = 0
    for path in sys.argv[1:]:
        for line in open(path):
            m = re.match(r'\s*sound d=(\d+) steps=(\d+) capacity=(\d+) : (.*)$', line)
            if not m:
                continue
            d, steps, cap, text = int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4)
            data, cmps = parse(text)
            assert len(cmps) == d and len(data) + d == steps, line
            members = leaf_set(data, cmps)
            assert len(members) == cap, (len(members), cap, line)
            assert all(is_cover(x) for x in members), line
            n += 1
            if cap > best.get((d, steps), (0, ''))[0]:
                best[d, steps] = (cap, text)
    print(f'{n} printed paths replayed: every leaf set is cover-only and has the printed size')
    for (d, steps), (cap, text) in sorted(best.items()):
        print(f'  comparisons={d} steps={steps} capacity={cap}: {text}')


if __name__ == '__main__':
    main()
