"""Whitespace padding of the Andreev projection to arbitrary byte lengths, for
depth-two-threshold-circuit-bounds-for-3-sat.md.

Padding = spaces inserted inside the last clause line (before its final newline), so the
journal's checker (splitlines, line-count equality, 4-token unpack) still accepts the file.
Checks properness (journal assertions) and CaDiCaL verdict == KW Andreev for padded files.
Usage: python3 andreev_projection_padding_check.py
"""
import os
import sys
from itertools import product
from random import Random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import andreev_projection_copy_audit as A  # noqa: E402


def pad(file, spaces):
    assert file.endswith(b' 0\n')
    return file[:-1] + b' ' * spaces + b'\n'


def main():
    rng = Random(7)
    count = 0
    for s in product(range(2), repeat=8):
        for spaces in (1, 7):
            f = pad(A.encode(2, 2, 2, list(s)), spaces)
            x, a = A.journal_to_kw(list(s), 2, 2)
            assert A.sat_cadical(f) == bool(A.kw_andreev(x, a))
            count += 1
    for _ in range(10):
        s = [rng.randrange(2) for _ in range(512)]
        base = A.encode(8, 32, 1, s)
        for spaces in (1, 1000, 300000):          # 300000 spaces ~ 7x the canonical length
            f = pad(base, spaces)
            assert len(f) == len(base) + spaces
            x, a = A.journal_to_kw(s, 8, 32)
            assert A.sat_cadical(f) == bool(A.kw_andreev(x, a))
            count += 1
    print(f'padded files: {count} checked (proper per journal assertions; CaDiCaL == KW Andreev)')


if __name__ == '__main__':
    main()
