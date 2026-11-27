"""Verify finite native SAT clocks on 4488 and 5488, with complete four-bit opcodes."""

import argparse
import subprocess
import tempfile
from itertools import combinations
from pathlib import Path

import numpy as np

from clocked_native_path import ALU, Catalog, primitive, sensitive_base, verdict, words

BASE = 0x5488
HIGH = [int(s, 16) for s in ["5488", "f488", "4f88", "44f8", "448f", "dd77", "8eb6", "4448", "548c", "5c88", "5498", "5499", "74a8", "5455", "6c88", "5678", "7444", "d488", "6589", "545b", "56b8"]]
TWO = [21640, 62600, 20360, 17656, 17551, 56695, 36534, 255, 21644, 23688,
       21656, 21657, 59528, 22168, 22216, 38088, 25732, 54408, 22472,
       22456, 25796, 21251, 25693, 21897]


def raw_agreement_counts():
    # An agreement mask lists all negatives that follow the base's comparison.
    fields = list(zip(*(words(code) for code in HIGH)))
    args = [[j] * len(HIGH) for j in range(16)] + fields
    masks = {2**(len(HIGH)-1) - 1}
    for left, right in combinations(args, 2):
        for primitive_name in ('eq', 'lt', 'slt'):
            for a, b in ((left, right), (right, left)):
                flags = [primitive(primitive_name, x, y) for x, y in zip(a, b)]
                masks.add(sum(1 << j for j, flag in enumerate(flags[1:]) if flag == flags[0]))
    minimum = min((a & b & c).bit_count() for a in masks for b in masks for c in masks)
    assert minimum >= 1
    print(f'{len(masks)} raw comparison agreement masks; every triple retains at least {minimum} negative')


def seven_step_lookup():
    catalog = Catalog()
    a, b, m, n = catalog.original
    address = b & n
    selected = np.select([address == j for j in range(4)], [a, b, m, n], default=0)
    count = 0
    for p0 in range(2,16,2):
        for m0 in range(16):
            if p0 & m0:
                continue
            accepted = (m == m0) & (selected == p0)
            assert not np.any(accepted & ~catalog.sat)
            target = catalog.sat & (a == p0) & (m == m0)
            assert np.all(accepted[target])
            count += np.count_nonzero(target & (a > 0) & (m > 0) & (b > 0) & (n > 0))
    assert count == 1550
    assert sum(map(sensitive_base, range(65536))) == 2500
    yes = lambda x: ['i', x]
    reg = lambda x: ['r', x]
    path = [['L', None, yes(1)], ['L', None, yes(2)], ['L', None, yes(3)],
            ['A', 'and', reg(0), reg(2)], ['L', None, reg(3)],
            ['B', 'eq', reg(1), yes(8)], ['B', 'eq', reg(4), yes(4)]]
    assert not len(catalog.survivors(path, 0x4488))
    print('Seven-step paths cover 1,550 of 2,500 sensitive positive bases; 4488 has a verified path')


def run(compiler):
    assert HIGH[0] == TWO[0] == BASE and sensitive_base(BASE)
    assert all(not verdict(words(code)) for code in set(HIGH[1:] + TWO[1:]))
    assert min(min(words(code)) for code in HIGH) >= 4
    raw_agreement_counts()
    seven_step_lookup()
    with tempfile.TemporaryDirectory() as temp:
        folder = Path(temp)
        binary = folder/'census'
        subprocess.run([compiler, '-O3', '-std=c++20', str(Path(__file__).with_name('seven_step_two_alu_census.cpp')),
                        '-o', str(binary)], check=True)
        truth = subprocess.check_output([binary, '--primitive-tables'], text=True)
        answers = [int(value) for value in truth.split()]
        expected = [primitive(op, a, b) for op in ALU for a in range(16) for b in range(16)]
        assert answers == expected
        for gates, suite in ((1, HIGH), (2, TWO)):
            listing = folder/'suite'
            listing.write_text(''.join(f'{code:04x}\n' for code in suite))
            result = subprocess.check_output([binary, str(gates), listing], text=True).strip()
            assert result.startswith(f'EXHAUSTED {gates} '), result
            print(f'{len(suite)} input files: {result}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler', default='c++')
    run(parser.parse_args().compiler)
