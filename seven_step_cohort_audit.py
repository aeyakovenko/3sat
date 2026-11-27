"""Replay the seven-step cohort theorem, the eight-step timing bound and its controls."""
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE
sys.path.insert(0, str(ROOT))
from clocked_native_path import ALU, primitive
from nine_step_native_referee_audit import scalar


def packed(values):
    return int.from_bytes(np.packbits(values, bitorder='little').tobytes(), 'little')


def tests(a, b):
    return a == b, a < b, b < a, (a ^ 8) < (b ^ 8), (b ^ 8) < (a ^ 8)


def truth_tables():
    codes = np.arange(65536, dtype=np.int32)
    p, q, m, n = words = [codes >> s & 15 for s in (12, 8, 4, 0)]
    sat = np.zeros(65536, dtype=bool)
    pos, neg = p | (q << 4), m | (n << 4)
    for assignment in range(1, 256):
        sat |= ((pos & assignment) == pos) & ((neg & assignment) == 0)
    assert np.array_equal(sat, ((p & m) == 0) & ((q & n) == 0) & ((m & n) != 15))
    selected = codes[(p >= 4) & (p <= 11) & (q >= 4) & (q <= 11) &
                     (p + m == 15) & (q + n == 15)]
    assert sat.sum() == 6560 and len(selected) == 64 and sat[selected].all()
    return codes, words, sat, selected


def high_word_checks(codes, words, sat, selected):
    high = np.logical_and.reduce([(col >= 4) & (col <= 11) for col in words])
    files = np.concatenate([selected, codes[high & ~sat]])
    assert len(files) == 64 + 3772
    raw = [np.full(len(files), i, dtype=np.uint8) for i in range(16)]
    raw += [col[files].astype(np.uint8) for col in words]
    targets = (1 << 64) - 1
    universe = (1 << len(files)) - 1

    def outcomes(a, b):
        for test in tests(a, b):
            value = packed(test)
            yield value
            yield value ^ universe

    guards = {g for i, a in enumerate(raw) for b in raw[i:]
              for g in outcomes(a, b) if g & targets}
    doubles = {a & b for a in guards for b in guards if a & b & targets}
    for ab in doubles:
        for c in guards:
            z = ab & c
            assert not (z & targets) or (z >> 64)
    print(f'{len(guards)} raw outcome tables, {len(doubles)} target-hitting '
          'two-guard intersections, no sound raw triple.')

    lut = np.array([[[scalar(k, a, b) for b in range(16)] for a in range(16)]
                    for k in range(20)], dtype=np.uint8)
    seen = set()
    for k in range(20):
        for a in raw:
            for b in raw:
                result = lut[k, a, b]
                key = result.tobytes()
                if key in seen:
                    continue
                seen.add(key)
                low = [packed(result == v) for v in range(4)]
                high_result = universe ^ (low[0] | low[1] | low[2] | low[3])
                last = guards | {g for y in raw for g in outcomes(result, y) if g & targets}
                for guard in last:
                    # Allow a fresh indirect read at the single omitted address.
                    for layer in low:
                        z = layer & guard
                        assert not (z & targets) or (z >> 64)
                    # If the store was addressed by result, every passing negative
                    # must collide with a later direct load. Exclude as few
                    # low addresses as possible so as to retain all possible targets.
                    if (guard & high_result) >> 64:
                        continue
                    allowed = universe
                    for layer in low:
                        if (guard & layer) >> 64:
                            allowed &= ~layer
                    assert not (allowed & targets & guard)
    assert len(seen) == 954
    print('All 954 high-suite ALU tables exclude a one-guard, one-store path.')


def build(source, output):
    subprocess.run([os.environ.get('CXX', 'c++'), '-std=c++20', '-O3',
                    '-I', str(ROOT), str(source), '-o', str(output)], check=True)


def single_guard(folder):
    # Same read-only superset as the journal. Request even ONE target, using
    # the original pruning logic and fixed suite. Only its threshold changes.
    source = (ROOT / 'two_arithmetic_results_with_unlimited_native_reads.cpp').read_text()
    assert source.count('threshold = 37') == 1
    adapted = folder / 'single.cpp'
    adapted.write_text(source.replace('threshold = 37', 'threshold = 1'))
    exe = folder / 'single'
    build(adapted, exe)
    line = subprocess.check_output([exe], text=True).strip()
    assert 'of 1182 tables' in line and '22064 negatives' in line
    print('Read-only one-guard search at support one:', line)


def seed_negatives(codes, words, sat, seed):
    p, q, m, n = words
    # Keep all conflicts replacing one pair of a target, plus the exceptional
    # negative and a reproducible sample. Refinement supplies missing examples.
    pair1 = (p >= 4) & (p <= 11) & (p + m == 15)
    pair2 = (q >= 4) & (q <= 11) & (q + n == 15)
    neg = set(map(int, codes[(pair1 | pair2) & ~sat])) | {255}
    rng = random.Random(seed)
    neg.update(rng.sample(list(map(int, codes[~sat])), 512))
    files = sorted(neg)
    rng.shuffle(files)
    assert not any(sat[files])
    return files


def identify_address_operation(reg, sample):
    raw = [r for r in range(20) if r != 16]  # P is the missing direct column.
    values = {r: reg[r][sample] for r in raw}
    wanted = values[17] & values[19]
    matches = {(op, a, b) for op in ALU for a in raw for b in raw
               if np.array_equal(primitive(op, values[a], values[b]), wanted)}
    assert matches == {('and', 17, 19), ('and', 19, 17)}


def pair_census(exe, codes, words, sat, selected, seed):
    neg = seed_negatives(codes, words, sat, seed)
    reg = [np.full(len(codes), i, dtype=np.int32) for i in range(16)] + words
    rows = {255 << (8*i) for i in range(0, 8, 2)}
    for iteration in range(1, 65537):
        listing = subprocess.check_output([exe], input='\n'.join(map(str, neg)), text=True)
        sample = np.concatenate([selected, neg])
        first = set()
        path_sets = set()
        counterexamples = set()
        tables = []
        operations = set()
        paths = 0
        for line in listing.splitlines():
            tag, *args = line.split()
            if tag == 'tables':
                tables.append(tuple(map(int, args)))
                continue
            assert tag == 'path'
            omit, op, a, b, *tail = map(int, args)
            val = primitive(ALU[op], reg[a], reg[b])
            load = np.choose(np.minimum(val, 4), [*words, reg[0]])
            live = reg + [val, load]
            guards = []
            for i in (0, 4):
                x, y, t, flip = tail[i:i+4]
                guards.append(tests(live[x], live[y])[t] ^ bool(flip))
            passed = guards[0] & guards[1]
            fresh = (val == omit) if omit >= 0 else True
            support = int(tail[8])
            assert packed((passed & fresh)[selected]) == support
            assert not passed[neg].any()
            paths += 1
            opposites = np.flatnonzero(passed & ~sat)
            if len(opposites):
                counterexamples.add(int(opposites[0]))
            path_sets.add(support)
            operations.add((omit, op, a, b))
            # Index FIRST outcomes on the actual unfiltered sample, the same
            # domain used for operand and comparison deduplication in C++.
            for guard in guards:
                key = packed(guard[sample])
                first.add(key)
        assert [i for i, _ in tables] == [-1, 0, 1, 2, 3]
        print(f'Two-guard seed {seed}, pass {iteration}: {len(neg)} negatives, {sum(n for _,n in tables)} '
              f'first tables, {paths} surviving guard pairs, {len(counterexamples)} new negatives.')
        if counterexamples:
            assert counterexamples.isdisjoint(neg)
            neg.extend(sorted(counterexamples))
            continue
        assert path_sets == rows
        assert operations == {(0, ALU.index('and'), 17, 19)}
        identify_address_operation(reg, sample)
        all_lanes = (1 << len(sample)) - 1
        assert all((mask ^ all_lanes) not in first for mask in first)
        print(f'{len(first)} distinct first-outcome signatures, zero complementary pairs. '
              f'Final layout counts {tables}.')
        return
    raise AssertionError('negative refinement did not terminate')


def upper_paths(words, sat, selected):
    p, q, m, n = words
    j = q & n
    x = np.choose(np.minimum(j, 4), [p, q, m, n, np.zeros_like(p)])
    for fixed in (4, 6, 8, 10):
        ok = (m == 15-fixed) & (x == fixed)
        assert not (ok & ~sat).any() and ok.sum() == 81
        assert np.array_equal(ok[selected], p[selected] == fixed)
    assert x[0x05A1] == 5 and m[0x05A1] == 10 and not sat[0x05A1]
    r = (m << (m % 4)) & 15
    ok = (m < r) & (x == r)
    assert not (ok & ~sat).any() and ok.sum() == 486 and ok[selected].sum() == 16
    print('Four seven-step row paths and the 486-file, eight-step path pass full assignment replay.')


def serialized_lengths(words, selected):
    p, q, m, n = words
    lengths = set()
    for i in selected:
        positive = int(p[i] | (q[i] << 4))
        negative = int(m[i] | (n[i] << 4))
        assert positive ^ negative == 255 and not (positive & negative)
        lines = ['p cnf 8 9', '1 2 3 4 5 6 7 8 0']
        for bit in range(8):
            name = bit + 1
            lit = -name if negative & (1 << bit) else name
            lines.append(f'{lit} 0')
        size = 8 * len(('\n'.join(lines) + '\n').encode('ascii'))
        assert size == 8 * (60 + negative.bit_count())
        lengths.add(size)
    assert lengths == set(range(496, 529, 8))
    print('All 64 ordinary CNF serializations match 8(60 + number of negative units) bits.')


def mixed_bound():
    # d counts only noncomparison instructions. Use an always-true comparison
    # to pad an accepting prefix to the original eight-step census horizon.
    cap = (0, 0, 0, 0, 1, 8, 18, 36)
    bound = {(d, 8-d): 0 for d in range(9)}
    for elapsed in range(7, -1, -1):
        for d in range(elapsed + 1):
            c = elapsed-d
            mixed_child = bound[d,c+1]
            bound[d,c] = max(bound[d+1,c], 2*mixed_child, cap[d]+mixed_child)
    assert [bound[0,c] for c in range(5)] == [36, 18, 8, 1, 0]
    print('Eight-step mixed-prefix table, rows c=0..4:',
          [[bound[d,c] for d in range(9-c)] for c in range(5)])
    # A seven-step row has two comparisons and five data instructions.
    # Its first sibling and its last sibling must each contain a negative
    # whenever reachable with targets, by the six-step exclusion.
    off_first = max(bound[d,1] for d in range(6))
    off_last = bound[5,2]
    fast_with_row = 8 + off_first + off_last
    saved = max(bound[0,0], fast_with_row + 8)
    assert (fast_with_row, 9*64 - saved) == (34, 534)
    print('With a seven-step row, at most 34 targets finish by eight. '
          'Across the 64 targets the clock sum is at least 534.')


def packed_product(sat):
    rng = random.Random(71832)
    count = 0
    positives = np.flatnonzero(sat).tolist()
    for lanes in (1, 2, 3, 4, 8, 17):
        unit = sum(1 << (16*j) for j in range(lanes))
        low = unit * 255
        for _ in range(500):
            blocks = [rng.randrange(65536) for _ in range(lanes)]
            for source in (blocks, rng.choices(positives, k=lanes)):
                word = sum(x << (16*j) for j,x in enumerate(source))
                neg = word & low
                clashes = neg & (word >> 8)
                forced = (neg + unit) & (unit << 8)
                assert bool(clashes or forced) == (not all(sat[source]))
                count += 1
    print(f'{count} packed conjunctions passed the scan cross-check.')


def main():
    codes, words, sat, selected = truth_tables()
    upper_paths(words, sat, selected)
    serialized_lengths(words, selected)
    high_word_checks(codes, words, sat, selected)
    with tempfile.TemporaryDirectory() as temp:
        folder = Path(temp)
        single_guard(folder)
        exe = folder / 'pair'
        build(HERE / 'seven_step_cohort_guard_pairs.cpp', exe)
        for seed in (27504, 50427):
            pair_census(exe, codes, words, sat, selected, seed)
    mixed_bound()
    packed_product(sat)


if __name__ == '__main__':
    main()
