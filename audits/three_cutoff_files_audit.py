"""Generate a three-file Hamming path whose middle SAT verdict encodes a supplied 3-CNF."""

import argparse
from collections import Counter
from functools import partial
from itertools import combinations
from pathlib import Path

from almost_mixed_cutoff_audit import checked_solve, make_formula, signed_catalog, source_has_model
from one_byte_dense_successor_audit import clause, encode, parse
from selector_parity_cube_audit import physical_template


# Coordinates are in physical switch order. The first two switches do not constrain the source.
CORNERS = (('B', (1, 1, 0, 0)), ('M', (0, 1, 1, 0)), ('C', (0, 0, 1, 1)))


def guarded_cutoffs(high, low, source, _unused, arity):
    assert arity == 4 and max(abs(x) for row in source for x in row) == high
    switches = list(range(high + 1, high + arity + 1))
    rows = list(source)
    for index, cutoff_var in ((2, high), (3, low)):
        # switch -> not cutoff_var; both signs of a private third variable give proper clauses.
        pad = high + arity + index + 1
        rows.extend([(-switches[index], -cutoff_var, pad), (-switches[index], -cutoff_var, -pad)])
    return rows, switches


def write_checked(path, raw):
    if path.exists():
        if path.read_bytes() != raw:
            raise FileExistsError(f'different bytes already exist at {path}')
    else:
        with path.open('xb') as dest:
            dest.write(raw)


def generate(tag, source, outdir):
    encoded, high, low = make_formula(source)
    underlying = parse(encoded)
    truth = source_has_model(source)
    fixed, switches, names = physical_template(
        underlying, [], 4, h=3, semantic_builder=partial(guarded_cutoffs, high, low))
    files = []
    histogram = None
    counts = []
    for key, mask in CORNERS:
        selectors = {clause(p, q, b if active else a)
                     for active, (p, q, a, b) in zip(mask, switches)}
        raw = encode(fixed | selectors)
        rows = parse(raw)
        degree = Counter(abs(x) for row in rows for x in row)
        assert len(degree) == names and max(degree.values()) <= 4
        expected = {'B': True, 'M': truth, 'C': False}[key]
        assert checked_solve(rows, []) == expected
        if histogram is None:
            histogram = Counter(raw)
        assert Counter(raw) == histogram
        if outdir is not None:
            write_checked(outdir / f'{tag}-{key}.cnf', raw)
        files.append(raw)
        counts.append(len(rows))
    assert len(set(map(len, files))) == 1 and len(set(counts)) == 1
    distances = [sum((a ^ b).bit_count() for a, b in zip(left, right))
                 for left, right in combinations(files, 2)]
    assert distances == [2, 4, 2]  # B-M, B-C, M-C.
    changing = [i for i, (a, b) in enumerate(zip(files[0], files[2])) if a != b]
    assert len(changing) == 4 and all({files[0][i], files[2][i]} == {50, 51} for i in changing)
    assert all(files[j][i] == 50 + mask[coordinate] for j, (_, mask) in enumerate(CORNERS)
               for coordinate, i in enumerate(changing))
    print(f'{tag}: {len(files[0])} bytes each, {names} names, {counts[0]} clauses, '
          f'B/M/C = YES/{"YES" if truth else "NO"}/NO; edit offsets {changing}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-dir', type=Path, help='save the B, M and C files for each source')
    args = parser.parse_args()
    if args.write_dir is not None:
        args.write_dir.mkdir(parents=True, exist_ok=True)
    catalog = signed_catalog()
    for label, instance in [('single', catalog[:1]), ('seven', catalog[:-1]), ('eight', catalog)]:
        generate(label, instance, args.write_dir)
