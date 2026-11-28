"""Two physical edits with disjoint signed pin sets and easy density (11/7)(4/7)^4."""

from itertools import combinations, product

from one_bit_clause_density_threshold import count_after, encode, parse
from two_edits_at_the_density_threshold import build as threshold_square
from two_edits_at_the_density_threshold import complete_sat, padded


# Negative entries complement a coordinate of the existing two-edit wrapper.
RENAMING = {1: 2, 2: 4, 3: -3, 4: 5, 5: 6, 7: 7}
B, T, A0, F0, A1, F1 = 2, 4, -3, 5, 6, 7
CONTROLS = (B, T, abs(A0), F0, A1, F1)
PETAL = (1, 14, 17)
Y = PETAL[0]


def rename(literal):
    name = RENAMING.get(abs(literal), abs(literal))
    return name if literal > 0 else -name


def build(source):
    base, occurrences, guard_groups, private, reps, source = threshold_square(source, False)
    added = [PETAL, (B, T, Y)]
    # There is just one hard extension on the three new names.
    for literal in (-Y, PETAL[1], -PETAL[2]):
        added.extend(padded(-B, literal, T))
    files = []
    for mask in range(4):
        rows = [tuple(map(rename, row)) for row in parse(base[mask])]
        if mask & 1:
            assert rows[-2] == (T, B, F0)
            rows[-2] = (T, -Y, F0)
        files.append(encode(rows[:-2] + added + rows[-2:]))
    guards = {tuple(map(rename, core)): [tuple(map(rename, row)) for row in copies]
              for core, copies in guard_groups.items()}
    return files, occurrences, guards, private, reps, source


def loss_pins(old, new):
    """True signed literals forced when an old clause holds and its edit fails."""
    replaced, = set(old) - set(new)
    assert len(set(old) & set(new)) == 2
    pins = {replaced, *(-literal for literal in new)}
    assert len({abs(literal) for literal in pins}) == 4
    return pins


def check_transversal(rows, occurrences, guard_groups, private):
    # The guards require at least four names even with private fillers allowed.
    # The new petal and all occurrence triples are disjoint from the guards
    # and from each other. Each therefore pays for one additional name.
    present = set(rows)
    guard_names = set(CONTROLS) | set(private)
    disjoint = [PETAL, *occurrences]
    assert set(disjoint) <= present
    assert all(guard_names.isdisjoint(row) for row in disjoint)
    assert len(set().union(*disjoint)) == 3*len(disjoint)
    for core, copies in guard_groups.items():
        assert len(copies) == 4 and set(copies) <= present
        assert all(row[:len(core)] == core for row in copies)
        fillers = [set(row[len(core):]) for row in copies]
        assert set().union(*fillers) <= set(private)
        assert all(x.isdisjoint(y) for x, y in combinations(fillers, 2))
    assert set(private).isdisjoint(CONTROLS)
    for size in range(4):
        for taken in combinations(CONTROLS, size):
            assert any(set(taken).isdisjoint(map(abs, core)) for core in guard_groups)
    # This hits all printed supports and meets the lower certificate exactly.
    cover = {B, T, abs(A0), F0, Y} | {row[0] for row in occurrences}
    assert len(cover) == 5 + len(occurrences)
    assert all(not cover.isdisjoint(map(abs, row)) for row in rows)


def check(source):
    files, occurrences, guard_groups, private, reps, src = build(source)
    cnfs = [parse(blob) for blob in files]
    names = {abs(literal) for row in cnfs[0] for literal in row}
    assert len(names) == 9 + len(private) + 3*len(occurrences) + len(reps)
    assert all({abs(literal) for row in rows for literal in row} == names for rows in cnfs)
    assert len({blob.splitlines()[0] for blob in files}) == 1
    for i, j in combinations(range(4), 2):
        assert len(files[i]) == len(files[j])
        assert sum((a^b).bit_count() for a,b in zip(files[i], files[j])) == (i^j).bit_count()
    edits = [[(chr(a), chr(b)) for a,b in zip(files[0], files[1<<j]) if a != b]
             for j in range(2)]
    assert edits == [[('3', '1')], [('6', '2')]]
    first = loss_pins(cnfs[0][-2], cnfs[1][-2])
    second = loss_pins(cnfs[0][-1], cnfs[2][-1])
    assert first == {-T, Y, A0, -F0} and second == {T, -B, A1, -F1}
    assert first.isdisjoint(second)
    check_transversal(cnfs[0], occurrences, guard_groups, private)

    # For fixed controls and source representatives, count_after counts the
    # actual simplified printed clauses by independent connected components.
    # Compare that count on every fiber with the two dormant boxes and the
    # parsimonious hard branch. Never enumerate assignments to all fillers.
    masses = [0]*4
    source_count = 0
    free_choices = 7**len(occurrences) * 2**len(private)
    for values in product((False, True), repeat=len(reps)):
        source_bits = dict(zip(reps, values))
        satisfies = all(any(source_bits[abs(l)] == (l>0) for l in row) for row in src)
        source_count += satisfies
        fixed_source = {reps[k]: v for k,v in source_bits.items()}
        for bits in product((False, True), repeat=len(CONTROLS)+1):
            fixed = {**fixed_source, **dict(zip((*CONTROLS, Y), bits))}
            b, t, neg_a0, f0, a1, f1, y = bits
            left = not b and not t and not neg_a0 and not f0 and y
            right = not b and t and a1 and not f1
            hard = b and not t and neg_a0 and not f0 and not a1 and not f1 and not y
            for mask, rows in enumerate(cnfs):
                count = count_after(rows, names, fixed)
                dormant = (4*int(left and not mask & 1) +
                           (4 if y else 3)*int(right and not mask & 2))
                live = hard and bool(mask & 1) and satisfies
                assert count == dormant*free_choices + int(live)
                masses[mask] += count
    m = len(occurrences)
    assert masses[0] * 128*8**m == (1<<len(names)) * 11*7**m
    assert masses[0] * 8**(m+5) * 7**5 == (1<<len(names)) * 7**(m+5) * 11*4**4
    assert masses[3] == source_count
    assert [complete_sat(rows) for rows in cnfs] == [True, True, True, bool(source_count)]
    return source_count


if __name__ == '__main__':
    signs = [tuple(i*s for i,s in enumerate(bits,1)) for bits in product((-1,1),repeat=3)]
    counts = [check(source) for source in ([], signs[:7], signs)]
    assert counts == [1, 1, 0]
    print('3 ordinary DIMACS squares: both individual edits SAT on each; '
          'joint model counts 1, 1, 0.')
    print('Disjoint signed pin sets, (11/7)(4/7)^4 normalized density, '
          'transversal m+5, and all physical distances verified.')
