"""Build and verify the proper DIMACS pair attaining the normalized density threshold."""
from itertools import product


A, B, PAD, OTHER_PAD = 3, 1, 5, 7
PRIVATE = tuple(range(80, 88))


def encode(cnf):
    maximum = max((abs(lit) for row in cnf for lit in row), default=0)
    text = [f'p cnf {maximum} {len(cnf)}']
    text.extend(' '.join(map(str, row)) + ' 0' for row in cnf)
    return ('\n'.join(text) + '\n').encode('ascii')


def parse(file):
    lines = file.splitlines()
    p, typ, var_bound, clause_count = lines[0].split()
    assert (p, typ) == (b'p', b'cnf') and len(lines) == int(clause_count) + 1
    cnf = []
    for row in lines[1:]:
        fields = tuple(map(int, row.split()))
        assert len(fields) == 4 and fields[-1] == 0
        triple = fields[:-1]
        assert all(0 < abs(lit) <= int(var_bound) for lit in triple)
        assert len(set(map(abs, triple))) == 3
        cnf.append(triple)
    return cnf


def files(source_file):
    source = sorted({tuple(sorted(row)) for row in parse(source_file)})
    reps = {abs(lit): int('6' + str(abs(lit))) for row in source for lit in row}
    common, independent, cover = [], [], {A, B, PAD, OTHER_PAD}
    for j, row in enumerate(source):
        occurrence = tuple(int('9' + str(3 * j + i)) for i in range(3))
        common.append(occurrence)
        independent.append(occurrence)
        cover.add(occurrence[0])
        for y, lit in zip(occurrence, row):
            source_lit = reps[abs(lit)] if lit > 0 else -reps[abs(lit)]
            common.extend(((-B, -y, source_lit), (-B, y, -source_lit)))
    for pad in (PAD, OTHER_PAD):
        common.extend((-pad, a, b) for a, b in product((A, -A), (B, -B)))
    common.extend(((A, B, PAD), (-A, -B, PAD)))
    for j, control in enumerate((A, -B, -PAD, -OTHER_PAD)):
        triple = (control, PRIVATE[2*j], PRIVATE[2*j+1])
        independent.append(triple)
        common.append(triple)
    common.extend((-B, u, PAD) for u in PRIVATE)
    easy = encode([*common, (A, PAD, OTHER_PAD)])
    edited = encode([*common, (B, PAD, OTHER_PAD)])
    return easy, edited, reps, independent, cover


def residual(cnf, fixed):
    out = []
    for row in cnf:
        surviving = []
        for lit in row:
            v = abs(lit)
            if v not in fixed:
                surviving.append(lit)
            elif fixed[v] == (lit > 0):
                break
        else:
            out.append(tuple(surviving))
    return out


def count_after(cnf, names, fixed):
    """Count a cofactor by unit propagation and independent final clauses."""
    live = residual(cnf, fixed)
    remaining = len(names) - len(fixed)
    while True:
        if () in live:
            return 0
        units = {row[0] for row in live if len(row) == 1}
        if not units:
            break
        if any(-u in units for u in units):
            return 0
        live = residual(live, {abs(u): u > 0 for u in units})
        remaining -= len(units)
    used = [abs(lit) for row in live for lit in row]
    assert len(set(used)) == len(used)
    count = 1 << (remaining - len(used))
    for row in live:
        count *= (1 << len(row)) - 1
    return count


def check(source):
    src_file = encode(source)
    easy, edited, reps, independent, cover = files(src_file)
    assert len(easy) == len(edited) and easy.splitlines()[0] == edited.splitlines()[0]
    assert sum((x ^ y).bit_count() for x, y in zip(easy, edited)) == 1
    assert [(x, y) for x, y in zip(easy, edited) if x != y] == [(ord('3'), ord('1'))]
    src = parse(src_file)
    eform, fform = parse(easy), parse(edited)
    nsrc = len(reps)
    m = len(set(tuple(sorted(row)) for row in src))
    names = {abs(lit) for row in eform for lit in row}
    assert len(names) == 12 + nsrc + 3*m
    assert set(independent) <= set(eform) and set(independent) <= set(fform)
    witness = [abs(lit) for triple in independent for lit in triple]
    assert len(set(witness)) == len(witness)
    assert len(independent) == len(cover) == m + 4
    for row in [*eform, *fform]:
        assert not cover.isdisjoint(map(abs, row))
    models_e = models_f = models_s = 0
    for bits in product((False, True), repeat=nsrc):
        z = dict(zip(reps, bits))
        source_model = all(any(z[abs(lit)] == (lit > 0) for lit in row) for row in src)
        z_reps = {reps[i]: z[i] for i in z}
        easy_count = hard_count = 0
        for controls in product((False, True), repeat=4):
            fixed = dict(zip((A, B, PAD, OTHER_PAD), controls))
            fixed.update(z_reps)
            easy_count += count_after(eform, names, fixed)
            hard_count += count_after(fform, names, fixed)
        assert hard_count == int(source_model)
        assert easy_count == (1 << len(PRIVATE)) * (7 ** m)
        models_e += easy_count
        models_f += hard_count
        models_s += int(source_model)
    tau = len(cover)
    assert models_f == models_s
    assert models_e * 8**tau * 7**4 == (1 << len(names)) * 7**tau * 4**4
    return bool(models_f)


if __name__ == '__main__':
    clauses = [tuple(i*s for i, s in enumerate(signs, 1))
               for signs in product((-1, 1), repeat=3)]
    positives = negatives = 0
    for enabled in range(256):
        answer = check([row for i, row in enumerate(clauses) if (enabled >> i) & 1])
        positives += int(answer)
        negatives += int(not answer)
    huge = int('6' * 61)
    examples = [
        [(huge, -7, 91), (91, huge, -7)] * 9,
        clauses + [(3, 2, 1), (-1, -3, -2)],
        [(1, 5, -9), (-1, 3, 9), (1, -3, -9)]
    ]
    for example in examples:
        answer = check(example)
        positives += int(answer)
        negatives += int(not answer)
    controls_unsat = clauses + [(1, 2, 7)]
    controls_sat = [(-1, -2, -7) if row == (-1, -2, -3) else row
                    for row in controls_unsat]
    assert not check(controls_unsat) and check(controls_sat)
    easy1, _, reps1, _, _ = files(encode(controls_unsat))
    easy2, _, reps2, _, _ = files(encode(controls_sat))
    assert reps1 == reps2
    easy_controls = {A: True, B: False, PAD: False, OTHER_PAD: False}
    assert residual(parse(easy1), easy_controls) == residual(parse(easy2), easy_controls)
    positives += 1
    negatives += 1
    print(f'Proper one-bit pairs: {positives} SAT and {negatives} UNSAT edits.')
    print('Every easy density, transversal certificate and per-source hard-model count agrees.')
