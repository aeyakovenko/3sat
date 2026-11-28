"""Check the control subcubes and complete serialized ordinary 3-CNF edit square."""
from itertools import combinations, product

from one_bit_clause_density_threshold import encode, parse, residual, count_after


B, T = 1, 2
A, F = (3, 5), (4, 7)
CONTROL = (T, B, A[0], F[0], A[1], F[1])
LEFT = (-T, -B, A[0], -F[0])
RIGHT = (T, -B, A[1], -F[1])


def padded(left, right, extra):
    return [(left, right, extra), (left, right, -extra)]


def build(source, bonus):
    src = sorted({tuple(sorted(cl)) for cl in parse(encode(source))})
    reps = {abs(t): int('6' + str(abs(t))) for cl in src for t in cl}
    clauses, groups = [], []
    for j, cl in enumerate(src):
        group = tuple(int('9' + str(3*j+i)) for i in range(3))
        groups.append(group)
        clauses.append(group)
        for y, lit in zip(group, cl):
            sign = reps[abs(lit)] if lit > 0 else -reps[abs(lit)]
            clauses += [(-B, -y, sign), (-B, y, -sign)]

    for g, a, f in zip((T, -T), A, F):
        clauses += padded(g, -f, B)
        clauses += [(g, a, B), (g, a if bonus else -a, -B)]

    guards = {}
    private = []
    for l in LEFT:
        for r in RIGHT:
            if l == -r:
                continue
            key = (l,) if l == r else (l, r)
            guards[key] = []
            for _ in range(4):
                fills = tuple(int('8' + str(i)) for i in
                              range(len(private), len(private) + 3 - len(key)))
                private.extend(fills)
                row = key + fills
                clauses.append(row)
                guards[key].append(row)

    for u in private:
        clauses += padded(-B, u, T)
    clauses += padded(-B, -T, A[0])
    clauses += padded(-B, -A[1], T)
    clauses += padded(-B, -F[1], T)

    files = {}
    for mask in range(4):
        edited = [(g, B if mask & (1 << j) else A[j], F[j]) for j, g in enumerate((T, -T))]
        files[mask] = encode(clauses + edited)
    return files, groups, guards, private, reps, src


def verify_transversal(cnf, occ, guards, private):
    """Lower certificate applies even when a proposed transversal uses filler variables."""
    cover = set(map(abs, LEFT)) | {cl[0] for cl in occ}
    assert len(cover) == 4 + len(occ)
    assert all(not cover.isdisjoint(map(abs, cl)) for cl in cnf)
    assert len(set(private)) == len(private)
    assert len({v for cl in occ for v in cl}) == 3 * len(occ)
    assert not {v for cl in occ for v in cl}.intersection(set(CONTROL) | set(private))
    present = set(cnf)
    for key, rows in guards.items():
        assert len(rows) == 4 and set(rows) <= present
        petals = [set(cl[len(key):]) for cl in rows]
        assert all(a.isdisjoint(b) for a, b in combinations(petals, 2))
    # A budget of three after paying on occurrence triples is impossible.
    # Even if up to three slots were spent on private petals, four disjoint
    # sets suffice for each compatible control pair avoiding the spent slots.
    for k in range(4):
        for subset in combinations(CONTROL, k):
            taken = set(subset)
            assert any(taken.isdisjoint(map(abs, row)) for row in guards)


def complete_sat(rows):
    """A separate complete DPLL decision on the reparsed file."""
    while rows:
        if () in rows:
            return False
        units = {row[0] for row in rows if len(row) == 1}
        if any(-lit in units for lit in units):
            return False
        if not units:
            signs = {lit for row in rows for lit in row}
            units = {lit for lit in signs if -lit not in signs}
        if not units:
            var = abs(min(rows, key=len)[0])
            return any(complete_sat(residual(rows, {var: bit})) for bit in (False, True))
        rows = residual(rows, {abs(lit): lit > 0 for lit in units})
    return True


def check(source, bonus):
    files, occ, guards, private, reps, src = build(source, bonus)
    forms = {i: parse(blob) for i, blob in files.items()}
    names = {abs(lit) for cl in forms[0] for lit in cl}
    assert all({abs(lit) for cl in cnf for lit in cl} == names for cnf in forms.values())
    assert len(names) == 6 + len(private) + 3*len(occ) + len(reps)
    assert len({blob.splitlines()[0] for blob in files.values()}) == 1
    for i, j in combinations(range(4), 2):
        x, y = files[i], files[j]
        assert len(x) == len(y)
        assert sum((a ^ b).bit_count() for a, b in zip(x,y)) == (i ^ j).bit_count()
    diffs = [[(old, new) for old, new in zip(files[0], files[j]) if old != new] for j in (1, 2)]
    assert diffs == [[(ord('3'), ord('1'))], [(ord('5'), ord('1'))]]
    verify_transversal(forms[0], occ, guards, private)
    totals = [0, 0, 0, 0]
    source_count = 0
    for values in product((False, True), repeat=len(reps)):
        z = dict(zip(reps, values))
        src_model = all(any(z[abs(lit)] == (lit > 0) for lit in cl) for cl in src)
        source_count += src_model
        hard = 0
        for bits in product((False, True), repeat=6):
            fixed = {**{reps[k]: v for k, v in z.items()}, **dict(zip(CONTROL,bits))}
            j = int(fixed[T])
            # Evaluating the residual components proves every dormant model factor.
            for mask, cnf in forms.items():
                counted = count_after(cnf, names, fixed)
                dormant = (not fixed[B] and fixed[A[j]] and not fixed[F[j]]
                           and not (mask & (1 << j)))
                live = (fixed[B] and not fixed[T] and fixed[A[0]] == bonus
                        and all(not fixed[v] for v in (A[1], *F))
                        and (bonus or bool(mask & 1)))
                expected = int(dormant)*(1 << len(private))*(7**len(occ)) + int(live and src_model)
                assert counted == expected
                totals[mask] += counted
                if mask == 3:
                    hard += counted
        assert hard == int(src_model)
    m = len(occ)
    assert (totals[0] - int(bonus)*source_count) * 8 * 8**m == (1 << len(names)) * 7**m
    assert totals[3] == source_count
    assert [complete_sat(form) for form in forms.values()] == [True, True, True, bool(source_count)]
    return bool(source_count)


def check_three(source, bonus):
    s, t = 2, 4
    a0, a1, a2 = 3, 5, 9
    ctr = (B, s, t, a0, a1, a2)
    a = (a0, a1, a2)
    gates = ((s, t), (-s, t), (s, -t))
    ranks = ((-s, -t), (-s, a1), (-t, a2),
             (s, a0, a2), (t, a0, a1), (a0, a1, a2))
    prior, groups, _, _, reps, source = build(source, bonus)
    # Copy only the occurrence and source-representative rows from the prior wrapper.
    body = [cl for cl in parse(prior[0])
            if any(str(abs(v)).startswith(('6','9')) and abs(v) >= 10 for v in cl)]
    body += padded(-s, -t, B)
    private = []
    blocks = {}
    for key in [(-B,), *ranks]:
        if len(key) == 3:
            body.append(key)
            blocks[key] = [key]
            continue
        blocks[key] = []
        for _ in range(4):
            fresh = tuple(int('8'+str(i)) for i in
                          range(len(private),len(private)+3-len(key)))
            body.append((*key,*fresh))
            blocks[key].append((*key,*fresh))
            private.extend(fresh)
    hard_lits = (-s, -t, a0 if bonus else -a0, a1, a2, *private)
    for lit in hard_lits:
        body += padded(-B, lit, t if abs(lit) == s else s)
    files = [encode(body+[(*g, B if mask & (1 << j) else a[j]) for j,g in enumerate(gates)])
             for mask in range(8)]
    assert len({f.splitlines()[0] for f in files}) == 1
    for mask, fl in enumerate(files):
        assert len(fl) == len(files[0])
        diffs = [(x,y) for x,y in zip(files[0],fl) if x != y]
        assert diffs == [(ord(str(v)),ord('1')) for j,v in enumerate(a) if mask & (1 << j)]
        assert sum((x ^ y).bit_count() for x,y in diffs) == mask.bit_count()
    cnfs = [parse(f) for f in files]
    names = {abs(lit) for cl in cnfs[0] for lit in cl}
    cover = {s,t,B,a0} | {cl[0] for cl in groups}
    assert len(cover) == len(groups)+4 and all(not cover.isdisjoint(map(abs,cl)) for cl in cnfs[0])
    for k in range(4):
        for trial in combinations(ctr,k):
            # The padded -B block forces paying one, then the six guards cost three more.
            assert any(set(map(abs,key)).isdisjoint(trial) for key in blocks)
    for key, rows in blocks.items():
        if len(key) < 3:
            assert len(rows) == 4
            assert all(set(x[len(key):]).isdisjoint(y[len(key):]) for x,y in combinations(rows,2))
        assert set(rows) <= set(cnfs[0])
    source_count = 0
    totals = [0]*8
    for values in product((False,True),repeat=len(reps)):
        z = dict(zip(reps,values))
        model = all(any(z[abs(l)] == (l > 0) for l in cl) for cl in source)
        source_count += model
        per = [0]*8
        for control_bits in product((False,True),repeat=6):
            fixed = {**{reps[k]:v for k,v in z.items()}, **dict(zip(ctr,control_bits))}
            mode = int(fixed[s])+2*int(fixed[t])
            for mask,cnf in enumerate(cnfs):
                actual = count_after(cnf,names,fixed)
                off = (not fixed[B] and mode<3 and fixed[a[mode]] and not mask & (1 << mode))
                on = (fixed[B] and mode==0 and fixed[a0] == bonus and fixed[a1] and fixed[a2]
                      and (bonus or bool(mask&1)))
                assert actual == int(off)*(1 << len(private))*7**len(groups)+int(on and model)
                per[mask] += actual
                totals[mask] += actual
        assert per[7] == int(model)
    assert (totals[0]-int(bonus)*source_count)*16*8**len(groups) == 3*(1<<len(names))*7**len(groups)
    assert totals[7] == source_count
    assert [complete_sat(cnf) for cnf in cnfs] == [True]*7 + [bool(source_count)]
    return bool(source_count)


if __name__ == '__main__':
    signs = [tuple(v*s for v,s in enumerate(bits,1)) for bits in product((-1,1),repeat=3)]
    huge = int('5' * 51)
    cases = [[], [(1,2,3)], signs[:7], signs, signs + [(-1,-2,7)],
             [(huge,-7,4),(4,huge,-7)]*4]
    verdicts = [check(case, bonus) for case in cases for bonus in (False, True)]
    print(f'{len(verdicts)} serialized edit squares, both singleton edits SAT in each; '
          f'{sum(verdicts)} jointly SAT, {len(verdicts)-sum(verdicts)} jointly UNSAT.')
    print('Every control cofactor, hard projection, density and transversal certificate passed.')

    more = [check_three(case,bonus) for case in ([], signs[:7], signs)
            for bonus in (False,True)]
    print(f'{len(more)} three-edit cubes, all proper subedits SAT; '
          f'{sum(more)} jointly SAT, {len(more)-sum(more)} jointly UNSAT.')
