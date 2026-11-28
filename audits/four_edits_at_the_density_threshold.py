"""The four-edit mixed-guard threshold, checked on serialized proper DIMACS files."""
from itertools import combinations, product

from one_bit_clause_density_threshold import encode, parse, residual, count_after
from two_edits_at_the_density_threshold import complete_sat, padded


D = 11
# Mathematical x,A,B,C are negative literals of their physical variables.
X, Y, Z, A, B, C = -10, 2, 4, -13, -15, -19
CONTROL = (D, 10, 2, 4, 13, 15, 19)
BOXES = ((X,Y,Z), (-X,Y,A), (X,-Z,B), (-Y,Z,C))
GUARDS = ((X,Y,Z), (X,A,C), (Y,B,C), (Z,A,B))
OLD = ((D,-Y,-Z), (A,X,-Y), (B,-X,Z), (C,Y,-Z))
NEW = ((-X,-Y,-Z), (-D,X,-Y), (-D,-X,Z), (-D,Y,-Z))
PRIVATE = tuple(range(80,88))


def build(source, bonus):
    src = sorted({tuple(sorted(cl)) for cl in parse(encode(source))})
    reps = {abs(t): int('6'+str(abs(t))) for cl in src for t in cl}
    common = list(GUARDS)
    occ = []
    for j, cl in enumerate(src):
        ys = tuple(int('9'+str(3*j+i)) for i in range(3))
        occ.append(ys)
        common.append(ys)
        for y, old in zip(ys, cl):
            lit = reps[abs(old)] if old > 0 else -reps[abs(old)]
            common += [(D, -y, lit), (D,y,-lit)]
    petals = [(D, PRIVATE[2*i], PRIVATE[2*i+1]) for i in range(4)]
    common += petals
    hard = (-X, -Y, Z, A, B, C if bonus else -C)
    for lit in (*hard, *PRIVATE):
        common += padded(D, lit, Y if abs(lit) == abs(X) else X)
    files = [encode(common+[NEW[j] if mask & (1<<j) else OLD[j] for j in range(4)])
             for mask in range(16)]
    return files, src, reps, occ, hard, petals


def check(source, bonus):
    files, src, reps, occ, hard, petals = build(source, bonus)
    cnfs = [parse(f) for f in files]
    names = {abs(l) for cl in cnfs[0] for l in cl}
    assert len(names) == len(CONTROL)+len(PRIVATE)+len(reps)+3*len(occ)
    assert len({f.splitlines()[0] for f in files}) == 1
    for i,j in combinations(range(16),2):
        old, new = files[i], files[j]
        assert len(old) == len(new)
        assert sum((a^b).bit_count() for a,b in zip(old,new)) == (i^j).bit_count()
    assert [[(chr(a),chr(b)) for a,b in zip(files[0],files[1<<j]) if a!=b]
            for j in range(4)] == [[('1','0')],[('3','1')],[('5','1')],[('9','1')]]

    certificate = (*OLD[1:], *GUARDS)
    assert set(certificate) <= set(cnfs[0])
    for v,w in combinations(map(abs, (X,Y,Z,A,B,C)),2):
        assert any({v,w}.isdisjoint(map(abs,cl)) for cl in certificate)
    assert set(petals) <= set(cnfs[0])
    assert len({u for row in petals for u in row[1:]}) == 8
    support = {abs(v) for row in certificate for v in row}
    assert support.isdisjoint(PRIVATE) and D not in support
    assert len({u for row in occ for u in row}) == 3*len(occ)
    assert all((support|set(PRIVATE)|{D}).isdisjoint(row) for row in occ)
    upper = {D,abs(X),Y,Z} | {row[0] for row in occ}
    assert len(upper) == len(occ)+4 and all(not upper.isdisjoint(map(abs,cl)) for cl in cnfs[0])
    # Any transversal of the source-independent part with at most 3 slots
    # needs d to cover the four private petals, and then misses a certificate triple.
    for size in range(4):
        for hit in combinations(CONTROL+PRIVATE,size):
            assert any(set(hit).isdisjoint(map(abs,cl)) for cl in (*certificate,*petals))

    counts = [0]*16
    source_count = 0
    for values in product((False,True),repeat=len(reps)):
        za = dict(zip(reps,values))
        model = all(any(za[abs(l)] == (l>0) for l in row) for row in src)
        source_count += model
        zr = {reps[k]:v for k,v in za.items()}
        for bits in product((False,True),repeat=len(CONTROL)):
            ctrl = dict(zip(CONTROL,bits))
            z = {**zr,**ctrl}
            is_true = lambda l: ctrl[abs(l)] == (l>0)
            boxes = [i for i,box in enumerate(BOXES) if ctrl[D] and all(map(is_true,box))]
            assert len(boxes) <= 1
            live = not ctrl[D] and all(map(is_true,hard))
            for mask,rows in enumerate(cnfs):
                dormant = bool(boxes) and not (mask & (1 << boxes[0]))
                hard_ok = live and (bonus or bool(mask & 8))
                # For fixed controls, every other choice group is forced or independent.
                count = count_after(rows, names, z)
                assert count == int(dormant)*(1<<len(PRIVATE))*(7**len(occ)) + int(hard_ok and model)
                counts[mask] += count
    assert counts[-1] == source_count
    assert (counts[0]-int(bonus)*source_count)*4*8**len(occ) == (1<<len(names))*7**len(occ)
    assert [complete_sat(cnf) for cnf in cnfs] == [True]*15+[bool(source_count)]
    return bool(source_count)


if __name__ == '__main__':
    signs = [tuple(i*s for i,s in enumerate(bits,1)) for bits in product((-1,1),repeat=3)]
    cases = [[], signs[:7], signs]
    outcomes = [check(src,bonus) for src in cases for bonus in (False,True)]
    print(f'{len(outcomes)} four-edit cubes, 90 strict subedits SAT; '
          f'{sum(outcomes)} jointly SAT and {len(outcomes)-sum(outcomes)} jointly UNSAT.')
    print('Every byte distance, control cofactor, threshold or bonus density, and transversal holds.')
