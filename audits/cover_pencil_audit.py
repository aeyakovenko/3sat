"""Check the exact covers, supplied defects, and binary basis-change census."""

from itertools import combinations, product


P = (2,6,8,9,0,7,13,3,1,5,4,14,11,10,12)
Q = (6,0,11,10,2,12,14,9,7,8,13,5,1,4,3)
FILLER_P = (1,3,4,5,2,0)
FILLER_Q = (5,2,1,4,0,3)


def inverse(perm):
    assert sorted(perm) == list(range(len(perm)))
    return tuple(perm.index(i) for i in range(len(perm)))


def instances(p, q):
    return [(p, q), (inverse(p), inverse(q))]


def row_sums(p, q, weights):
    return [weights[i] + weights[j] + weights[k] for i, (j,k) in enumerate(zip(p,q))]


def indicator(n, selected):
    return [int(i in selected) for i in range(n)]


def all_covers(p, q):
    n = len(p)
    return [s for s in combinations(range(n), n//3) if row_sums(p,q,indicator(n,s)) == [1]*n]


def connected(p, q):
    reached = {0}
    while True:
        step = reached | {p[i] for i in reached} | {q[i] for i in reached}
        if step == reached:
            return len(step) == len(p)
        reached = step


def pencil_pairs():
    n = len(P)
    signed = [-1] + [1]*6 + [0]*8
    packing = {1,2,10,14}
    results = []
    for p, q in instances(P,Q):
        assert connected(p,q)
        assert all(len({i,j,k}) == 3 for i,(j,k) in enumerate(zip(p,q)))
        assert row_sums(p,q,signed) == [1]*n
        coverage = row_sums(p,q,indicator(n,packing))
        assert coverage.count(0) == 3 and set(coverage) == {0,1}
        assert {i for i,value in enumerate(coverage) if value==0} == {5,7,9}
        results.append(all_covers(p,q))
    assert results == [[(1,2,3,5,13)], []]
    assert all(all_covers(p,q) == [(2,5)] for p,q in instances(FILLER_P,FILLER_Q))
    return sum(len(solutions) for solutions in results)


def parity_census(support):
    arity = len(support[0])
    gl2 = [m for m in product(range(2),repeat=4) if (m[0]*m[3]-m[1]*m[2])%2]
    assert len(gl2) == 6
    total = 0
    for bases in product(gl2,repeat=arity):
        parities = set()
        for target in product(range(2),repeat=arity):
            value = sum(all(base[2*b+a] for base,b,a in zip(bases,target,source)) for source in support)
            if value%2:
                parities.add(sum(target)%2)
        assert parities == {0,1}
        total += 1
    return total


if __name__ == '__main__':
    assert pencil_pairs() == 1
    copy = parity_census([(0,0,0),(1,1,1)])
    paired = parity_census([(0,0,0,1),(0,0,1,0),(1,1,0,0)])
    print('3,003 candidate five-sets per orientation; 15 candidate pairs per filler orientation;')
    print('mixed parity in all',copy,'copy and',paired,'contracted-vertex binary basis choices.')
