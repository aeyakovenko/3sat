"""Check labelled output moments, the colored four-cycle, and signed CNF extraction."""

from itertools import combinations, permutations, product
from math import prod


def probability(bits, means):
    return prod(x if bits >> i & 1 else 1-x for i, x in enumerate(means))


def contracted(d, x, y, weights):
    k = len(weights)
    result = 0
    for a, b in product(range(1 << d), repeat=2):
        terms = [1] + [0]*((1 << k)-1)
        for i, j in product(range(d), repeat=2):
            if (a >> i) & (b >> j) & 1:
                for mask in range(len(terms)-1, -1, -1):
                    for color, table in enumerate(weights):
                        if not mask >> color & 1:
                            terms[mask | (1 << color)] += terms[mask] * table[d*i+j]
        result += terms[-1] * probability(a, x) * probability(b, y)
    return result


def edge_sum(d, x, y, weights):
    value = 0
    for edges in permutations(range(d*d), len(weights)):
        left = {e//d for e in edges}
        right = {e%d for e in edges}
        value += prod(x[i] for i in left) * prod(y[j] for j in right) * prod(
            table[e] for table, e in zip(weights, edges))
    return value


def moments():
    count = 0
    for d in (1, 2, 3):
        for k in range(1, 5):
            for seed in range(3):
                x = [2*i-seed-1 for i in range(d)]
                y = [seed+3-2*j for j in range(d)]
                weights = [[(e*(c+2)+seed+2*c+1)%7-3 for e in range(d*d)] for c in range(k)]
                assert contracted(d,x,y,weights) == edge_sum(d,x,y,weights)
                count += 1
    return count


def cycles():
    m = 2
    block_pairs = list(product(range(m), repeat=2))
    monomials = []
    for (i,j), (k,p), (l,s), (g,h) in product(block_pairs, repeat=4):
        # Physical rows/cols of four different blocks in the 2m-square output.
        rows = {i,m+k,m+l,g}
        cols = {j,p,m+s,m+h}
        if len(rows) == len(cols) == 2 and g == h:
            monomials.append((m*i+j,m*p+k,m*l+s))
    for a,b,z in product(range(1 << (m*m)),repeat=3):
        extracted = sum((a>>x) & (b>>y) & (z>>w) & 1 for x,y,w in monomials)
        triangle = sum((a>>(m*i+j)) & (b>>(m*j+k)) & (z>>(m*k+i)) & 1
                       for i,j,k in product(range(m), repeat=3))
        assert extracted == triangle
    return 1 << (3*m*m)


def selector_response():
    d = 2
    def observed(a, b, q, z):
        if not q:
            return 0
        k = (q & -q).bit_length()-1
        return sum(z[d*i+j] for i, j in product(range(d), repeat=2)
                   if ((a >> (d*i+k)) & (b >> (d*k+j)) & 1))

    for seed in range(12):
        x = [((seed+2)*(v+1)) % 7-3 for v in range(d*d)]
        y = [(seed+3*v) % 5-2 for v in range(d*d)]
        z = [(seed+v*v) % 7-1 for v in range(d*d)]
        means = [seed-3, (seed % 5)-1]
        direct = sum(probability(a, x)*probability(b, y)*probability(q, means)*observed(a,b,q,z)
                     for a,b,q in product(range(1 << (d*d)), range(1 << (d*d)), range(1 << d)))
        formula = sum(means[k]*prod(1-m for m in means[:k])*x[d*i+k]*y[d*k+j]*z[d*i+j]
                      for i,j,k in product(range(d), repeat=3))
        assert direct == formula
    for a,b,zbits in product(range(1 << (d*d)), repeat=3):
        z = [(zbits >> j) & 1 for j in range(d*d)]
        # Linear coefficient of u^|q| (1-u)^(d-|q|) for each selector mask.
        extracted = sum((-d if not q else int(q.bit_count()==1))*observed(a,b,q,z)
                        for q in range(1 << d))
        trilinear = sum((a >> (d*i+k)) & (b >> (d*k+j)) & z[d*i+j] & 1
                        for i,j,k in product(range(d), repeat=3))
        assert extracted == trilinear
    return 12, 1 << (3*d*d)


def coefficient(n, clauses, weights):
    m = len(clauses)
    total = 0
    for left in range(1 << (2*n)):
        # Actual [u^n] of all normalized left weights of this assignment.
        left_coeffs = [1] + [0]*n
        for i, weight in enumerate(weights):
            constant, linear = (0, weight) if left >> i & 1 else (1, -weight)
            left_coeffs = [constant*c + (linear*left_coeffs[k-1] if k else 0)
                           for k,c in enumerate(left_coeffs)]
        for right in range(1 << m):
            if any((right >> j & 1) and any(left >> k & 1 for k in clause)
                   for j,clause in enumerate(clauses)):
                continue
            total += left_coeffs[n] * (-1)**(m-right.bit_count())
    return (-1)**m * total


def cnfs():
    n = 2
    possible = [()] + [(x,) for x in range(2*n)] + list(combinations(range(2*n),2))
    weights = [2,3,-1,5]
    count = 0
    for extra in [()] + [(c,) for c in possible] + list(combinations(possible,2)):
        clauses = [(0,1),(2,3),*extra]
        truth = 0
        for assignment in product(range(2),repeat=n):
            selected = {2*i+b for i,b in enumerate(assignment)}
            if all(selected.intersection(clause) for clause in clauses):
                truth += prod(weights[j] for j in selected)
        assert coefficient(n,clauses,weights) == truth
        count += 1
    return count


if __name__ == '__main__':
    print(f'{moments()} integer moment evaluations; {cycles()} complete binary factor triples; '
          f'{cnfs()} literal-clause systems')
    general, bits = selector_response()
    print(f'{general} exact normalized selector contractions; {bits} selector linear-coefficient cases')
