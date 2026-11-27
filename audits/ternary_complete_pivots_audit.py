"""A complete ternary CSP with one forbidden tuple per triple and cubic private rows."""

from itertools import combinations, product
from math import comb

SITES = tuple(product(range(3), range(4)))


def guard_pair(p, q):
    r, c = SITES[p]
    s, d = SITES[q]
    if r == s:
        return 0
    if c == d:
        return 1
    if (c - r) % 4 == (d - s) % 4:
        return 2
    return 0


def build(t):
    assert t >= 3
    width = 2*t-3
    real = 3*width
    groups = []
    formula = {}

    def put(names, forbidden):
        ordered = sorted(zip(names, forbidden))
        support = tuple(i for i, _ in ordered)
        assert len(set(support)) == 3 and support not in formula
        formula[support] = tuple(b for _, b in ordered)

    for h in range(3):
        variables = tuple(range(h*width, h*width+t))
        carries = tuple(range(h*width+t, (h+1)*width))
        groups.append((variables, carries))
        if t == 3:
            put(variables, (0, 0, 0))
        else:
            put((*variables[:2], carries[0]), (0, 0, 0))
            for j in range(len(carries)-1):
                put((carries[j], variables[j+2], carries[j+1]), (1, 0, 0))
            put((carries[-1], *variables[-2:]), (1, 0, 0))
    targets = tuple(product(*(g for g, _ in groups)))
    for names in targets:
        put(names, (1, 1, 1))
    boolean = dict(formula)
    for x in range(real):
        for p, q in combinations(range(len(SITES)), 2):
            symbol = guard_pair(p, q)
            put((x, real+p, real+q), (2, symbol, symbol))
    n = real+len(SITES)
    for support in combinations(range(n), 3):
        if support not in formula:
            put(support, (2, 2, 2))
    assert len(formula) == comb(n, 3)
    return groups, real, targets, boolean, formula


def failed(row, clauses):
    for (a,b,c), (pa,pb,pc) in clauses.items():
        if row[a] == pa and row[b] == pb and row[c] == pc:
            yield (a,b,c)


def main():
    guards = [(p,q,guard_pair(p,q)) for p,q in combinations(range(len(SITES)), 2)]
    covered = 0
    for row in product(range(3), repeat=len(SITES)):
        assert any(row[p] == row[q] == z for p,q,z in guards)
        covered += 1
    total_witnesses = total_formulas = exhaustive = 0
    for t in (3, 4, 5, 6):
        groups, real, targets, boolean, formula = build(t)
        if t <= 4:
            for row in product(range(2), repeat=real):
                assert next(failed(row, boolean), None) is not None
                exhaustive += 1
        for target in targets:
            w = [0] * (real + len(SITES))
            for (group, carries), choice in zip(groups, target):
                w[choice] = 1
                for j, carry in enumerate(carries):
                    w[carry] = int(choice not in group[:j+2])
            assert list(failed(w, formula)) == [target]
            total_witnesses += 1
        total_formulas += len(formula)
    print(f"{covered:,} ternary guard assignments ruled out")
    print(f"{exhaustive:,} Boolean core assignments exhausted")
    print(f"{total_witnesses} private witnesses checked against four complete catalogs "
          f"with {total_formulas:,} total triples")


if __name__ == "__main__":
    main()
