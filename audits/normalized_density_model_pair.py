"""Construct and check pairs of models using the two block packings."""
from itertools import combinations, product


def variables(clause):
    return frozenset(map(abs, clause))


def holds(clause, ones):
    return any((abs(lit) in ones) == (lit > 0) for lit in clause)


def restrict(clause, fixed, ones):
    if any(abs(lit) in fixed and (abs(lit) in ones) == (lit > 0) for lit in clause):
        return None
    return tuple(lit for lit in clause if abs(lit) not in fixed)


def settings(scope):
    ordered = sorted(scope)
    for bits in product((False, True), repeat=len(ordered)):
        yield frozenset(x for x, b in zip(ordered, bits) if b)


def first_packing(cnf, cap):
    supports = sorted({tuple(sorted(variables(c))) for c in cnf if len(c) == 3})
    already = set()
    for _ in range(cap + 1):
        owner = {}
        for support in supports:
            if not already.isdisjoint(support):
                continue
            overlap = next((v for v in support if v in owner), None)
            if overlap is not None:
                already.update(support)
                already.update(owner[overlap])
                break
            for v in support:
                owner[v] = support
        else:
            return frozenset(already)
    return None


def under_first(live, names, cap):
    starts = {}
    additional = []
    for clause in live:
        support = variables(clause)
        if len(clause) == 3 and support not in starts:
            starts[support] = clause
        else:
            additional.append(clause)
    scopes = list(starts)
    used = set().union(*scopes)
    assert sum(map(len, scopes)) == len(used)
    scopes.extend(frozenset([v]) for v in sorted(names - used))
    domains = [[x for x in settings(s) if s not in starts or holds(starts[s], x)] for s in scopes]
    loc = {v: i for i, s in enumerate(scopes) for v in s}
    active = []
    marked = set()
    packing = 0
    for row in additional:
        touched = sorted({loc[abs(v)] for v in row})
        assert len(touched) <= 2
        if all(holds(row, set().union(*states))
               for states in product(*(domains[i] for i in touched))):
            continue
        active.append(row)
        if marked.isdisjoint(touched):
            packing += 1
            if packing > cap:
                return
            marked.update(touched)
    marked = sorted(marked)
    fixed = set().union(*(scopes[i] for i in marked))
    for chosen in product(*(domains[i] for i in marked)):
        ones = set().union(*chosen)
        allowed = [d.copy() for d in domains]
        for row in active:
            rest = restrict(row, fixed, ones)
            if rest is None:
                continue
            if not rest:
                break
            ids = {loc[abs(v)] for v in rest}
            assert len(ids) == 1
            i = ids.pop()
            allowed[i] = [s for s in allowed[i] if holds(rest, s)]
            if not allowed[i]:
                break
        else:
            x, y = set(ones), set(ones)
            for i in range(len(scopes)):
                if i not in marked:
                    left, right = max(product(allowed[i], repeat=2),
                                      key=lambda p: len(p[0] ^ p[1]))
                    x.update(left)
                    y.update(right)
            yield x, y


def pair_at_budget(cnf, cap):
    names = set().union(*(variables(c) for c in cnf))
    fixed = first_packing(cnf, cap)
    if fixed is None:
        return None
    for ones in settings(fixed):
        live = [c for row in cnf if (c := restrict(row, fixed, ones)) is not None]
        if () in live:
            continue
        for x, y in under_first(live, names - fixed, cap):
            x.update(ones)
            y.update(ones)
            if len(names) - len(x ^ y) <= cap:
                assert all(holds(c, x) and holds(c, y) for c in cnf)
                return x, y
    return None


def tiny():
    n = 4
    supports = list(combinations(range(1, n+1), 3))
    choices = [[None] + [tuple(v if s else -v for v, s in zip(e, polarities))
                         for polarities in product((False, True), repeat=3)]
               for e in supports]
    count = 0
    for decision in product(*choices):
        cnf = tuple(c for c in decision if c is not None)
        exists = any(all(holds(c, x) for c in cnf) for x in settings(range(1, n+1)))
        assert (pair_at_budget(cnf, n) is not None) == exists
        count += 1
    unsat = tuple(c for c in choices[0] if c is not None)
    assert pair_at_budget(unsat, n) is None
    return count


def scalable():
    independent = [tuple(range(3*i+1, 3*i+4)) for i in range(160)]
    x, y = pair_at_budget(independent, 0)
    assert x.isdisjoint(y) and len(x | y) == 480
    extra = [(1,4), (-7,10), (1,3,-2), (13,), (-16,17)]
    pair = pair_at_budget(independent + extra, 20)
    assert pair is not None
    conditional = independent + [(-481,-1,4),(-481,1,-4),(-481,)]
    assert pair_at_budget(conditional, 10) is not None


if __name__ == '__main__':
    print('Signed four-variable catalogs checked:', tiny())
    scalable()
    print('Independent, narrowed and guarded examples checked on up to 481 variables.')
