"""Recover the dense list gadget from signed, permuted DIMACS clauses."""
from collections import Counter, defaultdict
from itertools import combinations, product
from random import Random

import pycosat

from dense_ascii_chunk_circuit_audit import encode


class Unrecognized(Exception):
    """The general SAT algorithm must handle this input."""


def need(test):
    if not test:
        raise Unrecognized


def key(lits):
    return tuple(sorted(lits))


def without(terms, var):
    return [v for v in terms if abs(v) != var]


def cancel_padding(triples):
    positive, negative = Counter(), Counter()
    for c in triples:
        need(len(c) == 3 and len(set(map(abs, c))) == 3 and 0 not in c)
        for x in c:
            (positive if x > 0 else negative)[abs(x)] += 1
    choices = set(positive).intersection(negative)
    need(choices)
    pad = max(choices, key=lambda v: positive[v]+negative[v])
    a, b, rest = Counter(), Counter(), []
    for c in triples:
        if pad in c or -pad in c:
            (a if pad in c else b)[key(without(c, pad))] += 1
        else:
            rest.append(c)
    need(a == b)
    return a, rest


def split_units(pairs):
    by_names = defaultdict(list)
    for c, count in pairs.items():
        need(count == 1)
        by_names[key(map(abs, c))].append(c)
    doubles = [(names, cs) for names, cs in by_names.items() if len(cs) > 1]
    need(len(doubles) >= 2)
    common = set.intersection(*(set(names) for names, cs in doubles))
    need(len(common) == 1)
    pad = common.pop()
    units = {}
    for names, cs in doubles:
        need(len(cs) == 2 and pad in names)
        l, r = cs
        need((pad in l) != (pad in r))
        a, b = without(l, pad), without(r, pad)
        need(len(a) == 1 and a == b and abs(a[0]) not in units)
        units[abs(a[0])] = a[0]
        del pairs[l], pairs[r]
    need(all(pad not in map(abs, c) for c in pairs))
    return units, pad


def strip_guards(triples, pairs, units, pad):
    counts = Counter(x for c in triples for x in combinations(sorted(map(abs, c)), 2))
    common = [p for p, v in counts.items() if v > 2]
    need(len(common) == 1)
    guard, passive = common[0]
    need(pad not in common[0] and guard not in units and passive not in units)
    need(all(guard not in map(abs, c) and passive not in map(abs, c) for c in pairs))
    rest, polar = [], {}
    for c in triples:
        a = [x for x in c if abs(x) in common[0]]
        if a:
            need(len(a) == 2)
            for x in a:
                need(polar.setdefault(abs(x), x) == x)
        else:
            rest.append(c)
    return rest


def read_gates(triples, pairs):
    gates, siblings, consumed = {}, defaultdict(list), Counter()
    for c in triples:
        def supports(z):
            return all(key((-z, -u)) in pairs for u in c if u != z)
        output = [z for z in c if supports(z)]
        need(len(output) == 1)
        z = output[0]
        inputs = without(c, abs(z))
        need(abs(z) not in gates)
        gates[abs(z)] = (z, inputs)
        siblings[key(map(abs, inputs))].append(abs(z))
        consumed.update(key((-z, -u)) for u in inputs)
    need(all(pairs[c] >= n for c, n in consumed.items()))
    pairs.subtract(consumed)
    return gates, siblings


def threshold(gates, siblings, units):
    companion = {v for outputs in siblings.values() if len(outputs) == 2 for v in outputs}
    pinned = set(gates).intersection(units)
    need(len(pinned) == 1)
    end = pinned.pop()
    threshold_end = end
    schedule, visited = [], set()
    while end in gates:
        need(end not in visited and end not in companion)
        inputs = set(map(abs, gates[end][1]))
        both = inputs.intersection(companion)
        need(len(both) == 1)
        conjunction = both.pop()
        before = (inputs-{conjunction}).pop()
        inpair = key(map(abs, gates[conjunction][1]))
        disjunction = (set(siblings[inpair])-{conjunction}).pop()
        need(not visited.intersection((end, conjunction, disjunction)))
        visited.update((end, conjunction, disjunction))
        schedule.append((end, conjunction, disjunction, inpair))
        end = before
    need(end in units and visited == set(gates) and len(schedule) >= 2)
    two0 = end
    selected, orientation = {}, {}
    def require_orientation(lit):
        need(orientation.setdefault(abs(lit), lit) == lit)
    seen = None
    for total, conjunction, disjunction, inpair in reversed(schedule):
        if seen is None:
            starts = [v for v in inpair if v in units]
            need(len(starts) == 1)
            seen = seen0 = starts[0]
        need(seen in inpair)
        row = (set(inpair)-{seen}).pop()
        need(row not in gates and row not in units and row not in selected)
        for node in (total, conjunction, disjunction):
            out, args = gates[node]
            sign = 1 if node == conjunction else -1
            require_orientation(sign*out)
            for u in args:
                require_orientation(-sign*u)
        selected[row] = orientation[row]
        seen = disjunction
    need(len({seen0, two0, threshold_end}) == 3)
    for name, sign in ((seen0,-1), (two0,-1), (threshold_end,1)):
        need(units.pop(name) == sign*orientation[name])
    return selected, set(orientation)


def decode_banks(pairs, units, selected, threshold_vars):
    adjacency = defaultdict(dict)
    row_flags, data = defaultdict(list), set()
    for c, count in pairs.items():
        if count == 0:
            continue
        need(count == 1)
        incident = [u for u in c if abs(u) in threshold_vars]
        if incident:
            need(len(incident) == 1)
            s = incident[0]
            need(selected.get(abs(s)) == -s)
            f, = without(c, abs(s))
            row_flags[abs(s)].append(f)
            data.add(abs(f))
        else:
            a,b = c
            need(abs(b) not in adjacency[abs(a)])
            adjacency[abs(a)][abs(b)] = a
            adjacency[abs(b)][abs(a)] = b
    need(len(units) == 8 and all(len(d) <= 4 for d in adjacency.values()))
    bank_flags, covered = {}, set()
    for bank, start in enumerate(units):
        current = start
        need(start not in covered)
        covered.add(start)
        old = set()
        # At the first cursor the triangle literal is its forced-true unit.
        needed = units[start]
        while True:
            nbrs = set(adjacency[current])-old
            need(len(nbrs) == 2 and not nbrs.intersection(covered))
            a,b = nbrs
            need(b in adjacency[a])
            need(adjacency[current][a] == adjacency[current][b] == needed)
            for u,v in ((a,b),(b,a)):
                need(adjacency[u][current] == adjacency[u][v])
            covered.update(nbrs)
            further = [v for v in nbrs if len(adjacency[v]) > 2]
            if not further:
                need(not nbrs.issubset(data))
                flag = next(iter(nbrs.intersection(data)), a)
                bank_flags[flag] = (bank, -adjacency[flag][current])
                break
            need(len(further) == 1)
            nxt = further[0]
            flag = (nbrs-{nxt}).pop()
            bank_flags[flag] = (bank, -adjacency[flag][current])
            needed = -adjacency[nxt][current]
            old = {current, flag}
            current = nxt
    need(covered == set(adjacency))
    rows = []
    for row in selected:
        fs = row_flags[row]
        need(len(fs) == 8)
        values = []
        for f in fs:
            need(abs(f) in bank_flags)
            b, actual = bank_flags[abs(f)]
            need(actual == f)
            values.append((b, abs(f)))
        values.sort()
        need([b for b, _ in values] == list(range(8)))
        rows.append(tuple(v for b,v in values))
    return len(rows) != len(set(rows))


def recognize(clauses):
    """True/False is a certified SAT verdict; None selects the fallback."""
    try:
        pairs, triples = cancel_padding({key(c) for c in clauses})
        units, pad = split_units(pairs)
        need(all(pad not in map(abs, c) for c in triples))
        triples = strip_guards(triples, pairs, units, pad)
        gates, siblings = read_gates(triples, pairs)
        selected, threshold_vars = threshold(gates, siblings, units)
        need(not set(units).intersection(threshold_vars))
        return decode_banks(pairs, units, selected, threshold_vars)
    except Unrecognized:
        return None


def main():
    rng = Random(3191)
    transformed = duplicated = mutations = checked_mutations = 0
    for r in (1, 2, 3, 4, 5):
        n = 1 << r
        for trial in range(12):
            source = rng.sample(range(n*n), n)
            if trial % 2:
                source[1] = source[0]
            lines = encode(r, source).splitlines()
            names = int(lines[0].split()[2])
            perm = list(range(1,names+1))
            rng.shuffle(perm)
            mapping = [0]+[v*rng.choice((-1,1)) for v in perm]
            clauses = []
            for line in lines[1:]:
                c = [mapping[abs(int(x))]*(1 if int(x) > 0 else -1) for x in line.split()[:3]]
                rng.shuffle(c)
                clauses.append(c)
            rng.shuffle(clauses)
            expected = len(set(source)) != n
            assert recognize(clauses) == expected
            assert (pycosat.solve(clauses) != 'UNSAT') == expected
            transformed += 1
            copies = clauses + [list(reversed(c)) for c in clauses[::3]] * 2
            assert recognize(copies) == expected
            duplicated += 1
            for _ in range(6):
                changed = [c.copy() for c in clauses]
                i = rng.randrange(len(changed))
                if rng.randrange(3) == 0:
                    del changed[i]
                else:
                    j = rng.randrange(3)
                    changed[i][j] *= -1
                verdict = recognize(changed)
                if verdict is not None:
                    assert verdict == (pycosat.solve(changed) != 'UNSAT')
                    checked_mutations += 1
                mutations += 1
    print(f'{transformed} randomly renamed, polarity-switched and reordered formulas verified; '
          f'{duplicated} duplications; {mutations} mutations, {checked_mutations} recognized and cross-checked')


if __name__ == '__main__':
    main()
