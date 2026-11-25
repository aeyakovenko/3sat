"""Audit the one-negative patch on the physical permutation arrays of guarded CNFs."""

from itertools import combinations_with_replacement, product

from two_permutation_sat_audit import compile_source


def inverse(p):
    result = [None] * len(p)
    for source, target in enumerate(p):
        assert result[target] is None
        result[target] = source
    return result


def coverage(p, q, weights):
    counts = list(weights)
    for v, value in enumerate(weights):
        counts[p[v]] += value
        counts[q[v]] += value
    return counts


def guard(raw):
    guard_var = 1 + max((abs(x) for row in raw for x in row), default=0)
    fresh = guard_var
    clauses = []
    selectors = []
    for clause in dict.fromkeys(raw):
        if not clause:
            clauses.append((-guard_var,))
            continue
        a, b, c = clause + (clause[-1],) * (3-len(clause))
        fresh += 1
        h = fresh
        selectors.append((h, a))
        clauses.extend([(-h, guard_var), (-h, -a), (-guard_var, a, h), (-h, b, c)])
    return guard_var, selectors, clauses


def literal_value(assignment, literal):
    return assignment[abs(literal)] ^ int(literal < 0)


def compile_positive(guard_var, clauses, assignment):
    zero = ('zero',)
    one = ('one',)
    triples = [(zero, zero, one)]
    vals = {zero: 0, one: 1}
    all_vars = {abs(literal) for clause in clauses for literal in clause} | {guard_var}
    for i in sorted(all_vars):
        vals['base', i] = assignment[i]
        vals['neg', i] = 1 - assignment[i]
        triples.append((('base', i), ('neg', i), zero))

    def opposite_wire(literal):
        return ('neg' if literal > 0 else 'base', abs(literal))

    for j, clause in enumerate(clauses):
        t = clause + (clause[-1],) * (3-len(clause))
        chosen = next(k for k, literal in enumerate(t) if literal_value(assignment, literal))
        choices = [('choice', j, k) for k in range(3)]
        triples.append(tuple(choices))
        for k, choice in enumerate(choices):
            vals[choice] = int(k == chosen)
            for i, wanted in enumerate((t[k],) + tuple(-q for q in t[:k])):
                slack = ('slack', j, k, i)
                vals[slack] = literal_value(assignment, wanted) - vals[choice]
                triples.append((choice, opposite_wire(wanted), slack))
    assert all(v in (0, 1) for v in vals.values())
    assert all(sum(vals[v] for v in row) == 1 for row in triples)
    return triples, vals


def base_weights(labels, names, assignment):
    y = [0] * len(labels)
    for i, name in enumerate(names):
        bit = assignment[name]
        for wire, value in [('x', bit), ('w', bit), ('a', 1-bit), ('b', 0)]:
            y[labels[wire, i]] = value
    return y


def patch():
    # Choose the colors cyclically, with D having color i in D-row i and
    # H_i having color i in row 3+i. The physical variable labels are I-edges.
    rows = []
    for i in range(3):
        rows.append({i: 'D', (i+2) % 3: f'H{(i+1)%3}', (i+1) % 3: f'H{(i+2)%3}'})
    for i in range(3):
        rows.append({i: f'H{i}', (i+1) % 3: 'Z0', (i+2) % 3: 'Z1'})
    labels = {row[0]: j for j, row in enumerate(rows)}
    p_back = [labels[row[1]] for row in rows]
    q_back = [labels[row[2]] for row in rows]
    p, q = inverse(p_back), inverse(q_back)
    solutions = [bits for bits in product(range(2), repeat=6) if coverage(p,q,bits)==[1]*6]
    assert len(solutions)==2 and all(s[labels['H0']]==0 for s in solutions)
    return p_back, q_back, labels, solutions


def cyclic_lift(p, q, y, d):
    """Give a d-cover explicit cyclic sheet shifts realising the vertex counts."""
    threes = d % 2
    twos = (d-3*threes)//2
    z = [twos * (1-v) + threes for v in y]
    assert all(0 <= a <= d for a in z) and coverage(p, q, z) == [d]*len(z)
    back = inverse(p)
    lift_p, lift_q, chosen = [], [], []
    for v in range(len(p)):
        for sheet in range(d):
            left, right = p[v], q[v]
            lift_p.append(d*left + (sheet + z[left]) % d)
            lift_q.append(d*right + (sheet + z[right] + z[back[right]]) % d)
            chosen.append(int(sheet < z[v]))
    inverse(lift_p)
    inverse(lift_q)
    assert coverage(lift_p,lift_q,chosen) == [1]*len(chosen)


def audit(raw, sheet_counts):
    g, selectors, clauses = guard(raw)
    source_vars = sorted({abs(literal) for row in raw for literal in row})
    def assignment(original, guard_bit):
        out = dict(zip(source_vars,original))
        out[g]=guard_bit
        for h,a in selectors:
            out[h]=guard_bit * (1-literal_value(out,a))
        return out

    start = assignment([0] * len(source_vars), 0)
    triples, initial = compile_positive(g, clauses, start)
    base_p_back, base_q_back, labels, names = compile_source(triples)
    old = base_weights(labels, names, initial)
    # The color-zero matching fixes the physical variable labels.
    port = labels['x', names.index(('neg', g))]
    assert old[port] == 1
    gp, gq, gadget_labels, gadget_solutions = patch()
    n = len(base_p_back)
    p_back = list(base_p_back) + [n + u for u in gp]
    q_back = list(base_q_back) + [n + u for u in gq]
    h0 = n + gadget_labels['H0']
    base_row = p_back.index(port)
    gadget_row = p_back.index(h0)

    before = old + list(gadget_solutions[0])
    assert coverage(inverse(p_back), inverse(q_back), before) == [1] * len(before)
    p_back[base_row], p_back[gadget_row] = p_back[gadget_row], p_back[base_row]
    p, q = inverse(p_back), inverse(q_back)
    assert all(len({u, p_back[u], q_back[u]}) == 3 for u in range(len(p)))

    # The original Boolean selection now misses just the detached base row
    # and covers the new gadget row twice. Remove D, one of its two columns.
    defects = coverage(p, q, before)
    assert defects[base_row] == 0 and defects[gadget_row] == 2
    assert defects.count(0) == defects.count(2) == 1
    assert set(defects) == {0, 1, 2}
    partial = before.copy()
    dropped = n + gadget_labels['D']
    assert partial[dropped] == 1 and gadget_row in {dropped, p[dropped], q[dropped]}
    partial[dropped] = 0
    packing = coverage(p, q, partial)
    assert set(packing) == {0, 1} and packing.count(0) == 3
    assert 3 * sum(partial) == len(p) - 3

    # A separate integer solution has D=-1; truncating D highlights exactly
    # the three rows of its triple. Check this using the physical forward maps.
    signed_values = {'D': -1, 'Z0': 0, 'Z1': 0, 'H0': 1, 'H1': 1, 'H2': 1}
    tail = [0] * 6
    for wire, value in signed_values.items():
        tail[gadget_labels[wire]] = value
    y = old + tail
    assert y.count(-1) == 1 and coverage(p, q, y) == [1] * len(y)
    clipped = coverage(p, q, [int(value == 1) for value in y])
    double = {u for u, value in enumerate(clipped) if value == 2}
    assert set(clipped) == {1, 2}
    assert double == {dropped, p[dropped], q[dropped]} and len(double) == 3
    for d in sheet_counts:
        cyclic_lift(p, q, y, d)

    positives = 0
    for bits in product(range(2), repeat=len(source_vars)):
        source = dict(zip(source_vars, bits))
        true = all(any(literal_value(source, a) for a in row) for row in raw)
        applied = assignment(bits, 1)
        guarded_true = all(any(literal_value(applied, a) for a in row) for row in clauses)
        assert true == guarded_true
        if true:
            same, values = compile_positive(g, clauses, applied)
            assert same == triples
            base = base_weights(labels, names, values)
            assert base[port] == 0
            for gadget in gadget_solutions:
                assert coverage(p, q, base + list(gadget)) == [1] * len(p)
            positives += 1

    # No Boolean completion can exploit the interface exchange.
    for external in range(2):
        for internal in product(range(2), repeat=6):
            view = [internal[i] + internal[gp[i]] + internal[gq[i]] for i in range(6)]
            view[gadget_row - n] += external - internal[gadget_labels['H0']]
            assert (view == [1] * 6) == (external == 0 and internal in gadget_solutions)
    return positives, len(p)


if __name__ == '__main__':
    atoms = (1, -1, 2, -2)
    clauses = [()] + [(x,) for x in atoms] + list(product(atoms, repeat=2))
    suite = [()] + [(row,) for row in clauses] + list(combinations_with_replacement(clauses, 2))
    suite += [((1, -1, 2), (-2, 1, 1)), ((1, 1, 1), (-1, -1, -1)), ((), (1, 1, 1))]
    totals = [audit(raw, (2, 3, 4, 5)) for raw in suite]
    print(len(suite), 'guarded CNFs;', sum(s for s, n in totals), 'satisfying source assignments;',
          4 * len(suite), 'explicit cyclic lifts; maximum permutation size', max(n for s, n in totals))
