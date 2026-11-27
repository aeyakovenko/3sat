"""Exercise the DLMST transfer claims on small RAM traces and explicit CNFs."""
from itertools import combinations, permutations, product
from math import comb


def clauses_for_gate(left, right, result, function):
    clauses = []
    for a, b, c in product((0, 1), repeat=3):
        if c != function(a, b):
            # Exclude exactly this inconsistent input and gate assignment.
            clauses.append(tuple(-v if bit else v for v, bit in
                                 zip((left, right, result), (a, b, c))))
    return clauses


def satisfies(clauses, values):
    return all(any(values[abs(lit)-1] == int(lit > 0) for lit in clause)
               for clause in clauses)


def pinned_formula(bits):
    clauses = [(i if bit else -i,) for i, bit in enumerate(bits, 1)]
    last = len(bits)
    results = []
    for offset in range(0, len(bits), 4):
        a, b, c, d = range(offset + 1, offset + 5)
        clauses.extend(clauses_for_gate(a, b, last+1, int.__and__))
        clauses.extend(clauses_for_gate(c, d, last+2, int.__and__))
        clauses.extend(clauses_for_gate(last+1, last+2, last+3, int.__xor__))
        last += 3
        results.append(last)
    out = results[0]
    for nxt in results[1:]:
        clauses.extend(clauses_for_gate(out, nxt, last+1, int.__xor__))
        last += 1
        out = last
    clauses.append((out,))
    return clauses, last


def balanced_blocks():
    cases = assignments = 0
    for b in range(1, 4):
        accepted = 0
        for labels in product((False, True), repeat=b):
            bits = tuple(bit for label in labels
                         for bit in ((1, 1, 0, 0) if label else (1, 0, 1, 0)))
            assert bits.count(0) == bits.count(1) == 2*b
            clauses, n = pinned_formula(bits)
            assert all(1 <= len(c) <= 3 for c in clauses)
            models = sum(satisfies(clauses, bits + rest)
                         for rest in product((0, 1), repeat=n-len(bits)))
            assignments += 2**(n-len(bits))
            assert models == sum(labels) % 2
            cases += 1
            accepted += models
        assert accepted == 2**(b-1)
    return cases, assignments


def reply_budgets():
    sharp_cases = scripts = 0
    for q in (2, 3):
        for m in range(1, 7):
            for cap in range(m+1):
                histories = set()
                for k in range(cap+1):
                    for support in combinations(range(m), k):
                        for values in product(range(1, q), repeat=k):
                            mem = dict(zip(support, values))
                            histories.add(tuple(mem.get(i, 0) for i in range(m)))
                assert len(histories) == sum(comb(m, j)*(q-1)**j for j in range(cap+1))
                sharp_cases += 1
    # An adaptive next address determined only by the observed prefix.
    # Other events may perform arbitrary writes, independent of that schedule.
    actions = [None] + list(product(range(2), range(3)))
    for ops in product(actions, repeat=6):
        mem = [0, 0]
        observed = [0, 0]
        addr = 0
        replies = []
        marks = {}
        for op in ops:
            if op is not None:
                loc, value = op
                mem[loc] = value
                continue
            value = mem[addr]
            if value != observed[addr]:
                marks[len(replies)] = value
            replies.append(value)
            observed[addr] = value
            addr = (addr + value + len(replies)) % 2
        assert len(marks) <= sum(op is not None for op in ops)
        addr = 0
        seen = [0, 0]
        for i, expected in enumerate(replies):
            value = marks.get(i, seen[addr])
            assert value == expected
            seen[addr] = value
            addr = (addr + value + i+1) % 2
        scripts += 1
    return sharp_cases, scripts


def source_sets_and_fresh_inputs():
    fixed = list(combinations(range(2), 1)) + [(0, 1)]
    count = 0
    for sets in product(fixed, repeat=5):
        hist = {tuple(max(s, key=order.index) for s in sets)
                for order in permutations(range(2))}
        assert len(hist) <= 2
        count += 1
    writers = {0: 1, 1: 2}
    fresh = {tuple(writers[b] for b in word) for word in product((0, 1), repeat=10)}
    assert len(fresh) == 2**10
    return count, len(fresh)


def pin_relations():
    triples = list(product(range(2), repeat=3))
    signatures = set()
    checks = 0
    for mask in range(1 << len(triples)):
        formula = [(-(1+i), -(3+j), 5+k) for bit, (i,j,k) in enumerate(triples)
                   if mask & (1 << bit)]
        signature = []
        for bit, (i,j,k) in enumerate(triples):
            pinned = formula + [(1+i,), (3+j,), (-(5+k),)]
            has_model = any(satisfies(pinned, vals) for vals in product((0,1), repeat=6))
            assert has_model == (mask & (1 << bit) == 0)
            signature.append(has_model)
            checks += 1
        signatures.add(tuple(signature))
    assert len(signatures) == 2**len(triples)
    return checks, len(signatures)


if __name__ == "__main__":
    cases, assignments = balanced_blocks()
    print(f"{cases} balanced pinned 3-CNFs, {assignments} gate-table continuations")
    cases, scripts = reply_budgets()
    print(f"{cases} sharp write budgets, {scripts} address-adaptive scripts")
    fixed, fresh = source_sets_and_fresh_inputs()
    print(f"{fixed} fixed set families versus {fresh} fresh-input writer histories")
    checks, signatures = pin_relations()
    print(f"{checks} pinned satisfiability queries, {signatures} distinct signatures")
