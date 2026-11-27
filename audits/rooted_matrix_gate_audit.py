"""Decode a restricted matrix-verification circuit from local predecessor flags."""

from itertools import product


def build(d):
    gates = []

    def gate(op, *inputs):
        gates.append((op, inputs))
        return len(gates)-1

    for bank in "ABC":
        for i, j in product(range(d), repeat=2):
            gate(bank, i, j)
    at = lambda bank, i, j: "ABC".index(bank)*d*d+i*d+j
    result = None
    for j, i in product(range(d), repeat=2):
        terms = [gate("and", at("A", i, k), at("B", k, j)) for k in range(d)]
        dot = terms[0]
        for term in terms[1:]:
            dot = gate("xor", dot, term)
        eq = gate("eq", dot, at("C", i, j))
        result = eq if result is None else gate("and", result, eq)
    return gates


def apply(op, vals, full):
    a, b = vals
    if op == "and":
        return a & b
    if op == "xor":
        return a ^ b
    assert op == "eq"
    return full ^ (a ^ b)


def foreground(d, col):
    return {bank*d*d+i*d+col: sum(1 << a for a in range(1 << (2*d))
                                  if a >> (offset+i) & 1)
            for bank, offset in ((1, 0), (2, d)) for i in range(d)}


def evaluate(gates, matrix, d, col, x_public, ports, full):
    values = []
    for site, (op, args) in enumerate(gates):
        if site in ports:
            v = ports[site]
        elif op in "ABC":
            i, j = args
            if op == "A":
                bit = (matrix >> (i*d+j)) & 1
            elif op == "B":
                bit = (x_public[j] >> i) & 1
            else:
                row = (matrix >> (i*d)) & ((1 << d)-1)
                bit = (row & x_public[j]).bit_count() % 2
            v = full if bit else 0
        else:
            v = apply(op, [values[v] for v in args], full)
        values.append(v)
    return values


def local_code(gates, values, ports, full):
    code = []
    seen = set()

    def visit(site):
        if site in seen or site in ports:
            return
        seen.add(site)
        op, children = gates[site]
        assert op not in "ABC"
        for child in children:
            if values[child] == 0:
                code.append(0)
            elif values[child] == full:
                code.append(1)
            else:
                code.append(2)
                visit(child)

    visit(len(gates)-1)
    return tuple(code)


def decode(gates, code, ports, full):
    cache = dict(ports)
    tokens = iter(code)

    def visit(site):
        if site in cache:
            return cache[site]
        op, children = gates[site]
        assert op not in "ABC"
        inputs = []
        for child in children:
            trit = next(tokens)
            inputs.append(visit(child) if trit == 2 else (full if trit else 0))
        cache[site] = apply(op, inputs, full)
        return cache[site]

    result = visit(len(gates)-1)
    assert next(tokens, None) is None
    return result


def run(d):
    gates = build(d)
    full = (1 << (1 << (2*d)))-1
    tested = 0
    for col in range(d):
        ports = foreground(d, col)
        meanings = {}
        for a in range(1 << (d*d)):
            expected = sum(1 << (x+(y << d)) for x in range(1 << d)
                           for y in [sum((((a >> (i*d)) & x).bit_count() % 2) << i
                                         for i in range(d))])
            if d == 2:
                contexts = product(range(4), repeat=d-1)
            else:
                contexts = [(0, 0), ((a+col) % 8, (a//8+col+1) % 8)]
            for other in contexts:
                preset = list(other)
                preset.insert(col, 0)
                values = evaluate(gates, a, d, col, preset, ports, full)
                assert values[-1] == expected
                code = local_code(gates, values, ports, full)
                assert meanings.setdefault(code, a) == a
                assert decode(gates, code, ports, full) == expected
                tested += 1
    return tested


if __name__ == "__main__":
    print("column restrictions encoded and decoded:", run(2), run(3))
