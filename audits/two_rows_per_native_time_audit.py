"""Check the two-candidate implication graph and the two-store native NAND interpreter."""

from collections.abc import Callable
from itertools import product
from typing import NamedTuple


class Row(NamedTuple):
    before: int
    after: int
    kind: str
    address: int = 0
    payload: int = 0
    source: int = -1


def schedule(pins, gates):
    operations = []
    dummy = pins + len(gates) + 1
    for g, (left, right) in enumerate(gates, start=pins + 1):
        operations.extend([("load", right), ("not", 0), ("put", g), ("clear", 0),
                           ("load", left), ("mul", dummy - g), ("add", g),
                           ("put_one", 0), ("clear", 0)])
    operations.append(("load", pins + len(gates)))
    return operations


def execute(operations, assignment):
    registers = {i: (a, -1) for i, a in enumerate(assignment, start=1)}
    state = 0
    rows = []
    for t, (op, arg) in enumerate(operations):
        if op == "load":
            value, source = registers.get(arg, (0, -1))
            row = Row(state, value, "r", arg, value, source)
        elif op == "put" or op == "put_one":
            address, value = (arg, state) if op == "put" else (state, 1)
            registers[address] = (value, t)
            row = Row(state, state, "w", address, value)
        else:
            after = {"not": 1 - state, "clear": 0, "mul": arg * state, "add": arg + state}[op]
            row = Row(state, after, "a")
        rows.append(row)
        state = row.after
    return rows


def unary_ok(operations, assignment, verdict, t, row):
    if t == 0 and row.before != 0 or t + 1 == len(operations) and row.after != verdict:
        return False
    op, arg = operations[t]
    if op != "load":
        if op == "put" or op == "put_one":
            addr, val = (arg, row.before) if op == "put" else (row.before, 1)
            return row == Row(row.before, row.before, "w", addr, val)
        val = {"not": 1 - row.before, "clear": 0, "mul": arg * row.before,
               "add": arg + row.before}[op]
        return row == Row(row.before, val, "a")
    if row.kind != "r" or row.address != arg or row.payload != row.after:
        return False
    if row.source == -1:
        initial = assignment[arg - 1] if 1 <= arg <= len(assignment) else 0
        return row.payload == initial
    return 0 <= row.source < t


def compatible(i, first, j, second):
    assert i < j
    if i + 1 == j and first.after != second.before:
        return False
    if second.kind != "r":
        return True
    if i == second.source:
        return first.kind == "w" and first.address == second.address and first.payload == second.payload
    return not (i > second.source and first.kind == "w" and first.address == second.address)


def satisfying_two(menus, allowed: Callable):
    if any(not menu for menu in menus):
        return False
    options = [menu if len(menu) == 2 else menu * 2 for menu in menus]
    assert all(len(menu) == 2 for menu in options)
    graph = [set() for _ in range(2 * len(menus))]
    for i, menu in enumerate(options):
        for b, first in enumerate(menu):
            x = 2 * i + b
            if not allowed(i, first):
                graph[x].add(x ^ 1)
            for j in range(i + 1, len(options)):
                for c, second in enumerate(options[j]):
                    if not compatible(i, first, j, second):
                        y = 2 * j + c
                        graph[x].add(y ^ 1)
                        graph[y].add(x ^ 1)

    def reaches(start, goal):
        todo = [start]
        seen = {start}
        while todo:
            for to in graph[todo.pop()]:
                if to == goal:
                    return True
                if to not in seen:
                    seen.add(to)
                    todo.append(to)
        return False

    return not any(reaches(i, i ^ 1) and reaches(i ^ 1, i) for i in range(0, len(graph), 2))


def main():
    cases = menus_checked = third_sites = 0
    for left, right in product((1, 2), repeat=2):
        for u, v in product((1, 2, 3), repeat=2):
            gates = [(left, right), (u, v)]
            ops = schedule(2, gates)
            traces = {bits: execute(ops, bits) for bits in product((0, 1), repeat=2)}
            menus = [sorted({run[t] for run in traces.values()}) for t in range(len(ops))]
            for menu in menus:
                assert len({row._replace(source=-1) for row in menu}) <= 2
                assert len(menu) <= 3
                third_sites += int(len(menu) == 3)
            for bits, trace in traces.items():
                values = [0, *bits]
                for a, b in gates:
                    values.append(1 - (values[a] & values[b]))
                assert trace[-1].after == values[-1]
                for skip in range(3):
                    pair = [list(menu) if len(menu) < 3 else [row for k, row in enumerate(menu) if k != skip]
                            for menu in menus]
                    covered = all(row in menu for row, menu in zip(trace, pair, strict=True))
                    for verdict in (0, 1):
                        def allowed(t, row, ops=ops, bits=bits, verdict=verdict):
                            return unary_ok(ops, bits, verdict, t, row)

                        assert satisfying_two(pair, allowed) == (covered and values[-1] == verdict)
                        menus_checked += 1
                cases += 1
    assert third_sites > 0
    print(f"{cases} native NAND computations, {menus_checked} implicit 2-SAT verdicts,"
          f" {third_sites} time/circuit pairs needing three augmented rows across assignments")


if __name__ == "__main__":
    main()
