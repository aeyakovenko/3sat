#!/usr/bin/env python3
"""Synthesize recurrent schedules for a fixed native_gate_lift.py instance.

Input JSON has the original gate/automaton fields; the original schedule is
ignored. An optional alphabet array selects named matrix layers (default:
all named layers). --all-width-one supplies every possible one-dimensional
layer instead. --candidate prints the complete found instance for piping to
native_gate_lift.py. A cap gives UNKNOWN if it omits work needed for a negative
decision. A FOUND answer always includes verification of the entire progression.

For one common layer word, a node stores the set of Folded states reached by
all timestamp words of that length. The next layer acts on the whole set before
another layer is selected, so the synthesis cannot choose a matrix separately
for each timestamp. At lengths below the uniform arithmetic threshold we retain
the states, saturate a length counter, and ignore acceptance. Omitting finitely
many accepting lengths preserves recurrence. For all later lengths a node
accepts exactly if all of its states pass the native local tests. The graph is
finite. Its accepted language is infinite iff a reachable directed cycle has
a path to an accepting node. The suffix after the cycle may be indispensable.

This is an exhaustive search over the specified width, boundary vectors and
layer alphabet. The timestamp set and the graph of such sets can both be large.
"""

import argparse
from itertools import product
from collections import deque
import json
import sys

from native_gate_lift import Folded, Instance, check, example, polynomial


class FiberCap(Exception):
    pass


def alphabet(data, all_one, max_letters):
    p = dict(data)
    if all_one:
        if p["width"] != 1 or p["blocks"] < 1:
            raise ValueError("--all-width-one requires width 1 and positive blocks")
        size = 1 << p["blocks"]
        total = 1 << size
        count = min(total, max_letters) if max_letters is not None else total
        p["layers"] = {"w1_%x" % bits: [[(bits >> i) & 1] for i in range(size)]
                       for bits in range(count)}
        letters = tuple(p["layers"])
    else:
        names = tuple(dict.fromkeys(p.get("alphabet", p["layers"])))
        if not names or any(k not in p["layers"] for k in names):
            raise ValueError("the alphabet must contain known layer names")
        total = len(names)
        letters = names[:max_letters]
    p.update(prefix=[], loop=[letters[0]], suffix=[])
    return p, letters, total


def advance(machine, states, letter, limit):
    nxt = set()
    for state in states:
        for symbol in range(machine.p.mask + 1):
            nxt.add(machine.step(state, letter, symbol))
            if limit is not None and len(nxt) > limit:
                raise FiberCap
    return frozenset(nxt)


def find_cycle(edges, parents, accepting):
    # Keep exactly the nodes with a known path to acceptance. Build a suffix
    # tree at the same time, including acceptance outside the eventual cycle.
    incoming = [[] for _ in edges]
    for u, terms in enumerate(edges):
        for letter, v in terms:
            incoming[v].append((letter, u))
    suffix = {u: None for u in accepting}
    pending = deque(accepting)
    while pending:
        v = pending.popleft()
        for letter, u in incoming[v]:
            if u not in suffix:
                suffix[u] = (letter, v)
                pending.append(u)

    # Drop dead ends repeatedly. All remaining nodes can reach a cycle
    # entirely inside the coaccessible subgraph. Parallel edges count twice.
    degree = {u: sum(v in suffix for _, v in edges[u]) for u in suffix}
    pending = deque(u for u in degree if degree[u] == 0)
    while pending:
        v = pending.popleft()
        for _, u in incoming[v]:
            if u in degree:
                degree[u] -= 1
                if degree[u] == 0:
                    pending.append(u)
    live = {u for u in degree if degree[u] > 0}
    if not live:
        return None

    u = min(live)
    where, path = {}, []
    while u not in where:
        where[u] = len(path)
        letter, v = next((label, target) for label, target in edges[u] if target in live)
        path.append(letter)
        u = v
    anchor = u
    loop = path[where[u]:]
    prefix = []
    while parents[u] is not None:
        u, label = parents[u]
        prefix.append(label)
    tail = []
    u = anchor
    while suffix[u] is not None:
        label, u = suffix[u]
        tail.append(label)
    return {"prefix": prefix[::-1], "loop": loop, "suffix": tail}


def synthesize(data, *, all_one=False, max_nodes=None, max_fiber=None, max_letters=None):
    if any(x is not None and x < 1 for x in (max_nodes, max_fiber, max_letters)):
        raise ValueError("caps must be positive")
    cfg, letters, total = alphabet(data, all_one, max_letters)
    p = Instance(cfg)
    geometry = p.geometry(p.safe_h)
    if geometry:
        return {"status": "NO_RECURRENT_SCHEDULE", "eventual_invalid_geometry": geometry}, None
    machine = Folded(p)
    first = (0, frozenset({machine.initial}))
    nodes, ids = [first], {first: 0}
    parents, edges = [None], [[]]
    accepting = []
    omitted = set()
    if len(letters) < total:
        omitted.add("letters")
    peak = 1
    for u, (h, states) in enumerate(nodes):  # appended nodes are subsequently visited
        if h == p.safe_h and all(machine.violation(s) is None for s in states):
            accepting.append(u)
        for letter in letters:
            try:
                members = advance(machine, states, letter, max_fiber)
            except FiberCap:
                omitted.add("fiber")
                continue
            peak = max(peak, len(members))
            target = min(h + 1, p.safe_h), members
            v = ids.get(target)
            if v is None:
                if max_nodes is not None and len(nodes) >= max_nodes:
                    omitted.add("nodes")
                    continue
                v = len(nodes)
                ids[target] = v
                nodes.append(target)
                parents.append((u, letter))
                edges.append([])
            edges[u].append((letter, v))

    schedule = find_cycle(edges, parents, accepting)
    result = {"nodes": len(nodes), "max_completed_fiber": peak, "accepting_nodes": len(accepting),
              "letters_searched": len(letters), "alphabet_size": total,
              "saturation_length": p.safe_h}
    if omitted:
        result["truncated_by"] = sorted(omitted)
    if schedule is None:
        result["status"] = "UNKNOWN" if omitted else "NO_RECURRENT_SCHEDULE"
        return result, None
    cand = dict(cfg, **schedule)
    cand.pop("alphabet", None)
    result.update(status="FOUND", schedule=schedule, verified=check(cand))
    if not result["verified"]["valid"]:
        raise AssertionError("synthesized schedule failed the all-width checker")
    return result, cand


def elementary(layers, sink, start=1):
    width = len(next(iter(layers.values()))[0])
    return {"blocks": 1, "width": width, "start": start, "layers": layers,
            "gates": [dict(name="z", inputs=[], table="0", pins=[sink, 0])],
            "terminal": dict(gate="z", value=0, horizon=[])}


def signed_sat(sign, adaptive=False):
    """Compile explicit truth-table SAT on a four-variable proper DIMACS file.

    Seven clauses force three anchors false. Two more force x and test one
    supplied sign of x. For each possible assignment one gate reads the sign
    and tests the actual clauses. Their OR computes the SAT decision. In the
    width-two calibration a row can select correct local pins for either sign
    with identical boundary masks in both instances. In width one the internal
    pins are the truthful bits for that instance. In both cases the terminal
    asserts YES, including on the negative file.
    """
    anchors = [tuple(-i if (bits >> (i - 1)) & 1 else i for i in range(1, 4))
               for bits in range(1, 8)]

    def serialize(s):
        rows = anchors + [(4, 1, 2), (4 if s else -4, 1, 3)]
        return b"p cnf 4 9\n" + b"".join(b"%d %d %d 0\n" % row for row in rows)

    def parse(raw):
        lines = raw.splitlines()
        assert lines[0] == b"p cnf 4 9" and len(lines) == 10
        rows = []
        for line in lines[1:]:
            x, y, z, end = map(int, line.split())
            assert end == 0 and len({abs(x), abs(y), abs(z)}) == 3
            rows.append((x, y, z))
        assert len(set(rows)) == 9
        return rows

    files = [parse(serialize(s)) for s in (0, 1)]
    def true_on(s, bits):
        return all(any(bool(bits & (1 << (abs(k) - 1))) == (k > 0) for k in clause)
                   for clause in files[s])

    gates = []
    def gate(name, parents, table, values):
        choices = values if adaptive else [values[sign]]
        pins = [sum(1 << j for j, v in enumerate(choices) if v == b) for b in (0, 1)]
        gates.append(dict(name=name, inputs=[[v, 0, 0] for v in parents], table=table, pins=pins))
        return (name, values)

    gate("sign", [], str(sign), [False, True])
    layer = []
    for bits in range(16):
        values = [true_on(s, bits) for s in (0, 1)]
        layer.append(gate("assignment_%d" % bits, ["sign"], "".join(str(int(v)) for v in values), values))
    serial = 0
    while len(layer) > 1:
        nxt = []
        for a, b in zip(layer[::2], layer[1::2]):
            serial += 1
            values = [v or w for v, w in zip(a[1], b[1])]
            nxt.append(gate("or_%d" % serial, [a[0], b[0]], "0111", values))
        layer = nxt
    gates[-1]["pins"] = [0, 3 if adaptive else 1]
    layers = ({"select0": [[1, 1], [1, 1]], "select1": [[2, 2], [2, 2]]}
              if adaptive else {"unused": [[0], [0]]})
    return {"blocks": 1, "width": 2 if adaptive else 1, "start": 1, "layers": layers,
            "gates": gates, "terminal": dict(gate=layer[0][0], value=1, horizon=[-1, 1])}


def scalar_samples(cand, count):
    p = Instance(cand)
    total = 0
    for r in range(count):
        schedule = p.prefix + p.loop * r + p.suffix
        assert p.geometry(len(schedule)) is None
        for t in range(polynomial(p.horizon, 1 << len(schedule)) + 1):
            assert p.scalar_at(schedule, t) is None
            total += 1
    return total


def self_test():
    scalar = 0
    shifted = example()
    res, found = synthesize(shifted)
    assert res["status"] == "FOUND" and res["max_completed_fiber"] > 1
    scalar += scalar_samples(found, 3)
    shifted["gates"][0]["seeds"] = []
    assert synthesize(shifted)[0]["status"] == "NO_RECURRENT_SCHEDULE"

    idle = [1, 4, 4]
    finish = [2, 4, 4]
    special = elementary({"idle": [idle, idle], "finish": [finish, finish]}, 2)
    res, found = synthesize(special)
    assert res["status"] == "FOUND" and res["schedule"]["suffix"][-1] == "finish"
    scalar += scalar_samples(found, 5)
    special["alphabet"] = ["finish"]
    assert synthesize(special)[0]["status"] == "NO_RECURRENT_SCHEDULE"

    toggle = elementary({"flip": [[2, 1], [2, 1]]}, 1)
    res, found = synthesize(toggle)
    assert res["status"] == "FOUND" and len(res["schedule"]["loop"]) == 2
    scalar += scalar_samples(found, 5)

    finite = elementary({"once": [[2, 0], [2, 0]]}, 2)
    p = Instance(dict(finite, prefix=[], loop=["once"], suffix=[]))
    assert p.scalar_at(("once",), 0) is None and p.scalar_at(("once", "once"), 0)
    assert synthesize(finite)[0]["status"] == "NO_RECURRENT_SCHEDULE"
    assert synthesize(toggle, max_nodes=1)[0]["status"] == "UNKNOWN"
    assert synthesize(toggle, max_fiber=1)[0]["status"] == "UNKNOWN"

    for s in (0, 1):
        res, found = synthesize(signed_sat(s), all_one=True)
        assert res["alphabet_size"] == 4
        assert res["status"] == ("FOUND" if s else "NO_RECURRENT_SCHEDULE")
        if s:
            scalar += scalar_samples(found, 4)
        print("four-variable SAT sign=%d: %s, %d reachable schedule nodes" %
              (s, res["status"], res["nodes"]))
    assert synthesize(signed_sat(1), all_one=True, max_letters=1)[0]["status"] == "UNKNOWN"

    paired = [signed_sat(s, adaptive=True) for s in (0, 1)]
    assert [g["pins"] for g in paired[0]["gates"]] == [g["pins"] for g in paired[1]["gates"]]
    assert paired[0]["gates"][1:] == paired[1]["gates"][1:]
    languages = []
    for sign, sample in enumerate(paired):
        res, found = synthesize(sample)
        assert res["status"] == ("FOUND" if sign else "NO_RECURRENT_SCHEDULE")
        if sign:
            scalar += scalar_samples(found, 4)
        p = Instance(dict(sample, prefix=[], loop=["select0"], suffix=[]))
        machine = Folded(p)
        checked_words = 0
        for h in range(p.safe_h, p.safe_h + 2):
            for word in product(p.layers, repeat=h):
                states = frozenset({machine.initial})
                for letter in word:
                    states = advance(machine, states, letter, None)
                passes = all(machine.violation(state) is None for state in states)
                expected = all(p.scalar_at(word, t) is None for t in range(1 << h))
                assert passes == expected == (sign == 1 and word[-1] == "select1")
                checked_words += 1
        languages.append(checked_words)
    print(f"Fixed boundaries, either sign admissible internally: exact/direct checks on {sum(languages)} schedules")
    print("PASS: required suffix, period two, transient acceptance, caps, exhaustive width-one "
          "layers; %d direct scalar timestamp checks" % scalar)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instance", nargs="?", help="JSON path or - for standard input")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--sat-example", type=int, choices=(0, 1), help="print a named-layer SAT example")
    parser.add_argument("--all-width-one", action="store_true")
    parser.add_argument("--max-nodes", type=int)
    parser.add_argument("--max-fiber", type=int)
    parser.add_argument("--max-letters", type=int)
    parser.add_argument("--candidate", action="store_true", help="on success print complete checker input")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    elif args.sat_example is not None:
        sample = signed_sat(args.sat_example)
        sample["layers"] = {"zero": [[0], [0]], "lsb0": [[1], [0]],
                            "lsb1": [[0], [1]], "one": [[1], [1]]}
        print(json.dumps(sample))
    elif args.instance:
        with (sys.stdin if args.instance == "-" else open(args.instance)) as file:
            result, candidate = synthesize(json.load(file), all_one=args.all_width_one, max_nodes=args.max_nodes,
                                           max_fiber=args.max_fiber, max_letters=args.max_letters)
        print(json.dumps(candidate if args.candidate and candidate is not None else result))
        sys.exit({"FOUND": 0, "NO_RECURRENT_SCHEDULE": 1, "UNKNOWN": 2}[result["status"]])
    else:
        parser.error("supply an instance, --sat-example, or --self-test")
