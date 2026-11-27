"""Check adaptive bit-query charts against grounded native rule violations.

A reader is a deterministic binary decision tree on two h-bit arguments.
Each native rule contains at most four atoms. The symbolic validator tries
only answer transcripts, glues all repeated bit queries, and checks each
surviving tuple cylinder with a fixed-state digit automaton. With at most b
probes per reader this costs at most 2^(4b) times a polynomial in h and b.
The small reference checker enumerates native times and addresses independently.
"""

from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass(frozen=True)
class Rule:
    label: str
    atoms: tuple
    step: bool = False
    unequal: bool = False


def rules(h):
    load = ("load", "t", 0, True)
    store = ("store", "t", 0, True)
    ptr = ("ptr", "t", "a", True)
    yield Rule("initial site register", (("ptr", 0, "y", False),))
    yield Rule("initial memory", (("mem0", 0, "x", False),))
    yield Rule("initial instruction", (("load", 0, 0, False),))
    yield Rule("final quietness", (("ret", (1 << h) - 1, 0, True),))
    yield Rule("STORE1", (store, ptr, ("mem1", "u", "a", False)), True)
    for bit in (0, 1):
        mem = f"mem{bit}"
        yield Rule(f"LOAD {bit}", (load, ptr, (mem, "t", "a", True),
                                   ("dest", "u", bit, False)), True)
        yield Rule(f"STORE frame {bit}", (store, ptr, (mem, "t", "x", True),
                                          (mem, "u", "x", False)), True, True)


def read(tree, h, time, value):
    while not isinstance(tree, bool):
        index, zero, one = tree
        source = time if index < h else value
        tree = one if (source >> (index % h)) & 1 else zero
    return tree


def digit_feasible(h, pins, step, unequal):
    # The remaining site field has only individual bit pins. Their mutual
    # consistency is checked when they are inserted into the same mapping.
    states = {(int(step), False)}
    for k in range(h):
        digits = tuple((pins[field, k],) if (field, k) in pins else (0, 1)
                       for field in ("t", "u", "a", "x"))
        next_states = set()
        for t, u, a, x in product(*digits):
            for carry, distinct in states:
                if step and (t + carry) % 2 != u:
                    continue
                next_states.add(((t + carry) // 2 if step else 0,
                                 distinct or (unequal and a != x)))
        states = next_states
    return (0, unequal) in states


def transcripts(tree, h, words, expected, pins):
    if isinstance(tree, bool):
        if tree == expected:
            yield pins
        return
    index, *branches = tree
    word = words[index // h]
    k = index % h
    if isinstance(word, int):
        yield from transcripts(branches[(word >> k) & 1], h, words, expected, pins)
    elif (word, k) in pins:
        yield from transcripts(branches[pins[word, k]], h, words, expected, pins)
    else:
        for bit, child in enumerate(branches):
            extra = pins.copy()
            extra[word, k] = bit
            yield from transcripts(child, h, words, expected, extra)


def symbolic_fault(rule, h, chart, site):
    initial = {("y", k): (site >> k) & 1 for k in range(h)}

    def search(i, pins):
        if i == len(rule.atoms):
            return digit_feasible(h, pins, rule.step, rule.unequal)
        tag, time, value, wanted = rule.atoms[i]
        return any(search(i + 1, extra)
                   for extra in transcripts(chart[tag], h, (time, value), wanted, pins))

    return search(0, initial)


def grounded_fault(rule, h, chart, site):
    words = range(1 << h)
    fields = {field for _, t, v, _ in rule.atoms for field in (t, v)}
    for t in (range((1 << h) - 1) if rule.step else
              words if "t" in fields else (0,)):
        for a in (words if "a" in fields else (0,)):
            for x in (words if "x" in fields else (0,)):
                if rule.unequal and x == a:
                    continue
                vals = {"t": t, "u": t + 1, "a": a, "x": x, "y": site}
                if all(read(chart[tag], h, vals.get(ti, ti), vals.get(vi, vi)) == wanted
                       for tag, ti, vi, wanted in rule.atoms):
                    return True
    return False


TAGS = ("load", "store", "ptr", "mem0", "mem1", "dest", "ret")


def charts(h):
    broad = dict.fromkeys(TAGS, True)
    broad["ret"] = False
    yield broad
    for bit in (False, True):
        # Permit pointer values whose most significant bit equals bit.
        yield broad | {"ptr": (2 * h - 1, not bit, bit)}
    yield broad | {"mem1": False}
    yield broad | {"dest": (h, False, True)}
    rng = Random(901 + h)

    def tree(depth):
        if not depth or rng.randrange(7) == 0:
            return bool(rng.randrange(2))
        return rng.randrange(2 * h), tree(depth - 1), tree(depth - 1)

    for depth in (1, 2, 3):
        for _ in range(6):
            yield {tag: tree(depth) for tag in TAGS}


def audit():
    grounded_checks = prefix_checks = valid_pairs = 0
    for h in (2, 3, 4):
        candidates = list(charts(h))
        all_rules = tuple(rules(h))
        valid, certified = {}, {}
        for i, chart in enumerate(candidates):
            for y in range(1 << h):
                outcomes, certified_outcomes = [], []
                for rule in all_rules:
                    expected = grounded_fault(rule, h, chart, y)
                    found = symbolic_fault(rule, h, chart, y)
                    assert found == expected
                    grounded_checks += 1
                    outcomes.append(expected)
                    certified_outcomes.append(found)
                valid[i, y] = not any(outcomes)
                certified[i, y] = not any(certified_outcomes)
                valid_pairs += valid[i, y]
        # The outer existence check may choose one site and one description.
        # Every rule must pass for that very pair. This small audit exhausts
        # the finite family of candidate descriptions only at this outer step.
        for prefix, omitted in product(("", "0", "1", "00", "01", "10", "11"),
                                       (None, ("ptr", 0, 0), ("ptr", 0, (1 << h) - 1),
                                        ("ret", 0, 0), ("load", 0, 0))):
            direct, symbolic = set(), set()
            for i, chart in enumerate(candidates):
                for y in range(1 << h):
                    if valid[i, y] and format(y, f"0{h}b").startswith(prefix):
                        if omitted is None or not read(chart[omitted[0]], h, *omitted[1:]):
                            direct.add((i, y))
                    compatible = all((y >> (h - 1 - j)) & 1 == int(bit)
                                     for j, bit in enumerate(prefix))
                    if certified[i, y] and compatible:
                        if omitted is None or not symbolic_fault(
                                Rule("omission", ((*omitted, True),)), h, chart, y):
                            symbolic.add((i, y))
            assert direct == symbolic
            if prefix in ("0", "1") and omitted is None:
                wanted = 1 + int(prefix)
                assert all((wanted, y) in direct for y in range(1 << h)
                           if format(y, f"0{h}b").startswith(prefix))
                assert all(i != 3 - wanted for i, _ in direct)
            if omitted == ("load", 0, 0):
                assert not direct
            if omitted == ("ptr", 0, 0) and prefix in ("0", "1"):
                assert any(i == 2 for i, _ in direct) == (prefix == "1")
            prefix_checks += 1

        # An inconsistent leaf within one reader and across two independent
        # reader runs would both be admitted by unconstrained transcript guesses.
        repeated = (0, (0, False, True), False)
        assert not symbolic_fault(Rule("repeat", (("ptr", "t", 0, True),)),
                                  h, {"ptr": repeated}, 0)
        opposite = {"left": (0, True, False), "right": (0, False, True)}
        both = Rule("shared", (("left", "t", 0, True), ("right", "t", 0, True)))
        assert not symbolic_fault(both, h, opposite, 0)
        wrap = {(field, k): bit for field, bit in (("t", 1), ("u", 0)) for k in range(h)}
        assert not digit_feasible(h, wrap, True, False)
        equal = {(field, k): k % 2 for field in ("a", "x") for k in range(h)}
        assert not digit_feasible(h, equal, False, True)
        equal["x", h - 1] ^= 1
        assert digit_feasible(h, equal, False, True)
    print(f"{grounded_checks} native rule checks matched grounding; {valid_pairs} valid site/chart pairs")
    print(f"{prefix_checks} prefix and omission queries matched; adaptive reads of depth through 3")
    print("Repeated-bit, shared-bit, final carry and STORE alias controls passed at h=2,3,4")


if __name__ == "__main__":
    audit()
