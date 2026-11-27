"""Finite checks of the balanced-relation probe constructions, using no dependencies."""

from collections import defaultdict
from itertools import product
from math import prod
from random import Random


def synchronize(components, actions):
    states = list(product(*(range(len(comp)) for comp in components)))
    edges = []
    for state in states:
        for letter, (kind, tag) in actions.items():
            dest = tuple(comp[q].get(letter) for comp, q in zip(components, state))
            if None not in dest:
                edges.append((kind, tag, state, dest))
    return states, edges


def violations(states, edges, rel):
    bad = set()
    followers = defaultdict(list)
    for a, b in rel:
        followers[a].append(b)
    for a in states:
        if (a, a) not in rel:
            bad.add(("diag", a))
    for a, b in rel:
        for c in followers[b]:
            if (a, c) not in rel:
                bad.add(("join", a, b, c))
    pops = defaultdict(list)
    for kind, tag, a, b in edges:
        if kind == "neutral" and (a, b) not in rel:
            bad.add(("neutral", a, b))
        if kind == "pop":
            pops[(tag, a)].append(b)
    for kind, tag, a, b in edges:
        if kind != "push":
            continue
        for c in followers[b]:
            for d in pops[tag, c]:
                if (a, d) not in rel:
                    bad.add(("wrap", tag, a, b, c, d))
    return bad


def check_cycles(ps, qs):
    components = []
    for p, q in zip(ps, qs):
        comp = [{"a": (i + 1) % p} for i in range(p)]
        comp[p - 1]["#"] = p
        comp += [{"b": p + (j + 1) % q} for j in range(q)]
        components.append(comp)
    states, edges = synchronize(
        components, {"a": ("push", 0), "b": ("pop", 0), "#": ("neutral", 0)}
    )
    count = prod(ps) * prod(qs)
    facts = [
        (tuple((p - 1 - t) % p for p in ps), tuple(p + t % q for p, q in zip(ps, qs)))
        for t in range(count)
    ]
    assert len(set(facts)) == count
    rel = {(q, q) for q in states}
    for j, (a, d) in enumerate(facts):
        expected = (("wrap", 0, a, *facts[j - 1], d) if j else ("neutral", a, d))
        assert violations(states, edges, rel) == {expected}
        rel.add((a, d))
    assert not violations(states, edges, rel)
    return count


def search_defect(bits):
    lo, hi = -1, len(bits) - 1
    assert not bits[hi]
    queries = 0
    while hi - lo > 1:
        middle = (lo + hi) // 2
        queries += 1
        if bits[middle]:
            lo = middle
        else:
            hi = middle
    assert not bits[hi] and (hi == 0 or bits[hi - 1])
    return queries


def grid_component(p, owner):
    phases = 3 if owner else 1
    comp = [{} for _ in range(phases * p * p)]
    for phase, t, j in product(range(phases), range(p), range(p)):
        row = comp[(phase * p + t) * p + j]
        for letter, before, after, dt, dj in (
            ("a", 0, 0, -1, 0), ("A", 2, 1, 1, 0),
            ("b", 1, 0, -1, 1), ("B", 2, 2, 1, -1), ("#", 0, 2, 0, 0),
        ):
            if owner and phase != before or letter == "#" and t != 0:
                continue
            dest_phase = after if owner else 0
            row[letter] = (dest_phase * p + (t + dt) % p) * p + (j + dj) % p
    return comp


def check_pyramid(moduli, exhaustive):
    H = prod(moduli)
    components = [grid_component(p, i == 0) for i, p in enumerate(moduli)]
    actions = {"a": ("push", 0), "A": ("pop", 0), "b": ("push", 1),
               "B": ("pop", 1), "#": ("neutral", 0)}
    states, edges = synchronize(components, actions)

    def encode(phase, t, j):
        return tuple(((phase if i == 0 else 0) * p + t % p) * p + j % p
                     for i, p in enumerate(moduli))

    cone = [(t, j) for t in range(H) for j in range(H - t)]
    # The sink is the last entry in this encoding.
    n_free = len(cone) - 1
    random = Random(42)
    masks = range(1 << n_free) if exhaustive else [
        0, (1 << n_free) - 1, *(random.getrandbits(n_free) for _ in range(64))
    ]
    for mask in masks:
        labels = {v: bool(mask & (1 << i)) for i, v in enumerate(cone)}
        assert not labels[H - 1, 0]
        rel = {(q, q) for q in states}
        expected = set()
        for t, j in product(range(H), repeat=2):
            l, m, r = (encode(stage, t, j) for stage in range(3))
            value = labels.get((t, j), True)
            first = labels.get(((t - 1) % H, j), True)
            second = labels.get(((t - 1) % H, (j + 1) % H), True)
            if value:
                rel.add((l, r))
            if first:
                rel.add((l, m))
            if second:
                rel.add((m, r))
            if not value:
                if t == 0:
                    expected.add(("neutral", l, r))
                if first and second:
                    expected.add(("join", l, m, r))
        assert expected and violations(states, edges, rel) == expected
    return len(masks)


if __name__ == "__main__":
    cuts = sum(check_cycles(*pair) for pair in [([2], [3]), ([2, 3], [5, 7])])
    words = 0
    for length in range(1, 13):
        for prefix in product((False, True), repeat=length - 1):
            assert search_defect(prefix + (False,)) <= (length - 1).bit_length()
            words += 1
    labels = sum(check_pyramid(mods, full) for mods, full in [
        ([2], True), ([3], True), ([4], True), ([2, 3], False)
    ])
    print(f"{cuts} cyclic thresholds, {words} root-excluding bit strings, "
          f"{labels} labelled pyramids passed")
