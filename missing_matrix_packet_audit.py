"""Check signed 2-by-2 products with each kind of genuine final DIMACS packet."""
from collections import Counter
from itertools import product
from random import Random

from late_clause_replay_audit import Layout
from table_probe_context_audit import satisfiable


def table_gate(clauses, inputs, output, operation):
    for values in product((0, 1), repeat=len(inputs)):
        guards = tuple(-v if bit else v for v, bit in zip(inputs, values))
        clauses.append(guards + (output if operation(*values) else -output,))


def make_family():
    signed_rows = ((12, 13), (22, 23))
    occupied = {v for pair in signed_rows for v in pair}
    fresh = (j for j in range(1, 100) if j not in occupied)
    row, col, parity = (next(fresh) for _ in range(3))
    cols = (next(fresh), next(fresh))
    values = tuple(next(fresh) for _ in range(4))
    bits = (next(fresh), next(fresh))
    fixed = []
    for k in range(4):
        selector = row if k < 2 else col
        for z in range(4):
            table_gate(fixed, (selector, values[k]), mask_name(k, z),
                       lambda lane, value: value == (z >> lane & 1))
    for h in range(2):
        table_gate(fixed, (values[h], values[h+2]), bits[h], lambda a, b: a & b)
    table_gate(fixed, bits, parity, lambda a, b: a ^ b)
    for i, pair in enumerate(signed_rows):
        for e, flag in enumerate(pair):
            table_gate(fixed, (row, parity), flag, lambda a, v: (i, e) == (a, v))
        table_gate(fixed, (col,), cols[i], lambda a: a == i)
    layout = Layout(r=2, count=len(fixed) + 5, bits=1 << 18, variables=411)
    anchors = layout.anchors
    def pad(c):
        return c + tuple(a for a in anchors if a not in map(abs, c))[:3-len(c)]
    static = tuple(layout.packet([pad(c)]) for c in fixed)
    rev_pad = tuple(-a for a in reversed(anchors))
    dynamic = {(k, z): layout.packet([pad((mask_name(k, z),)), rev_pad])
               for k in range(4) for z in range(4)}
    queries = {(i, j, tag): layout.pins((signed_rows[i][tag], cols[j]))
               for i, j, tag in product(range(2), repeat=3)}
    return layout, static, dynamic, queries


def mask_name(k, z):
    return int(f'{k+1}{z & 1}{z >> 1}')


def dot(masks, i, j):
    return ((masks[0] >> i & 1) & (masks[2] >> j & 1)) ^ (
        (masks[1] >> i & 1) & (masks[3] >> j & 1))


def freeze(prefix, fixed, dyn, queries):
    """Return a reply table for legal last words, including every compatible mask."""
    count = Counter(fixed)
    masks = {}
    query = None
    for word in prefix:
        if count[word]:
            count[word] -= 1
        elif word in dyn:
            k, val = dyn[word]
            assert k not in masks
            masks[k] = val
        else:
            assert query is None
            query = queries[word]
    if query is None:
        assert len(masks) == 4 and sum(count.values()) == 0
        return {word: dot(masks, i, j) == tag for word, (i, j, tag) in queries.items()}
    i, j, tag = query
    if len(masks) == 4:
        missing, = list(count.elements())
        return {missing: dot(masks, i, j) == tag}
    assert len(masks) == 3 and sum(count.values()) == 0
    absent, = set(range(4)) - masks.keys()
    masks[absent] = 0
    known = dot(masks, i, j)
    if absent < 2:
        lane, coefficient = i, masks[absent+2] >> j & 1
    else:
        lane, coefficient = j, masks[absent-2] >> i & 1
    return {w: known ^ ((z >> lane & 1) & coefficient) == tag
            for w, (k, z) in dyn.items() if k == absent}


def parse(data):
    header, rest = data.split(b'\n', 1)
    _, _, bound, count = header.split()
    tokens = list(map(int, rest.split()))
    assert len(tokens) == 4*int(count) and not any(tokens[3::4])
    rows = [tuple(tokens[i:i+3]) for i in range(0, len(tokens), 4)]
    assert all(len({abs(lit) for lit in c}) == 3
               and all(1 <= abs(lit) <= int(bound) for lit in c) for c in rows)
    return rows


def main():
    rng = Random(19003)
    layout, fixed, dynamic, query = make_family()
    reverse_dynamic = {w: k for k, w in dynamic.items()}
    reverse_query = {w: q for q, w in query.items()}
    files = data_replies = query_replies = fixed_replies = 0
    for factors in product(range(4), repeat=4):
        chunks = [dynamic[k, z] for k, z in enumerate(factors)]
        replies = freeze([*fixed, *chunks], fixed, reverse_dynamic, reverse_query)
        assert all(replies[w] == (dot(factors, i, j) == e) for (i, j, e), w in query.items())
        query_replies += len(replies)
        for (i, j, tag), word in query.items():
            baseline_expected = dot(factors, i, j) == tag
            packets = [*fixed, *chunks, word]
            rng.shuffle(packets)
            # Parsing the proper file gives an independent SAT decision with
            # no access to factor labels, query type, or the withheld packet.
            assert satisfiable(parse(layout.file(packets))) == baseline_expected
            files += 1
            for h in range(4):
                replies = freeze([w for w in packets if w != chunks[h]],
                                 fixed, reverse_dynamic, reverse_query)
                for z in range(4):
                    changed = list(factors)
                    changed[h] = z
                    assert replies[dynamic[h, z]] == (dot(changed, i, j) == tag)
                    data_replies += 1
            # Sweep all fixed positions once per signed coordinate, and one
            # pseudorandom fixed position for every other product.
            keep = range(len(fixed)) if factors == (0, 1, 2, 3) else [rng.randrange(len(fixed))]
            for h in keep:
                prefix = packets.copy()
                prefix.remove(fixed[h])
                assert freeze(prefix, fixed, reverse_dynamic, reverse_query) == {
                    fixed[h]: baseline_expected}
                fixed_replies += 1
        for i, j in product(range(2), repeat=2):
            assert (query[i, j, 0] ^ query[i, j, 1]).bit_count() == 1
    print(f'{files} shuffled proper DIMACS verdicts, {query_replies} missing-query '
          f'replies, {data_replies} missing-data replies, {fixed_replies} fixed-clause replies')


if __name__ == '__main__':
    main()
