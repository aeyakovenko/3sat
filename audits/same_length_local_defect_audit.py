"""Exact-byte proper DIMACS self-reduction and label-free retirement, finite audit."""

from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from random import Random


# A row forbids one valuation of (1,2,3). Leave both choices of the third bit.
PINS = tuple(tuple(-i if bit else i for i, bit in enumerate(bits, 1))
             for bits in product((0, 1), repeat=3) if any(bits[:2]))
CUT = 8


def natural(token):
    if not token.isdigit():
        raise ValueError(token)
    return int(token)


@lru_cache(None)
def parse(data):
    lines = [line for line in data.splitlines() if line.strip()
             and not line.lstrip().startswith(b'c')]
    kind, grammar, raw_bound, raw_count = lines[0].split()
    assert (kind, grammar) == (b'p', b'cnf')
    bound, count = natural(raw_bound), natural(raw_count)
    rows, row = [], []
    for token in b' '.join(lines[1:]).split():
        negative = token.startswith(b'-')
        name = natural(token[1:] if negative else token)
        if name == 0:
            assert not negative and len(row) == len({abs(x) for x in row}) == 3
            rows.append(tuple(row))
            row = []
        else:
            assert name <= bound
            row.append(-name if negative else name)
    assert len(rows) == count and not row
    return bound, tuple(rows)


def emit(bound, rows, target=None):
    header = f'p cnf {bound} {len(rows)}\n'.encode()
    body = b''.join((' '.join(map(str, row)) + ' 0\n').encode() for row in rows)
    data = header + body
    if target is None:
        return data
    assert body and len(data) <= target
    # Interior body whitespace also works when the grammar requires a final newline.
    return header + b' ' * (target - len(data)) + body


def extend(a, literal, value):
    bit = value if literal > 0 else not value
    name = abs(literal)
    if name in a and a[name] != bit:
        return None
    return {**a, name: bit}


def cover(rows, a):
    """Disjoint partial assignments, branching on the first true literal of a row."""
    for row in rows:
        if any(abs(x) in a and a[abs(x)] == (x > 0) for x in row):
            continue
        for x in row:
            if abs(x) in a:
                continue
            yield from cover(rows, extend(a, x, True))
            a = extend(a, x, False)
        return
    yield a


def outside_names(rows):
    return {abs(x) for row in rows for x in row if abs(x) > 3}


@lru_cache(None)
def children(data):
    bound, rows = parse(data)
    outside = outside_names(rows)
    if len(rows) < CUT or not outside:
        return None
    fixed = (1, 2, min(outside))
    out = []
    for start in product((False, True), repeat=len(fixed)):
        for a in cover(rows[:CUT], dict(zip(fixed, start))):
            residual = []
            for row in rows[CUT:]:
                if any(abs(x) in a and a[abs(x)] == (x > 0) for x in row):
                    continue
                live = tuple(x for x in row if abs(x) not in a)
                if not live:
                    break
                residual.append(live + (1, 2)[:3 - len(live)])
            else:
                new = emit(bound, PINS + tuple(residual), len(data))
                _, new_rows = parse(new)
                assert len(new_rows) <= len(rows) - 2
                assert outside_names(new_rows) < outside
                out.append(new)
    return tuple(dict.fromkeys(out))


@lru_cache(None)
def truth(data):
    _, rows = parse(data)
    names = sorted({abs(x) for row in rows for x in row})
    index = {name: i for i, name in enumerate(names)}
    for mask in range(1 << len(names)):
        if all(any(bool(mask >> index[abs(x)] & 1) == (x > 0) for x in row)
               for row in rows):
            return True
    return False


def defect(data, clock):
    answer = clock(data)
    if answer is None:
        return True
    queries = children(data)
    if queries is None:
        return answer != truth(data)
    replies = [clock(y) for y in queries]
    return None in replies or answer != any(replies)


def referee(root, first, second):
    """Return a candidate and witness. Both candidates passed only timed bits here."""
    node = root
    while True:
        answers = (first(node), second(node))
        assert None not in answers and answers[0] != answers[1]
        queries = children(node)
        if queries is None:
            return (first if answers[0] != truth(node) else second), node
        for y in queries:
            if first(y) != second(y):
                node = y
                break
        else:
            expected = any(first(y) for y in queries)
            return (first if answers[0] != expected else second), node


def run():
    assert [i for i in range(8) if all(any(bool(i >> (abs(x)-1) & 1) == (x > 0)
            for x in row) for row in PINS)] == [0, 4]
    assert sum(len((' '.join(map(str, row)) + ' 0\n').encode()) for row in PINS) == 59
    rng = Random(1741)
    samples = []
    triple = (4, 5, 6)
    blocker = tuple(tuple(-x if b else x for x, b in zip(triple, bits))
                    for bits in product((0, 1), repeat=3))
    prefix = ((7, 8, 9),) * CUT
    # Two distributions of the eight blockers test empty child lists and negative leaves.
    for mask in range(256):
        rows = tuple(row for j, row in enumerate(blocker) if mask >> j & 1)
        samples.append(emit(9, prefix + rows).rstrip(b'\n'))
    samples.extend([emit(9, blocker + prefix), emit(9, PINS), emit(3, ())])
    pool = list(combinations(range(1, 10), 3))
    for _ in range(20):
        rows = [tuple(x * rng.choice((-1, 1)) for x in rng.choice(pool))
                for _ in range(rng.randint(17, 25))]
        samples.append(emit(9, rows))
    # Sparse long decimal IDs and a header far above the actual number of variables.
    sparse_name = 10**83 + 127
    samples.append(b'c explanatory text\r\n p\tcnf 000' + str(10**130).encode() + b' 0009\r\n'
                   + b'  0007\t8\n 009 0\r\n' * CUT + b'c body comment\n -0007  -0008 '
                   + str(sparse_name).encode() + b' 0')
    samples.extend([emit(20, ((4,5,6),) * 8 + ((-1,-2,3), (-4,-5,20))),
                    emit(20, ((4,5,6),) * 8 + ((1,-2,3), (1,9,-20)))])
    roots = tuple(samples)
    seen, stack = set(), list(roots)
    edge_count = empty_internal = 0
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        queries = children(x)
        if queries is None:
            continue
        assert truth(x) == any(truth(y) for y in queries)
        assert all(len(y) == len(x) for y in queries)
        edge_count += len(queries)
        empty_internal += not queries
        stack.extend(queries)
    assert empty_internal and {truth(x) for x in seen} == {False, True}
    # Only consensus within a single physical length supports permanent retirement.
    target = max(map(len, roots)) + 1
    batch = tuple(emit(*parse(x), target) for x in roots if parse(x)[1])
    yes = next(x for x in batch if truth(x) and children(x))
    no = next(x for x in batch if not truth(x) and children(x) is not None)
    tip = children(yes)[0]
    clocks = (lambda x: True, lambda x: False, lambda x: None if x == no else truth(x),
              lambda x: not truth(x) if x in (yes, tip) else truth(x), truth)
    controls = seen | set(batch) | {tip}
    for clock in clocks:
        assert any(defect(x, clock) for x in controls) == any(clock(x) != truth(x) for x in controls)
    live = [clocks[0], clocks[1], clocks[3], truth]
    retirements = 0
    for x in (yes, no, tip) + batch:
        assert len(x) == target
        while any(c(x) != live[0](x) for c in live):
            other = next(c for c in live if c(x) != live[0](x))
            bad, cert = referee(x, live[0], other)
            assert bad is not truth and defect(cert, bad) and len(cert) == target
            live.remove(bad)
            retirements += 1
        assert live[0](x) == truth(x)
    assert retirements == len(clocks) - 2
    # None of the children starts with this root's chosen eight rows. An isolated
    # false label on that root creates exactly one local defect in the tested set.
    assert parse(yes)[1][:6] != PINS
    isolated = lambda x: not truth(x) if x == yes else truth(x)
    assert {x for x in controls if defect(x, isolated)} == {yes}
    # Make the proof-cover cost sharp using several singly clamped vertices on
    # a single genuine UNSAT chain. Repeating easy filler clauses keeps the
    # independent ground truth small for this finite example.
    filler = tuple((x, 10, 11) for x in (4, 5, 6, 7, 8, 9))
    # Each group has its own first variable; some branches leave both shared
    # literals untouched and carry the following groups down the tree.
    chain_rows = tuple(row for row in filler for _ in range(CUT))
    terminal = tuple(tuple((abs(z) + 10) * (1 if z > 0 else -1) for z in row)
                     for row in blocker)
    chain_root = emit(16, chain_rows + terminal)
    nodes, stack = set(), [chain_root]
    while stack:
        node = stack.pop()
        if node in nodes:
            continue
        nodes.add(node)
        stack.extend(children(node) or ())
    assert all(not truth(node) for node in nodes)
    selected = sorted(nodes, key=lambda node: (len(parse(node)[1]), node))[:5]
    assert len(selected) == 5
    for clamped in selected:
        @lru_cache(None)
        def altered(node):
            if node == clamped:
                return True
            queries = children(node)
            return truth(node) if queries is None else any(altered(y) for y in queries)
        assert altered(chain_root)
        assert {node for node in nodes if defect(node, altered)} == {clamped}
    print(f'{len(roots)} roots, {len(seen)} distinct DIMACS files, {edge_count} edges, '
          f'{empty_internal} empty internal ORs, {len(clocks)} clock controls, '
          f'{retirements} certified retirements, {len(selected)} disjoint singleton defects')


def audit_quotient():
    """Exact root-cover sizes over all decoders, with a bounded-depth colorer."""
    filler = [(x, 10, 11) for x in range(4, 10) for _ in range(CUT)]
    last = [tuple(-x if bit else x for x, bit in zip((14, 15, 16), bits))
            for bits in product((0, 1), repeat=3)]
    root = emit(16, filler + last)
    positive = emit(16, [(4, 5, 6)], len(root))
    nodes, stack = set(), [root, positive]
    while stack:
        node = stack.pop()
        if node not in nodes:
            nodes.add(node)
            stack.extend(children(node) or ())

    @lru_cache(None)
    def height(node):
        return 1 + max((height(y) for y in children(node) or ()), default=-1)

    @lru_cache(None)
    def bounded_color(node, cap):
        # A reached frontier contributes the saturated value at every ancestor.
        # No call of truth() is made on an internal node.
        if cap == 1:
            return 1
        queries = children(node)
        if queries is None:
            return cap if truth(node) else 1
        return 1 + max((bounded_color(y, cap - 1) for y in queries), default=0)

    # One actual third-to-fourth-color transition on saved physical bytes.
    # The new voter detects exactly negative height two.
    same_yes = min(x for x in nodes if truth(x))
    old_no, new_no = [min(x for x in nodes if not truth(x) and height(x) == h)
                      for h in (2, 3)]
    assert all(bounded_color(x, 3) == 3 for x in (same_yes, old_no, new_no))
    assert [bounded_color(x, 4) for x in (same_yes, old_no, new_no)] == [4, 3, 4]
    print('same-length third-to-fourth-color files (SAT, old UNSAT, new UNSAT) SHA-256:',
          *(sha256(x).hexdigest() for x in (same_yes, old_no, new_no)))

    for colors in range(1, 7):
        color = {x: bounded_color(x, colors) - 1 for x in nodes}
        assert all(c == (colors - 1 if truth(x) else min(colors - 1, height(x)))
                   for x, c in color.items())
        assert set(color.values()) == set(range(colors))
        # Each extra correct program reports a timely NO on exactly one new
        # negative height. The entire recorded response vector factors to
        # the cap color and splits only the preceding all-timeout bucket.
        for x in nodes:
            timely = [j for j in range(1, colors) if bounded_color(x, j+1) == j]
            assert timely == ([] if color[x] == colors-1 else [color[x]+1])
        if colors > 1:
            lower = {x for x in nodes if not truth(x) and height(x) == colors-2}
            deep = {x for x in nodes if not truth(x) and height(x) >= colors-1}
            assert lower and deep
            assert all(bounded_color(x, colors-1) == colors-1 for x in lower | deep)
            assert all(bounded_color(x, colors) == colors-1 for x in lower)

        threshold_tables = [sum(1 << i for i in range(j, colors))
                            for j in range(colors + 1)]
        violated = set()
        for node in nodes:
            queries = children(node)
            mask = 0
            for table in range(1 << colors):
                def reply(x):
                    return bool((table >> color[x]) & 1)
                expected = truth(node) if queries is None else any(reply(y) for y in queries)
                if reply(node) != expected:
                    mask |= 1 << table
            assert sum((mask >> table) & 1 for table in threshold_tables) <= 1
            if mask:
                violated.add(mask)

        @lru_cache(None)
        def minimum_cover(uncovered):
            if not uncovered:
                return 0
            first = uncovered & -uncovered
            return 1 + min(minimum_cover(uncovered & ~mask)
                           for mask in violated if mask & first)

        optimum = minimum_cover((1 << (1 << colors)) - 1)
        assert optimum == colors + 1
        print(f'{colors} colors, {len(nodes)} files at {len(root)} bytes, '
              f'height {height(root)}, {1 << colors} tables, minimum {optimum}')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quotient', action='store_true',
                        help='also compute optimal root covers for Boolean decoders of signatures')
    options = parser.parse_args()
    run()
    if options.quotient:
        audit_quotient()
