"""Verify the rotated query graphs, their closure clauses, and the local table bits."""

from collections import Counter
from itertools import product
from random import Random


def parameters(t):
    r = min((t - 1).bit_length(), t - 1)
    q = t - r
    k = max(0, q.bit_length() - 2)
    return r, q, k


def bits(value, width):
    return [(value >> i) & 1 for i in reversed(range(width))]


def index_of(values):
    result = 0
    for value in values:
        result = 2 * result + value
    return result


def build(t, table):
    """IDs retain the suffix-table bits as a literal low-order field."""
    r, q, k = parameters(t)
    high = t + 2
    accept, reject = 1, 2
    nodes = {}
    wildcard = Counter()

    def prefix(depth, path):
        return (1 << high) + (1 << depth) + path

    def suffix(group, depth, mask):
        if depth == 0:
            return accept if mask == 1 else reject
        return ((2 + group * (k + 1) + depth) << high) + mask

    def table_bit(assignment):
        return table[index_of(assignment)]

    def bottom(group, path):
        order = [r + (group + j) % q for j in range(q)]
        known = bits(group, r) + [0] * q
        for j, value in zip(order[:q-k], bits(path, q - k)):
            known[j] = value
        mask = 0
        # Bit s in the suffix truth table is indexed by its usual binary s.
        for s in range(1 << k):
            for j, value in zip(order[q-k:], bits(s, k)):
                known[j] = value
            mask |= table_bit(known) << s
            wildcard[index_of(known)] += 1
        return suffix(group % q, k, mask)

    for depth in range(t - k):
        for path in range(1 << depth):
            group = path >> (depth-r) if depth >= r else 0
            query = depth if depth < r else r + (group + depth - r) % q
            children = []
            for reply in (0, 1):
                child = 2 * path + reply
                if depth + 1 == t-k:
                    old_prefix = child >> (q-k)
                    children.append(bottom(old_prefix, child % (1 << (q-k))))
                else:
                    children.append(prefix(depth + 1, child))
            nodes[prefix(depth, path)] = (query, *children)

    for group in range(min(q, 1 << r)):
        for d in range(1, k + 1):
            half = 1 << (d - 1)
            low_mask = (1 << half) - 1
            for mask in range(1 << (2 * half)):
                children = (suffix(group, d - 1, mask & low_mask),
                            suffix(group, d - 1, mask >> half))
                nodes[suffix(group, d, mask)] = (r + (group + q - d) % q, *children)

    assert wildcard == Counter({j: 1 for j in range(1 << t)})
    return prefix(0, 0), nodes


def walk(start, nodes, assignment):
    path = []
    node = start
    while node in nodes:
        query, low, high = nodes[node]
        path.append(query)
        node = (low, high)[assignment[query]]
    assert sorted(path) == list(range(len(assignment)))
    return node == 1


def clauses_for(t, start, nodes, assignment):
    # Separate graph IDs, selector IDs and forced-false constants by low tag.
    z = lambda node: 8 * node + 4
    u = lambda query: 8 * query + 5
    clauses = [tuple(-v if truth else v for v, truth in zip((1, 2, 3), row))
               for row in product((0, 1), repeat=3) if any(row)]
    clauses.extend(((z(start), 1, 2), (-z(2), 1, 2)))
    clauses.extend(((u(i) if a else -u(i)), 1, 2) for i, a in enumerate(assignment))
    for src, (query, low, high) in nodes.items():
        clauses.extend(((-z(src), u(query), z(low)), (-z(src), -u(query), z(high))))
    assert all(len({abs(v) for v in row}) == 3 for row in clauses)
    return clauses


def serialize(clauses, table_independent_bound, word_bytes, chunk_bits):
    assert chunk_bits <= word_bytes
    groups = (table_independent_bound.bit_length() + chunk_bits - 1) // chunk_bits

    def name(code):
        digits = format(code, f'0{groups * chunk_bits}b')
        return b'1' + b''.join(
            b'0' * (word_bytes - chunk_bits) + digits[i:i + chunk_bits].encode()
            for i in range(0, len(digits), chunk_bits))

    maximum = name((1 << (groups * chunk_bits)) - 1)
    prefix = b'p cnf ' + maximum + f' {len(clauses)}\n'.encode()
    buf = bytearray(prefix.ljust(((len(prefix) + word_bytes - 1) // word_bytes) * word_bytes))
    for row in clauses:
        for v in row:
            buf.extend(b' ' * (word_bytes - 2) + (b'-' if v < 0 else b' ') + name(abs(v)))
        buf.extend(b' 0\n'.ljust(word_bytes))
    # The first byte in the next field is whitespace; the terminator itself
    # needs preceding whitespace to delimit the last decimal name.
    return bytes(buf)


def decode_token(token, word_bytes, chunk_bits):
    name = token.lstrip(b'-')
    assert name[:1] == b'1' and (len(name) - 1) % word_bytes == 0
    bits_of_name = bytearray()
    for i in range(1, len(name), word_bytes):
        chunk = name[i:i + word_bytes]
        assert chunk[:word_bytes - chunk_bits] == b'0' * (word_bytes - chunk_bits)
        bits_of_name.extend(chunk[-chunk_bits:])
    value = int(bits_of_name, 2)
    return -value if token.startswith(b'-') else value


def parsed_clauses(blob, word_bytes, chunk_bits):
    lines = blob.splitlines()
    header = lines[0].split()
    assert header[:2] == [b'p', b'cnf']
    rows, pending = [], []
    for token in b' '.join(lines[1:]).split():
        if token == b'0':
            assert len(pending) == 3 and len({v.lstrip(b'-') for v in pending}) == 3
            rows.append(tuple(decode_token(v, word_bytes, chunk_bits) for v in pending))
            pending.clear()
        else:
            assert token.lstrip(b'-').isdigit() and token.lstrip(b'-') <= header[2]
            pending.append(token)
    assert not pending and len(rows) == int(header[3])
    return rows


def exact_sat(rows):
    if not rows:
        return True
    if any(not row for row in rows):
        return False
    first = min(rows, key=len)
    options = first[:1] if len(first) == 1 else (first[0], -first[0])
    for chosen in options:
        rest = [tuple(x for x in row if x != -chosen) for row in rows if chosen not in row]
        if exact_sat(rest):
            return True
    return False


def audit():
    rng = Random(37)
    examples = lookups = solves = 0
    for t in (1, 2, 3, 5, 8, 12):
        tables = (product((0, 1), repeat=1 << t) if t <= 3 else
                  ([rng.randrange(2) for _ in range(1 << t)] for _ in range(3)))
        for table in tables:
            start, nodes = build(t, table)
            histogram = Counter(v[0] for v in nodes.values())
            r, q, k = parameters(t)
            groups_per_rotation = ((1 << r) + q - 1) // q
            suffix_count = sum(1 << (1 << d) for d in range(1, k + 1))
            tail_cap = groups_per_rotation * ((1 << (q-k))-1) + suffix_count
            assert max(histogram.values()) <= max(1 << r, tail_cap)
            for u, label in enumerate(table):
                assignment = bits(u, t)
                assert walk(start, nodes, assignment) == bool(label)
                if t <= 2:
                    assert exact_sat(clauses_for(t, start, nodes, assignment)) == bool(label)
                    solves += 1
                lookups += 1
            examples += 1
    print(f'{examples} query graphs, {lookups} paths, {solves} exact 3-CNF solutions')

    # At t=8 the suffix ID has a nonempty truth-table field. Anchor all code
    # lengths independently of the settings. Vary each table bit exactly once.
    t = 8
    for b in (1, 2, 4):
        wbytes = 4
        zero = [0] * (1 << t)

        def file(table, selector):
            start, nodes = build(t, table)
            return serialize(clauses_for(t, start, nodes, selector),
                             1 << (2*t+12), wbytes, b)

        baseline = file(zero, bits(0, t))
        model_width = 16 * (((8 * len(baseline) + 1).bit_length() + 15) // 16)
        assert model_width == 8 * wbytes
        start, nodes = build(t, zero)
        assert parsed_clauses(baseline, wbytes, b) == clauses_for(t, start, nodes, bits(0, t))
        changes = set()
        for i in range(1 << t):
            one = zero.copy()
            one[i] = 1
            changed = file(one, bits(0, t))
            delta = [j for j, (x, y) in enumerate(zip(baseline, changed)) if x != y]
            assert len(changed) == len(baseline) and len(delta) == 1
            j = delta[0]
            assert (baseline[j], changed[j]) == (ord('0'), ord('1')) and j not in changes
            changes.add(j)
        sites = set()
        for i in range(t):
            changed = file(zero, bits(1 << i, t))
            delta = [j for j, (x, y) in enumerate(zip(baseline, changed)) if x != y]
            assert len(delta) == 1 and delta[0] not in changes
            sites.add(delta[0] // wbytes)
        assert len(sites) == t
        print(f'b={b}: {len(changes)} independent one-byte table edits; {len(sites)} selector words')


if __name__ == '__main__':
    audit()
