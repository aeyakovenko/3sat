"""Exhaust the subset-label guards and positive table lookups on small alphabets."""
from itertools import combinations, product
from math import comb
from random import Random


def label_universe(addresses, r):
    size = r
    while comb(size, r) < addresses:
        size += 1
    assert size == r or comb(size - 1, r) < addresses
    return size


class GuardTable:
    """One shared OR for each chunk-choice row and distinct projection of i."""

    def __init__(self, size, r):
        self.size = size
        self.r = r
        self.bits = max(1, (size - 1).bit_length())
        q, extra = divmod(self.bits, r + 1)
        self.lengths = [q + (j < extra) for j in range(r + 1)]
        self.chunks = []
        start = 0
        for width in self.lengths:
            self.chunks.append([(i >> start) & ((1 << width) - 1)
                                for i in range(1 << self.bits)])
            start += width
        self.tests = []
        self.num_shared = 0
        for choice in product(range(r + 1), repeat=r):
            shared = {}
            for i in range(size):
                projection = tuple(self.chunks[t][i] for t in choice)
                shared[projection] = shared.get(projection, 0) | (1 << i)
            bound = 1 << sum(self.lengths[t] for t in set(choice))
            assert len(shared) <= bound
            if size == 1 << self.bits:
                assert len(shared) == bound
            self.num_shared += len(shared)
            self.tests.append((choice, shared))

    def enabled(self, labels):
        passing = (1 << self.size) - 1
        for choice, shared in self.tests:
            values = tuple(self.chunks[t][label] for t, label in zip(choice, labels))
            for projection, users in shared.items():
                if all(left != right for left, right in zip(projection, values)):
                    passing &= ~users
        return passing


def subset_mask(labels):
    return sum(1 << i for i in set(labels))


def colex(labels):
    return sum(comb(i, j) for j, i in enumerate(labels, 1))


def decode(labels, size, m, k):
    if any(i >= size for i in labels) or any(a >= b for a, b in zip(labels, labels[1:])):
        return None
    rank = colex(labels)
    if rank >= m**k:
        return None
    address = [0] * k
    for bank in reversed(range(k)):
        rank, address[bank] = divmod(rank, m)
    return tuple(address)


def audit_lookup(m, k, r):
    count = m**k
    size = label_universe(count, r)
    guard = GuardTable(size, r)
    real_queries = list(product(range(m), repeat=k))
    # Enumeration by the binary indicator number is an independent colex ordering.
    codes = sorted(combinations(range(size), r), key=subset_mask)
    assert [colex(code) for code in codes] == list(range(len(codes)))
    rank_reference = {code: q for code, q in zip(codes, real_queries)}
    valid_guesses = []
    guesses = 0
    bad_label, bad_rank = 0, 0
    for labels in product(range(1 << guard.bits), repeat=r):
        enabled = guard.enabled(labels)
        # Tests every i, including the ones which must stay false. Repeated
        # or padded guessed labels are included in this check of the raw guard.
        assert enabled == subset_mask(i for i in labels if i < size)
        address = decode(labels, size, m, k)
        assert address == rank_reference.get(labels)
        if address is not None:
            valid_guesses.append((enabled, address))
        elif labels in codes:
            bad_rank += 1
        else:
            bad_label += 1
        guesses += 1

    padded_m = 1 << (m - 1).bit_length()
    answers = 0
    for db in range(1 << (m*k)):
        tables = [tuple((db >> (j*m+i)) & 1 if i < m else 0 for i in range(padded_m))
                  for j in range(k)]
        assert all(not any(bank[m:]) for bank in tables)
        # A positive flag pin can be set arbitrarily within an enabled model.
        possible = [mask for mask, address in valid_guesses
                    if all(tables[j][a] for j, a in enumerate(address))]
        for code in codes:
            needed = subset_mask(code)
            actual = any((mask & needed) == needed for mask in possible)
            q = rank_reference.get(code)
            expected = q is not None and all(db & (1 << (j*m+a)) for j, a in enumerate(q))
            assert actual == expected, (m, k, r, db, code)
            answers += 1
    direct_guards = size * (r+1)**r
    print(f'm={m}, k={k}, r={r}, S={size}: {guesses} guesses, {bad_label} invalid '
          f'label tuples, {bad_rank} padded ranks, {guard.num_shared}/{direct_guards} '
          f'shared/unshared ORs, {answers} table answers')
    return guesses * size, answers, bad_label, bad_rank


class PackedBank:
    """Emit the actual ternary forbidden clauses of one binary table."""

    def __init__(self, values, block):
        assert block > 0 and block & (block - 1) == 0
        self.block = block
        groups = (len(values) + block - 1) // block
        q, extra = divmod((groups - 1).bit_length(), 3)
        self.shape = tuple(1 << (q + (j < extra)) for j in range(3))
        na, nb, nc = self.shape
        self.capacity = na * nb * nc * block
        self.names_a = list(range(1, 1 + na))
        self.names_b = list(range(1 + na, 1 + na + nb))
        self.k_names = {}
        base = 1 + na + nb
        self.clauses = []
        cells = iter(list(values) + [0] * (self.capacity - len(values)))
        for a, b, c in product(range(na), range(nb), range(nc)):
            mask = sum(next(cells) << h for h in range(block))
            name = self.k_names.setdefault((c, mask), base + len(self.k_names))
            self.clauses.append((-self.names_a[a], -self.names_b[b], -name))
        assert all(len(set(map(abs, clause))) == 3 for clause in self.clauses)

    def lookup(self, address):
        _, nb, nc = self.shape
        hi, low = divmod(address, self.block)
        hi, c = divmod(hi, nc)
        a, b = divmod(hi, nb)
        assert 0 <= a < len(self.names_a)
        true = {self.names_a[a], self.names_b[b]}
        for (selector, mask), name in self.k_names.items():
            if selector == c and not mask & (1 << low):
                true.add(name)
        return all(any(-literal not in true for literal in clause) for clause in self.clauses)


def audit_packed_banks():
    rng = Random(24919)
    tables = addresses = high_examples = 0
    for m, block in [(1, 1), (2, 2), (3, 1), (3, 4), (5, 2), (7, 2), (8, 1),
                     (8, 4), (19, 2), (31, 4), (65, 4), (101, 8)]:
        if m <= 8:
            cases = list(product((0, 1), repeat=m))
        else:
            cases = [[0]*m, [1]*m, [i % 2 for i in range(m)],
                     [int(i == m-1) for i in range(m)], [int(i != 0) for i in range(m)]]
            cases.extend([rng.randrange(2) for _ in range(m)] for _ in range(25))
        for values in cases:
            bank = PackedBank(values, block)
            for address in range(bank.capacity):
                assert bank.lookup(address) == bool(address < m and values[address])
                addresses += 1
            tables += 1
            high_examples += all(width > 1 for width in bank.shape)
    assert high_examples
    return tables, addresses, high_examples


def clause_value(clause, valuation):
    return any(bool(valuation & (1 << (abs(lit) - 1))) == (lit > 0) for lit in clause)


def audit_one_bank_triples():
    tables = answers = models_tried = 0
    for m in (1, 2, 3, 4, 5, 7):
        size = label_universe(m, 3)
        triples = sorted(combinations(range(1, size+1), 3),
                         key=lambda t: subset_mask(i-1 for i in t))
        anchors = tuple(range(size+1, size+4))
        # Each nonzero anchor pattern falsifies one distinct guard.
        guards = [tuple(-v if code & (1 << j) else v for j, v in enumerate(anchors))
                  for code in range(1, 8)]
        forced = [val for val in range(1 << (size + 3))
                  if all(clause_value(c, val) for c in guards)]
        assert forced == list(range(1 << size))
        queries = [tuple((i, anchors[0], anchors[1]) for i in tri)
                   + (tuple(-v for v in anchors),) for tri in triples]
        pin_masks = [[all(clause_value(c, x) for c in packet) for x in forced]
                     for packet in queries]
        for db in range(1 << m):
            forbidden = [tuple(-v for v in tri) for j, tri in enumerate(triples)
                         if j >= m or not db & (1 << j)]
            models = [all(clause_value(c, x) for c in forbidden) for x in forced]
            for j, (tri, pinned) in enumerate(zip(triples, pin_masks)):
                verdict = any(legal and query for legal, query in zip(models, pinned))
                target = j < m and bool(db & (1 << j))
                assert verdict == target
                # Test the extremal witness itself, including all padding pins.
                x = subset_mask(i-1 for i in tri)
                assert pinned[x] and models[x] == target
                answers += 1
                models_tried += len(forced)
            tables += 1
    return tables, answers, models_tried


def signed_pair_layout(db, r):
    """Two two-entry banks. The quotient has one group and its low block has two bits."""
    size = label_universe(4, r)
    codes = sorted(combinations(range(size), r), key=subset_mask)[:4]
    tags = [(12 + 10*i, 13 + 10*i) for i in range(size)]
    reserved = {name for pair in tags for name in pair}
    fresh = (j for j in range(4, 100) if j not in reserved)
    anchors = (1, 2, 3)
    clauses = [tuple(-a if pattern & (1 << j) else a for j, a in enumerate(anchors))
               for pattern in range(1, 8)]

    def add(*lits):
        assert len(set(map(abs, lits))) == len(lits)
        pads = [a for a in anchors if a not in map(abs, lits)]
        clauses.append(tuple(lits) + tuple(pads[:3-len(lits)]))

    high1, high2 = next(fresh), next(fresh)
    add(high1)
    add(high2)
    addr = (next(fresh), next(fresh))
    claims = (next(fresh), next(fresh))
    both = next(fresh)
    flags = [next(fresh) for _ in range(size)]
    # At size four encode the colex membership test by its direct truth table.
    for i, flag in enumerate(flags):
        for rank, code in enumerate(codes):
            if i not in code:
                add(-flag, -addr[0] if rank & 2 else addr[0],
                    -addr[1] if rank & 1 else addr[1])
        for tag, flag_name in enumerate(tags[i]):
            add(-flag_name, flag)
            add(-flag_name, both if tag else -both)
    add(-claims[0], -claims[1], both)
    add(claims[0], -both)
    add(claims[1], -both)
    for j in range(2):
        mismatch = [next(fresh) for _ in range(4)]
        for mask, bad in enumerate(mismatch):
            # D_mask = [mask[low] != proposed bank bit]. Its forbidden truth
            # table rows give width-three clauses on three distinct variables.
            for low, bit in product((0, 1), repeat=2):
                differs = ((mask >> low) & 1) != bit
                add(-addr[j] if low else addr[j], -claims[j] if bit else claims[j],
                    bad if differs else -bad)
        mask = (db >> (2*j)) & 3
        add(-high1, -high2, -mismatch[mask])
    used = {abs(v) for c in clauses for v in c}
    bound = max(used)
    for j in range(1, bound+1):
        if j not in used:
            add(-j)
    prefix = (f'p cnf {bound} {len(clauses)+r}\n'.encode() +
              b''.join((' '.join(map(str, c)) + ' 0\n').encode() for c in clauses))
    return codes, tags, flags, prefix


def audit_signed_pairs():
    from table_probe_context_audit import parse, satisfiable

    pairs = cnfs = 0
    for r in (2, 3):
        for db in range(16):
            codes, tags, flags, prefix = signed_pair_layout(db, r)
            for rank, code in enumerate(codes):
                packets = []
                verdicts = []
                for tag in (0, 1):
                    pins = [tags[code[0]][tag]] + [flags[i] for i in code[1:]]
                    packet = b''.join(f'{pin} 1 2 0\n'.encode() for pin in pins)
                    clauses, _ = parse(prefix + packet)
                    verdicts.append(satisfiable(clauses))
                    packets.append(packet)
                    cnfs += 1
                assert len(packets[0]) == len(packets[1])
                offsets = [i for i, (a, b) in enumerate(zip(*packets)) if a != b]
                assert offsets == [len(str(tags[code[0]][0]))-1]
                off, = offsets
                assert (packets[0][off], packets[1][off]) == (ord('2'), ord('3'))
                assert packets[0][off] ^ packets[1][off] == 1
                a, b = divmod(rank, 2)
                answer = bool(db & (1 << a)) and bool(db & (1 << (2+b)))
                assert verdicts == [not answer, answer]
                pairs += 1
    return pairs, cnfs


def main():
    cases = [(1, 2, 2), (2, 1, 1), (2, 3, 2), (3, 2, 2), (2, 4, 3),
             (3, 2, 3), (3, 3, 2), (2, 2, 4)]
    totals = [sum(column) for column in zip(*(audit_lookup(*p) for p in cases))]
    assert totals[2] and totals[3]
    for r in (1, 2, 3):
        for width in (4, 8, 12):
            size = 1 << width
            guard = GuardTable(size, r)
            # Independent exact count when all chunks have equal width.
            if width % (r + 1) == 0:
                alphabet = 1 << (width // (r + 1))
                expected = sum(alphabet**len(set(t)) for t in product(range(r + 1), repeat=r))
                assert guard.num_shared == expected
            print(f'sharing S={size}, r={r}: {guard.num_shared}/{size*(r+1)**r}')
    print(f'{totals[0]} candidate/flag membership checks, {totals[1]} positive table '
          f'answers, {totals[2]} rejected label tuples, {totals[3]} rejected padded ranks')
    packed = audit_packed_banks()
    print(f'{packed[0]} packed ternary tables, {packed[1]} padded-address verdicts, '
          f'{packed[2]} tables with three nontrivial quotient chunks')
    triples = audit_one_bank_triples()
    print(f'{triples[0]} single-bank triple tables, {triples[1]} query verdicts, '
          f'{triples[2]} complete flag valuations tested against those queries')
    signed = audit_signed_pairs()
    print(f'{signed[0]} one-physical-bit signed pairs, {signed[1]} independently solved '
          f'proper DIMACS formulas')


if __name__ == '__main__':
    main()
