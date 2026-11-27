"""Exhaust deterministic Boolean query graphs and check a one-variable lift.

A query node reads one fixed input bit. Its two edges may lead to any node
or either terminal. The start is node zero. Padding by unreachable nodes
covers smaller graphs, and a node with both edges to one terminal computes
a constant. A nonterminating run disqualifies a graph as a total decider.
"""

from itertools import product

from table_probe_context_audit import parse, truth_table_sat


def audit_dimacs_lift(guarded):
    """Align every private sign in the same lane, directly before its digit."""
    fixed = [(a, 2 * b, 3 * c) for a, b, c in product((1, -1), repeat=3)
             if (b, c) != (1, 1)]
    if guarded:
        fixed.append((-4, 2, 3))
    private = [1, 1, 4] if guarded else [1, 1]
    variable_count = 4 if guarded else 3
    prefix = f'p cnf {variable_count} {len(fixed) + len(private)}\n'
    prefix += ''.join(' '.join(map(str, clause)) + ' 0\n' for clause in fixed)
    files = []
    for bits in product((False, True), repeat=len(private)):
        data = bytearray(prefix, 'ascii')
        addresses = []
        for index, (name, bit) in enumerate(zip(private, bits)):
            if len(data) % 2:
                data.extend(b' ')
            addresses.append(len(data) // 2)
            # On the last pin for the guard, z=0 must agree with the fixed -4 pin.
            minus = not bit if index == 2 else bit
            data.extend(b' -' if minus else b'  ')
            data.extend(f'{name} 2 3 0\n'.encode('ascii'))
        clauses, variables = parse(data)
        assert truth_table_sat(clauses, variables) == (
            bits[0] == bits[1] and (not guarded or not bits[2]))
        assert (8 * len(data) + 2).bit_length() <= 16
        assert max(addresses) < int.from_bytes(b'  ', 'little')
        files.append(bytes(data))
    varying = {offset // 2 for offset, column in enumerate(zip(*files)) if len(set(column)) > 1}
    assert len(set(map(len, files))) == 1 and varying == set(addresses)
    return len(files[0]), addresses


def input_columns(bits):
    """Bit u of column j is the value of variable j on assignment u."""
    return [
        sum(1 << u for u in range(1 << bits) if (u >> j) & 1)
        for j in range(bits)
    ]


def parallel_table(columns, edges, full):
    """Return the truth mask, or None if any assignment diverges."""
    nodes = len(columns)
    # The last two entries are the absorbing false and true terminals.
    reached = [full] + [0] * (nodes + 1)
    for _ in range(nodes):
        after = [0] * nodes + reached[nodes:]
        for node, column in enumerate(columns):
            here = reached[node]
            after[edges[2 * node]] |= here & ~column
            after[edges[2 * node + 1]] |= here & column
        reached = after
    # On a fixed assignment a repeated node repeats forever.
    if (reached[nodes] | reached[nodes + 1]) != full:
        return None
    return reached[nodes + 1]


def scalar_table(bits, labels, edges):
    """Independent one-assignment-at-a-time simulation with cycle detection."""
    nodes = len(labels)
    table = 0
    for assignment in range(1 << bits):
        seen = set()
        node = 0
        while node < nodes:
            if node in seen:
                return None
            seen.add(node)
            reply = (assignment >> labels[node]) & 1
            node = edges[2 * node + reply]
        if node == nodes + 1:
            table |= 1 << assignment
    return table


def enumerate_tables(bits, nodes, *, check_scalar=False):
    columns = input_columns(bits)
    full = (1 << (1 << bits)) - 1
    tables = set()
    graphs = 0
    for labels in product(range(bits), repeat=nodes):
        query_columns = [columns[j] for j in labels]
        for edges in product(range(nodes + 2), repeat=2 * nodes):
            table = parallel_table(query_columns, edges, full)
            if check_scalar:
                assert table == scalar_table(bits, labels, edges)
            if table is not None:
                tables.add(table)
            graphs += 1
    assert graphs == bits**nodes * (nodes + 2) ** (2 * nodes)
    return tables, graphs


def main():
    for guarded in [False, True]:
        length, sites = audit_dimacs_lift(guarded)
        print(f'{length}-byte proper DIMACS files, private 16-bit words at {sites}.')
    for bits, nodes, expected in [(1, 1, 4), (2, 1, 6), (2, 2, 14)]:
        tables, _ = enumerate_tables(bits, nodes, check_scalar=True)
        assert len(tables) == expected
        if (bits, nodes) == (2, 2):
            assert set(range(16)) - tables == {0b0110, 0b1001}

    tables, graphs = enumerate_tables(3, 3)
    assert graphs == 421_875
    assert len(tables) == 126
    # The low nibble gives the truth table with the new high input bit zero.
    hard_counts = [
        sum((low | (high << 4)) not in tables for high in range(16))
        for low in range(16)
    ]
    assert hard_counts == [2, 9, 9, 6, 9, 6, 15, 9, 9, 15, 6, 9, 6, 9, 9, 2]

    equality = 0b1001
    attainable_highs = {
        high for high in range(16) if (equality | (high << 4)) in tables
    }
    assert attainable_highs == {equality}
    # Query z first. When z=0, query x and then y to decide equality.
    labels = [2, 0, 1, 1]
    edges = [1, 4, 2, 3, 5, 4, 4, 5]
    assert scalar_table(3, labels, edges) == equality
    print(f"{graphs:,} labeled three-node graphs realize {len(tables)}/256 functions.")
    print(f"Three-node-infeasible extensions of each two-input table: {hard_counts}")
    print("The only attainable high cofactor extending equality is equality (0x9).")
    print("The extension with zero high cofactor needs exactly four query nodes.")


if __name__ == "__main__":
    main()
