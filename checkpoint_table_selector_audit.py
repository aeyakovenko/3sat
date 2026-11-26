"""Evaluate shared subset ORs as an actual gate graph for every small table."""
from itertools import product


def select_rows(table, chunk, address):
    intervals = len(table) - 1
    width = len(table[0])
    active = [address == i for i in range(intervals)]
    if not any(active):
        return None
    families = []
    for start in range(0, intervals, chunk):
        selects = active[start:start + chunk]
        gates = [False]
        for bit in selects:
            gates += [entry or bit for entry in gates]
        families.append(gates)
    result = []
    for shift in (0, 1):
        endpoint = []
        for col in range(width):
            partials = []
            for group_id, gates in enumerate(families):
                start = group_id * chunk
                mask = sum(table[i + shift][col] << (i - start)
                           for i in range(start, min(intervals, start + chunk)))
                partials.append(gates[mask])
            endpoint.append(int(any(partials)))
        result.append(tuple(endpoint))
    return tuple(result)


if __name__ == '__main__':
    checks = 0
    for intervals, width, chunk in [(1, 4, 2), (2, 3, 2), (3, 3, 2), (4, 2, 3), (5, 2, 2)]:
        for bits in product(range(2), repeat=(intervals + 1)*width):
            table = [bits[start:start+width] for start in range(0, len(bits), width)]
            for address in range(2**intervals.bit_length()):
                expected = tuple(table[address:address+2]) if address < intervals else None
                assert select_rows(table, chunk, address) == expected
                checks += 1
    print(f'{checks} exact comparisons of two-row selector circuits.')
