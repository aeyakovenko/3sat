"""Check exact signed costs for rank-dependent completions in odd characteristic."""

from matrix_residual_query_audit import binary_rank


def order_of_two(prime):
    value = 2 % prime
    order = 1
    while value != 1:
        value = 2 * value % prime
        order += 1
    return order


def prediction(d, prime):
    period = order_of_two(prime)
    if d % period:
        return 1
    cost = period
    while (d // cost) % prime == 0:
        cost *= prime
    return cost


def character_table(d):
    """Sum binary Walsh signs separately on every input-rank orbit."""
    table = [[0] * (d + 1) for _ in range(d + 1)]
    masks = [sum(1 << (i*d + i) for i in range(h)) for h in range(d + 1)]
    for bits in range(1 << (d*d)):
        rows = [(bits >> (d*i)) & ((1 << d) - 1) for i in range(d)]
        r = binary_rank(rows)
        for h, mask in enumerate(masks):
            sign = -1 if (bits & mask).bit_count() % 2 else 1
            table[h][r] += sign
    return table


def consistent(equations, prime):
    """Each row contains coefficients followed by the right-hand side."""
    pivots = {}
    for equation in equations:
        row = [x % prime for x in equation]
        for j in range(len(row)-1):
            v = row[j]
            if not v:
                continue
            if j not in pivots:
                inv = pow(v, -1, prime)
                pivots[j] = [inv * x % prime for x in row]
                break
            row = [(x - v*y) % prime for x, y in zip(row, pivots[j])]
        else:
            if row[-1]:
                return False
    return True


def exhaustive_cost(d, table, prime):
    # Zero has value one, full rank zero. A total radial completion has
    # one arbitrary coefficient at each remaining rank. All high-rank
    # Fourier coefficients must vanish.
    for q in range(d + 1):
        equations = [orbit[1:d] + [-orbit[0]] for orbit in table[q+1:]]
        if consistent(equations, prime):
            return q
    raise AssertionError('all queries must suffice')


def main():
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    raw = recurrence = 0
    for d in range(1, 5):
        table = character_table(d)
        for p in primes:
            assert exhaustive_cost(d, table, p) == prediction(d, p)
            raw += 1
    for p in primes:
        row = [1]
        for d in range(1, 301):
            row = [1] + [(row[j] + pow(2, d-j, p)*row[j-1]) % p
                         for j in range(1, d)] + [1]
            first = next(j for j in range(1, d+1) if row[j])
            assert first == prediction(d, p)
            recurrence += 1
    print(f'{raw} raw Walsh completion systems, {recurrence} Gaussian-row minima.')
    print('Characteristic 3:', [(d, prediction(d, 3)) for d in (2, 6, 18, 54, 162)])


if __name__ == '__main__':
    main()
