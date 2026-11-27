"""Compare additive FFT evaluation and interpolation, edit radius, and local completion."""

from itertools import combinations, product


class BinaryField:
    def __init__(self, degree, polynomial):
        self.size = 1 << degree
        self.log = [0] * self.size
        self.exp = []
        value = 1
        for index in range(self.size - 1):
            assert value not in self.exp
            self.exp.append(value)
            self.log[value] = index
            value <<= 1
            if value & self.size:
                value ^= polynomial
        assert value == 1 and set(self.exp) == set(range(1, self.size))

    def mul(self, left, right):
        if not left or not right:
            return 0
        return self.exp[(self.log[left] + self.log[right]) % (self.size - 1)]

    def div(self, left, right):
        assert right
        if not left:
            return 0
        return self.exp[(self.log[left] - self.log[right]) % (self.size - 1)]

    def subspace_polynomial(self, dimension, point):
        result = 1
        for root in range(1 << dimension):
            result = self.mul(result, point ^ root)
        return result

    def transform(self, data, offset, inverse=False):
        if len(data) == 1:
            return tuple(data)
        half = len(data) // 2
        dimension = half.bit_length() - 1
        d = self.div(self.subspace_polynomial(dimension, offset),
                     self.subspace_polynomial(dimension, half))
        if inverse:
            low = self.transform(data[:half], offset, True)
            high = self.transform(data[half:], offset ^ half, True)
            second = tuple(a ^ b for a, b in zip(low, high))
            first = tuple(a ^ self.mul(d, b) for a, b in zip(low, second))
            return first + second
        low = tuple(a ^ self.mul(d, b) for a, b in zip(data[:half], data[half:]))
        high = tuple(a ^ b for a, b in zip(low, data[half:]))
        return self.transform(low, offset) + self.transform(high, offset ^ half)

    def evaluate(self, message):
        k = len(message)
        coefficients = self.transform(message, 0, True)
        return self.transform(coefficients + (0,) * k, 0)

    def lagrange_column(self, k, position):
        result = []
        for point in range(self.size):
            value = 1
            for other in range(k):
                if other != position:
                    value = self.mul(value, self.div(point ^ other, position ^ other))
            result.append(value)
        return tuple(result)


def audit(degree, polynomial):
    field = BinaryField(degree, polynomial)
    size = field.size
    k = size // 2
    columns = [field.lagrange_column(k, index) for index in range(k)]
    scale = [field.div(1, columns[0][i]) if i >= k else 1 for i in range(size)]
    words = []
    for data in product(range(size), repeat=k):
        raw_word = field.evaluate(data)
        word = tuple(field.mul(scale[i], raw_word[i]) for i in range(size))
        assert word[:k] == data
        independent = [0] * size
        for value, column in zip(data, columns):
            for index, entry in enumerate(column):
                independent[index] ^= field.mul(value, entry)
        assert raw_word == tuple(independent)
        # Relative to one fixed diagonal; linearity transfers to all others.
        edits = sum(value != 0 for value in data)
        words.append((word, edits))

    for count in range(k + 1):
        for subset in combinations(range(size), count):
            reachable = {tuple(word[i] for i in subset)
                         for word, edits in words if edits <= count}
            assert len(reachable) == size**count
    nonzero = [pair for pair in words if pair[1]]
    assert min(sum(value != 0 for value in word) for word, _ in nonzero) == size - k + 1
    for index in range(size):
        for value in range(1, size):
            def distance(word):
                return sum(actual != (value if pos == index else 0)
                           for pos, actual in enumerate(word))

            assert min(distance(word) for word, _ in nonzero) == size - k
            assert min(distance(word) for word, edits in nonzero
                       if edits == 1 and word[index] == value) == size - k
            if value == 1:
                single_bit_source = index if index < k else 0
                delta = tuple(int(j == single_bit_source) for j in range(k))
                single_bit_word = tuple(field.mul(s, v) for s, v in zip(scale, field.evaluate(delta)))
                assert single_bit_word[index] == 1 and distance(single_bit_word) == size - k
            for others in combinations([p for p in range(size) if p != index], k):
                # Any polynomial vanishing at k points is the zero polynomial.
                assert not any(word[index] == value and all(not word[p] for p in others)
                               for word, _ in words)
    return len(words)


def data_field(symbol, degree):
    return "1" + format(symbol, f"0{degree}b")


def proper_dimacs(left, right, degree):
    """One physical decimal-name occurrence per input field, with pinned false variables."""
    aux = 2 * 10**degree
    selectors = [aux + i for i in range(len(left))]
    zero, other, third = aux + len(left), aux + len(left) + 1, aux + len(left) + 2
    clauses = []
    for word in range(1, 8):
        pins = (zero, other, third)
        clauses.append(tuple(-v if (word >> i) & 1 else v for i, v in enumerate(pins)))
    for selector, x, y in zip(selectors, left, right):
        clauses.extend([(-selector, int(data_field(x, degree)), zero),
                        (-selector, -int(data_field(y, degree)), zero)])
    current = selectors[0]
    fresh = third + 1
    for selector in selectors[1:]:
        clauses.extend([(-current, fresh, zero), (-selector, fresh, zero),
                        (current, selector, -fresh)])
        current = fresh
        fresh += 1
    clauses.append((current, zero, other))
    assert all(len(set(abs(v) for v in clause)) == 3 for clause in clauses)
    return (f"p cnf {fresh - 1} {len(clauses)}\n" +
            "".join(" ".join(map(str, clause)) + " 0\n" for clause in clauses)).encode()


def audit_physical_edits(degree):
    m = 1 << degree
    k = m // 2
    checks = 0
    for symbol in range(m):
        left = [symbol] * k
        old = proper_dimacs(left, left, degree)
        for index in range(k):
            for bit in range(degree):
                new = left.copy()
                new[index] ^= 1 << bit
                for edited in (proper_dimacs(left, new, degree), proper_dimacs(new, left, degree)):
                    assert len(old) == len(edited)
                    assert sum((a ^ b).bit_count() for a, b in zip(old, edited)) == 1
                    checks += 1
    return checks


def audit_prefixes():
    field = BinaryField(2, 0b111)
    m, k = field.size, field.size // 2
    basis = field.lagrange_column(k, 0)
    scale = [field.div(1, basis[i]) if i >= k else 1 for i in range(m)]
    messages = list(product(range(m), repeat=k))
    words = [tuple(field.mul(s, v) for s, v in zip(scale, field.evaluate(u)))
             for u in messages]
    normals = [a for a in product(range(m), repeat=k) if any(a)]
    for normal in normals:
        signature = [field.mul(normal[0], u[0]) ^ field.mul(normal[1], u[1])
                     for u in messages]
        free = sum(len({(z, word[i]) for z, word in zip(signature, words)}) == m**2
                   for i in range(m))
        assert free >= m - 1
    # All possible one-bit functions of the sixteen source messages.
    all_sources = (1 << len(messages)) - 1
    partners = [[sum(1 << j for j, other in enumerate(words)
                     if other[coord] == (word[coord] ^ 1)) for word in words]
                for coord in range(m)]
    worst_misses = 0
    for summary in range(all_sources + 1):
        misses = 0
        for row in partners:
            for j, possible in enumerate(row):
                same_summary = summary if (summary >> j) & 1 else all_sources ^ summary
                misses += not (possible & same_summary)
        worst_misses = max(worst_misses, misses)
        assert misses * k <= m * len(messages)
    return len(normals), all_sources + 1, worst_misses, m * len(messages)


if __name__ == "__main__":
    print("systematic codewords verified:", audit(2, 0b111), audit(3, 0b1011))
    print("single physical DIMACS bit edits verified:", audit_physical_edits(2) + audit_physical_edits(3))
    print("linear summaries, binary summaries, worst misses, tests:", audit_prefixes())
