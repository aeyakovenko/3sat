"""Finite checks for component compression of multilinear Nullstellensatz identities."""

from collections import Counter
from itertools import product


def contributions(support, clause, modulus):
    """Return the nonzero coefficients of x^support times the violation polynomial."""
    terms = {support: 1}
    for literal in clause:
        bit = 1 << (abs(literal) - 1)
        expanded = Counter()
        for old, coefficient in terms.items():
            if literal > 0:
                expanded[old] += coefficient
                expanded[old | bit] -= coefficient
            else:
                expanded[old | bit] += coefficient
        terms = {s: c % modulus for s, c in expanded.items() if c % modulus}
    return terms


def combine(scaled_terms, modulus):
    total = Counter()
    for polynomial, scalar in scaled_terms:
        for support, coefficient in polynomial.items():
            total[support] += scalar * coefficient
    return {s: c % modulus for s, c in total.items() if c % modulus}


def root_component(rows, modulus):
    """Extract a certificate of parent pointers and symmetric differences."""
    adjacency = [[] for _ in range(len(rows) + 1)]
    first_row = {0: 0}  # Slot zero contributes the extra constant -1.
    supports = [0]
    for index, (support, clause, scalar) in enumerate(rows, 1):
        supports.append(support)
        if not scalar:
            continue
        for output in contributions(support, clause, modulus):
            if output in first_row:
                neighbor = first_row[output]
                adjacency[neighbor].append(index)
                adjacency[index].append(neighbor)
            else:
                first_row[output] = index

    stack = [0]
    seen = {0: 0}
    records = []
    while stack:
        parent = stack.pop()
        for child in adjacency[parent]:
            if child in seen:
                continue
            difference = supports[parent] ^ supports[child]
            assert difference.bit_count() <= 6
            _, clause, scalar = rows[child - 1]
            records.append((seen[parent], difference, clause, scalar))
            seen[child] = len(records)
            stack.append(child)
    return records


def check_records(records, modulus):
    supports = [0]
    rows = []
    for parent, difference, clause, coefficient in records:
        if not 0 <= parent < len(supports) or difference.bit_count() > 6:
            return False
        support = supports[parent] ^ difference
        supports.append(support)
        rows.append((contributions(support, clause, modulus), coefficient))
    return combine(rows, modulus) == {0: 1}


def unit_in_span(polynomials, variables, prime):
    """Row-reduce two-coordinate vectors for one-variable projected identities."""
    basis = {}
    for polynomial in polynomials:
        vector = [polynomial.get(0, 0), polynomial.get(variables, 0)]
        for pivot in range(2):
            if not vector[pivot]:
                continue
            if pivot in basis:
                factor = vector[pivot]
                vector = [(a - factor * b) % prime for a, b in zip(vector, basis[pivot])]
            else:
                scale = pow(vector[pivot], -1, prime)
                basis[pivot] = [scale * a % prime for a in vector]
                break
    vector = [1, 0]
    for pivot in sorted(basis):
        factor = vector[pivot]
        vector = [(a - factor * b) % prime for a, b in zip(vector, basis[pivot])]
    return vector == [0, 0]


def exhaustive_pairs(prime):
    options = []
    for variable in (1, 2):
        # Over F2 enumerate all multipliers. Over F3 use both cross-side choices.
        masks = range(4) if prime == 2 else [0, 1 << (2 - variable)]
        for sign in (-1, 1):
            for support in masks:
                options.append((support, (sign * variable,)))
    polys = [contributions(s, c, prime) for s, c in options]
    checked = disconnected = possibly_mixed = 0
    for coefficients in product(range(prime), repeat=len(options)):
        if combine(zip(polys, coefficients), prime) != {0: 1}:
            continue
        rows = [(s, c, a) for (s, c), a in zip(options, coefficients) if a]
        records = root_component(rows, prime)
        assert check_records(records, prime)
        if len(records) < len(rows):
            disconnected += 1
        sides = {1: [], 2: []}
        for support, clause, _ in rows:
            variable = abs(clause[0])
            projected = support & (1 << (variable - 1))
            sides[variable].append(contributions(projected, clause, prime))
        assert any(unit_in_span(polys, 1 << (v - 1), prime) for v, polys in sides.items())
        if all(sides.values()) and any(s & (1 << (2 - abs(c[0]))) for s, c, _ in rows):
            possibly_mixed += 1
        checked += 1
    assert disconnected and possibly_mixed
    return checked, disconnected, possibly_mixed


def check_local_expansions():
    checked = 0
    for width in range(4):
        for clause in product((1, -1, 2, -2, 3, -3), repeat=width):
            for support in range(8):
                for modulus in (2, 3, 4):
                    terms = contributions(support, clause, modulus)
                    for assignment in range(8):
                        value = sum(c for s, c in terms.items() if s & assignment == s)
                        violates = all(bool(assignment & (1 << (abs(l) - 1))) != (l > 0)
                                       for l in clause)
                        expected = int((support & assignment) == support and violates)
                        assert value % modulus == expected
                    checked += 1
    return checked


def check_wide_chain(length):
    rows = [(0, (1,), 1)]
    for i in range(1, length):
        rows.append(((1 << (i - 1)) - 1, (-i, i + 1), 1))
    rows.append(((1 << (length - 1)) - 1, (-length,), 1))
    for modulus in (2, 3, 4, 101):
        records = root_component(rows, modulus)
        assert len(records) == len(rows)
        assert check_records(records, modulus)
        assert not check_records(records[:-1], modulus)
        assert sum(d.bit_count() for _, d, _, _ in records) == length - 1
    names = sum(s.bit_count() for s, _, _ in rows)
    assert names == length * (length - 1) // 2
    return len(rows), names, length - 1


def check_product_scans(dimension):
    """Exhaust every F2 multilinear polynomial on this many variables."""
    domain = range(1 << dimension)
    checked = 0
    tight = 0
    for polynomial in range(1 << len(domain)):
        inputs = [s for s in domain if polynomial & (1 << s)]
        size = len(inputs)
        if not size:
            continue
        total_collisions = 0
        total_output = 0
        for i in range(dimension):
            bit = 1 << i
            image = 0
            collisions = 0
            for support in inputs:
                image ^= 1 << (support | bit)
                if not support & bit and polynomial & (1 << (support | bit)):
                    collisions += 1
            assert image.bit_count() == size - 2 * collisions
            total_collisions += collisions
            total_output += image.bit_count()
        assert size * dimension == total_output + 2 * total_collisions
        # Compare 2e to a log2(a) with exact integers.
        assert 2 ** (2 * total_collisions) <= size ** size
        tight += int(2 ** (2 * total_collisions) == size ** size)
        checked += 1
    assert tight
    return checked, tight


class NormalizedTrie:
    """Exact persistent handles for vectors over a fixed prime field."""

    zero = (0, 0)
    nonzero_leaf = 1

    def __init__(self, prime):
        self.prime = prime
        self.nodes = [None, None]
        self.identifiers = {}

    def scale(self, handle, factor):
        scalar, identifier = handle
        result = scalar * factor % self.prime
        return (result, identifier) if result else self.zero

    def join(self, height, left, right):
        leading = left[0] or right[0]
        if not leading:
            return self.zero
        inverse = pow(leading, -1, self.prime)
        key = (height, self.scale(left, inverse), self.scale(right, inverse))
        identifier = self.identifiers.get(key)
        if identifier is None:
            identifier = len(self.nodes)
            self.identifiers[key] = identifier
            self.nodes.append(key)
        return leading, identifier

    def add_entry(self, handle, height, index, increment):
        scalar, identifier = handle
        if not height:
            return self.scale((1, self.nonzero_leaf), scalar + increment)
        left = right = self.zero
        if identifier:
            stored_height, relative_left, relative_right = self.nodes[identifier]
            assert stored_height == height
            left = self.scale(relative_left, scalar)
            right = self.scale(relative_right, scalar)
        half = 1 << (height - 1)
        if index < half:
            left = self.add_entry(left, height - 1, index, increment)
        else:
            right = self.add_entry(right, height - 1, index - half, increment)
        return self.join(height, left, right)

    def build(self, coefficients, order):
        handle = self.zero
        height = (len(coefficients) - 1).bit_length()
        for index in order:
            if coefficients[index]:
                handle = self.add_entry(handle, height, index, coefficients[index])
        return handle


def check_prime_field(prime):
    """Compare persistent updates, linear rules, and product charges to dense arithmetic."""
    trie = NormalizedTrie(prime)
    vectors = list(product(range(prime), repeat=4))
    handles = {v: trie.build(v, range(4)) for v in vectors}
    assert len(set(handles.values())) == len(handles)
    mixed = 0
    for vector, handle in handles.items():
        assert trie.build(vector, reversed(range(4))) == handle
        for multiple in range(prime):
            expect = tuple(c * multiple % prime for c in vector)
            assert trie.scale(handle, multiple) == handles[expect]
        for index in range(4):
            for increment in range(prime):
                updated = list(vector)
                updated[index] = (updated[index] + increment) % prime
                assert trie.add_entry(handle, 2, index, increment) == handles[tuple(updated)]
        size = sum(c != 0 for c in vector)
        for bit in (1, 2):
            output = [0] * 4
            cancelled = retained = 0
            for mask, c in enumerate(vector):
                output[mask | bit] = (output[mask | bit] + c) % prime
                if not mask & bit and c and vector[mask | bit]:
                    if (c + vector[mask | bit]) % prime:
                        retained += 1
                    else:
                        cancelled += 1
            assert sum(c != 0 for c in output) == size - 2 * cancelled - retained
            mixed += int(bool(cancelled and retained))

    # Exhaust every pair of two-coefficient vectors and every choice of rule scalars.
    # Their four-coordinate embeddings overlap in two slots and share subtrees.
    checks = 0
    for first, second in product(range(prime), repeat=2):
        a = (first, second, second, 0)
        for third, fourth in product(range(prime), repeat=2):
            b = (third, 0, fourth, fourth)
            for alpha, beta in product(range(prime), repeat=2):
                output = tuple((alpha*x + beta*y) % prime for x, y in zip(a, b))
                updated = trie.scale(handles[b], -beta)
                for index, value in enumerate(output):
                    if value:
                        updated = trie.add_entry(updated, 2, index, value)
                assert updated == trie.scale(handles[a], alpha)
                assert trie.add_entry(updated, 2, 0, 1) != trie.scale(handles[a], alpha)
                checks += 1
    assert mixed
    return len(handles), checks, mixed


if __name__ == "__main__":
    print("Width-three expansions checked against all assignments:", check_local_expansions())
    for p in (2, 3):
        total, discarded, mixed = exhaustive_pairs(p)
        print(f"F_{p}: {total} identities, {discarded} pruned, {mixed} with cross-side multipliers")
    print("Chain (rows, printed variable names, support flips):", check_wide_chain(100))
    print("F2 polynomials (checked, tight edge bound):", check_product_scans(4))
    for p in (3, 5):
        print(f"F_{p} (distinct roots, linear combinations, mixed products):", check_prime_field(p))
