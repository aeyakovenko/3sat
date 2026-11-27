"""Exhaust finite batches in the polynomial fingerprint for implicit-output coding."""

from itertools import combinations


def remainder(value, divisor):
    while value.bit_length() >= divisor.bit_length():
        value ^= divisor << (value.bit_length() - divisor.bit_length())
    return value


def first_irreducible(degree):
    for polynomial in range(1 << degree, 2 << degree):
        if all(remainder(polynomial, divisor) for divisor in
               range(2, 1 << (degree // 2 + 1))):
            return polynomial
    raise AssertionError("missing irreducible polynomial")


def multiply(left, right, modulus):
    product = 0
    while right:
        if right & 1:
            product ^= left
        left <<= 1
        right >>= 1
    return remainder(product, modulus)


def evaluate(word, alpha, modulus):
    # The initial coefficient 1 marks length, including leading zero bits.
    value = 1
    for bit in word:
        value = multiply(value, alpha, modulus) ^ int(bit)
    return value


def check(capacity, depth):
    words = [bin(i)[3:] for i in range(1, 1 << (capacity + 1))]
    field_degree = 2 * depth + (capacity + 1).bit_length() + 2
    field_size = 1 << field_degree
    modulus = first_irreducible(field_degree)
    values = {w: [evaluate(w, alpha, modulus) for alpha in range(field_size)]
              for w in words}
    collisions = {}
    for left, right in combinations(words, 2):
        roots = {alpha for alpha in range(field_size)
                 if values[left][alpha] == values[right][alpha]}
        difference = int("1" + left, 2) ^ int("1" + right, 2)
        assert len(roots) <= difference.bit_length() - 1
        collisions[left, right] = roots

    batch_count = bad_points = nonbinary_collisions = query_count = 0
    for size in range(0, min(1 << depth, len(words)) + 1):
        for batch in combinations(words, size):
            bad = set().union(*(collisions[pair] for pair in combinations(batch, 2)))
            assert len(bad) <= size * (size - 1) // 2 * capacity < field_size
            alpha = next(a for a in range(field_size) if a not in bad)
            table = {values[w][alpha]: w for w in batch}
            assert len(table) == size
            for word in batch:
                matches = [w for w in batch if values[w][alpha] == values[word][alpha]]
                for i in range(capacity + 1):
                    exists = any(i < len(w) for w in matches)
                    one = any(i < len(w) and w[i] == "1" for w in matches)
                    assert exists == (i < len(word))
                    assert one == (i < len(word) and word[i] == "1")
                    query_count += 1
            batch_count += 1
            bad_points += len(bad)
            nonbinary_collisions += len(bad - {0, 1})
    return batch_count, bad_points, nonbinary_collisions, query_count


if __name__ == "__main__":
    cases = [(cap, depth) for cap in (2, 3, 4)
             for depth in range(3 if cap < 4 else 2)]
    results = [check(cap, depth) for cap, depth in cases]
    batches, collisions, nonbinary, queries = map(sum, zip(*results))
    assert nonbinary > 0
    print(f"{batches} batches, {collisions} colliding batch/point pairs "
          f"({nonbinary} outside 0 and 1), {queries} position and range checks")
