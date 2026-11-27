from itertools import permutations, product


def sparse_equal(left, right, radius):
    assert len(left) == len(right)
    mismatches = [(a, b) for a, b in zip(left, right) if a != b]
    left_errors = sorted(a for a, _ in mismatches)
    right_errors = sorted(b for _, b in mismatches)
    return len(mismatches) <= radius and left_errors == right_errors


def audit_cancellation():
    cases = 0
    for length in range(5):
        arrays = tuple(product(range(3), repeat=length))
        for left, right in product(arrays, repeat=2):
            distance = sum(a != b for a, b in zip(left, right))
            for radius in range(length + 1):
                expected = distance <= radius and sorted(left) == sorted(right)
                assert sparse_equal(left, right, radius) == expected
                cases += 1
    return cases


# Each row is (bank, address, unique time slot, operation, word).
def rows_for(words, guesses):
    left, right, seen = guesses
    return (
        (0, 0, 0, "init", words[0]),
        (0, 1, 1, "init", words[1]),
        (0, 0, 2, "read", left),
        (0, 1, 3, "read", right),
        (1, left, 4, "write", 1),
        (1, right, 5, "read", seen),
    )


def valid_sorted_memory(rows):
    key = None
    previous_order = None
    word = 0
    for bank, address, time, operation, value in rows:
        order = bank, address, time
        if previous_order is not None and not previous_order < order:
            return False
        previous_order = order
        if key != (bank, address):
            key = bank, address
            word = 0
        if operation in ("init", "write"):
            word = value
        elif value != word:
            return False
    return True


def audit_transcripts():
    cases = 0
    for words in product(range(2), repeat=2):
        for template in (tuple(range(6)), tuple(reversed(range(6)))):
            counts = [0] * 7
            for guesses in product(range(2), repeat=3):
                chronological = rows_for(words, guesses)
                predicted = tuple(chronological[i] for i in template)
                for candidate in permutations(chronological):
                    cases += 1
                    if not guesses[-1] or not valid_sorted_memory(candidate):
                        continue
                    for radius in range(7):
                        counts[radius] += sparse_equal(predicted, candidate, radius)
            true_rows = rows_for(words, (*words, int(words[0] == words[1])))
            true_order = sorted(true_rows)
            distance = sum(true_rows[i] != b for i, b in zip(template, true_order))
            expected = [int(words[0] == words[1] and distance <= r) for r in range(7)]
            assert counts == expected
    return cases


if __name__ == "__main__":
    print(f"{audit_cancellation()} array/radius tests")
    print(f"{audit_transcripts()} candidate transcript and template tests")
