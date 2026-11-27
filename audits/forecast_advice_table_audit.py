"""Check the exact extension criterion for small frozen Boolean tables."""

from itertools import combinations


def first_missing_extension(old, width, candidates):
    possible = 1 << width
    admitted_highs = {
        value >> width for value in candidates if value % possible == old
    }
    for high in range(possible):
        if high not in admitted_highs:
            return old + possible * high
    return None


def audit_extensions(width):
    possible = 1 << width
    tables = range(possible**2)
    checked = 0
    for count in range(len(tables) + 1):
        for selected in combinations(tables, count):
            candidates = set(selected)
            for old in range(possible):
                answer = first_missing_extension(old, width, candidates)
                expected = next(
                    (word for word in tables if word % possible == old and word not in candidates),
                    None,
                )
                assert answer == expected
                if count < possible:
                    assert answer is not None
                checked += 1
    return checked


def audit_padding():
    checked = 0
    for n in range(32, 257):
        padded_length = 1 << ((n + 3) // 4)
        assert padded_length >= 2 * n + 1
        for width in (1 << (n - 1), (1 << n) - 1):
            assert padded_length**4 <= 16 * width
            assert width < padded_length**4
            checked += 1
    return checked


if __name__ == "__main__":
    instances = sum(audit_extensions(width) for width in (1, 2))
    assert first_missing_extension(0, 1, (0, 2)) is None
    print(f"{instances} frozen tables and candidate families; {audit_padding()} padded-width endpoints")
