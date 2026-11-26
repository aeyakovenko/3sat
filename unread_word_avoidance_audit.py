"""Exhaust all observed-word restrictions of the four-symbol GF(4) index."""

from itertools import combinations, product

SYMBOLS = range(4)
WORD_BITS = 2


def multiply(a, b):
    """Multiply degree-one binary polynomials modulo X²+X+1."""
    shifted = (a << 1) ^ (0b111 if a & 2 else 0)
    return (a if b & 1 else 0) ^ (shifted if b & 2 else 0)


def output(words, length):
    powers = [1] * len(words)
    packed = 0
    for shift in range(0, length, WORD_BITS):
        moment = 0
        for alpha, value in enumerate(words):
            moment ^= multiply(value, powers[alpha])
            powers[alpha] = multiply(powers[alpha], alpha)
        packed |= moment << shift
    return packed & ((1 << length) - 1)


def avoid(observed, unread, length):
    """Output k-1 zero symbols and the retained bits of v+1."""
    value = 0
    for alpha, cell in observed.items():
        polynomial = 1
        for root in unread:
            polynomial = multiply(polynomial, alpha ^ root)
        value ^= multiply(cell, polynomial)
    packed = (value ^ 1) << (WORD_BITS * len(unread))
    return packed & ((1 << length) - 1)


def main():
    indices = list(product(SYMBOLS, repeat=4))
    restrictions = 0
    avoiders_checked = 0
    for length in range(1, 9):
        output_words = (length + WORD_BITS - 1) // WORD_BITS
        values = [output(words, length) for words in indices]
        for free_count in range(5):
            for unread in combinations(SYMBOLS, free_count):
                locations = tuple(j for j in SYMBOLS if j not in unread)
                completions = {}
                for words, value in zip(indices, values):
                    observed_values = tuple(words[j] for j in locations)
                    completions.setdefault(observed_values, set()).add(value)
                assert len(completions) == 4 ** len(locations)
                for observed_values, image in completions.items():
                    assert len(image) == 1 << min(length, WORD_BITS * free_count)
                    restrictions += 1
                    if free_count == output_words - 1:
                        observed = dict(zip(locations, observed_values))
                        assert avoid(observed, unread, length) not in image
                        avoiders_checked += 1
    print(f"GF(4), 4 words, lengths 1..8: {restrictions} exact images")
    print(f"{avoiders_checked} matching missing outputs checked")


if __name__ == "__main__":
    main()
