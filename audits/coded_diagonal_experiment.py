"""Binary polynomial residues, the signed-list bound, and the priority construction."""

from itertools import combinations, product
from random import Random


def residue(polynomial, modulus):
    while polynomial.bit_length() >= modulus.bit_length():
        polynomial ^= modulus << (polynomial.bit_length() - modulus.bit_length())
    return polynomial


def irreducibles(degree):
    # Direct trial division suffices for the small experimental degrees.
    return [f for f in range(1 << degree, 2 << degree)
            if all(residue(f, d) for d in range(2, 2 << (degree // 2)))]


def binary_dot(left, right):
    return (left & right).bit_count() % 2


def make_code(bits, degree):
    moduli = irreducibles(degree)
    words = []
    for table in range(1 << bits):
        code = 0
        for f in moduli:
            value = residue(table, f)
            for mask in range(1 << degree):
                code = (code << 1) | binary_dot(mask, value)
        words.append(code)
    return words, moduli


def check_predictor(words, question_count, overlap, support, predictions):
    answered = support.bit_count()
    scores = [answered - 2 * ((word ^ predictions) & support).bit_count() for word in words]
    strong = 0
    for sign in (-1, 1):
        aligned = [sign * score for score in scores]
        for score in set(aligned):
            gap = score * score - answered * overlap
            if score > 0 and gap > 0:
                count = sum(value >= score for value in aligned)
                assert count * gap <= answered * (question_count - overlap)
        strong += sum(val > 0 and val * val > answered * overlap for val in aligned)
    return strong


def check_lists():
    bits, degree = 4, 3
    words, moduli = make_code(bits, degree)
    questions = len(moduli) << degree
    overlap = ((bits - 1) // degree) << degree
    for i, j in combinations(range(len(words)), 2):
        same_residues = sum(residue(i ^ j, f) == 0 for f in moduli)
        inner = questions - 2 * (words[i] ^ words[j]).bit_count()
        assert inner == same_residues << degree
        assert inner <= overlap
    all_questions = (1 << questions) - 1
    total = 1 << questions
    strongest = max(check_predictor(words, questions, overlap, all_questions, p)
                    for p in range(total))
    rng = Random(73156)
    partial = 4000
    for _ in range(partial):
        support = rng.getrandbits(questions)
        check_predictor(words, questions, overlap, support, rng.getrandbits(questions))
    assert strongest > 0
    print(f"Gram bounds passed for {total} total and {partial} partial predictors")

    # A quadratic bent function has the same absolute correlation with
    # every character on the four low mask bits, at every modulus.
    degree = 4
    words, moduli = make_code(4, degree)
    prediction = 0
    for _ in moduli:
        for mask in range(1 << degree):
            bit = (mask & 3 == 3) ^ (mask & 12 == 12)
            prediction = (prediction << 1) | bit
    questions = len(moduli) << degree
    for word in words:
        assert abs(questions - 2 * (word ^ prediction).bit_count()) * 4 == questions
    print("All 16 low-degree tables attain absolute correlation 1/4 with one predictor")


def check_tail_support():
    width = 10
    checked = 0
    for degree in (2, 3, 4):
        moduli = irreducibles(degree)
        for count in range(1, min(len(moduli), width // degree) + 1):
            for chosen in combinations(moduli, count):
                tail = degree * count
                def residues(y):
                    return tuple(residue(y, f) for f in chosen)
                last_powers = {residues(y << (width - tail)) for y in range(1 << tail)}
                full = {residues(y) for y in range(1 << width)}
                assert last_powers == full and len(full) == 1 << tail
                checked += 1
    print(f"High-degree tail realizes every residue tuple for {checked} modulus sets")


def span(rows):
    space = {0}
    for row in rows:
        space |= {v ^ row for v in space}
    return space


def check_priority(stages, width):
    rows = []
    equations = []
    for menu in stages:
        old = span(rows)
        for normal, wanted in menu:
            if normal not in old:
                rows.append(normal)
                equations.append((normal, 1 ^ wanted))
                break
    solution = next(y for y in range(1 << width)
                    if all(binary_dot(y, v) == a for v, a in equations))
    assert solution.bit_count() <= len(rows)
    for earlier_count, menu in enumerate(stages):
        if all(binary_dot(solution, v) == a for v, a in menu):
            assert len(span(v for v, _ in menu)) <= 1 << earlier_count


def check_priority_stages():
    claims = list(product(range(4), (0, 1)))
    menus = [tuple(c for i, c in enumerate(claims) if subset & (1 << i))
             for subset in range(1 << len(claims))]
    for stages in product(menus, repeat=2):
        check_priority(stages, 2)
    print(f"Priority construction passed all {len(menus) ** 2} pairs of two-bit claim menus")


if __name__ == "__main__":
    check_lists()
    check_tail_support()
    check_priority_stages()
