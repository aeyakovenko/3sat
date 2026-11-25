"""Check weighted satisfiability of local relations on loops and directed cycles."""

from itertools import product


def allowed(relation, x, y):
    return (relation >> (2*x + y)) & 1


def satisfiable_cycle(labels, domain):
    for states in product(domain, repeat=len(labels)):
        if all((states[i], states[(i + 1) % len(states)]) in rel
               for i, rel in enumerate(labels)):
            return True
    return False


def check_boolean_menus():
    loop = [any(allowed(r, x, x) for x in (0, 1)) for r in range(16)]
    cycle = [[any(allowed(r, x, y) and allowed(s, y, x)
                  for x, y in product((0, 1), repeat=2))
              for s in range(16)] for r in range(16)]
    differences = 0
    for mask in range(1 << 16):
        menu = [r for r in range(16) if mask & (1 << r)]
        loops_value = sum(loop[r] for r in menu) ** 2 % 2
        cycle_value = sum(cycle[r][s] for r, s in product(menu, repeat=2)) % 2
        assert loops_value ^ cycle_value == int(6 in menu)
        differences += loops_value != cycle_value
    return differences


def check_prime_cycles():
    domain = range(3)
    # A directed order, a constant, and equality each preserve minimum.
    predicates = [lambda a, b: a <= b, lambda a, b: a == 1, lambda a, b: a == b]
    relations = [{(a, b) for a, b in product(domain, repeat=2) if pred(a, b)}
                 for pred in predicates]
    tests = 0
    for modulus, degree in ((2, 2), (2, 4), (3, 3), (5, 5)):
        monomials = []
        for indices in product(range(len(relations)), repeat=degree):
            if satisfiable_cycle([relations[i] for i in indices], domain):
                monomials.append(indices)
        for coefficients in product(range(modulus), repeat=len(relations)):
            total = 0
            for indices in monomials:
                term = 1
                for index in indices:
                    term *= coefficients[index]
                total += term
            loop_sum = sum(c for c, r in zip(coefficients, relations)
                           if any((a, a) in r for a in domain))
            assert total % modulus == pow(loop_sum, degree, modulus)
            tests += 1
    return tests


if __name__ == "__main__":
    count = check_boolean_menus()
    print(f"65,536 Boolean menus, {count:,} distinguished the transposition")
    print(f"{check_prime_cycles()} weighted prime-cycle cases")
