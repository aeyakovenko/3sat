"""Exhaust model-support fingerprints and scalar amplification in GF(8) and GF(9)."""

from itertools import product


class SmallField:
    def __init__(self, prime, modulus):
        self.p = prime
        self.d = len(modulus) - 1
        self.q = prime ** self.d
        self.modulus = modulus
        self.digits = [tuple((a // prime**i) % prime for i in range(self.d))
                       for a in range(self.q)]
        self.add = [[self.encode([x + y for x, y in zip(a, b)])
                     for b in self.digits] for a in self.digits]
        self.mul = [[self.multiply(a, b) for b in self.digits] for a in self.digits]

    def encode(self, coefficients):
        return sum((value % self.p) * self.p**i for i, value in enumerate(coefficients))

    def multiply(self, a, b):
        c = [0] * (2 * self.d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i+j] += x * y
        for i in reversed(range(self.d, len(c))):
            leading = c[i] % self.p
            for j, coef in enumerate(self.modulus):
                c[i - self.d + j] -= leading * coef
        return self.encode(c[:self.d])

    def primitive_powers(self):
        for g in range(1, self.q):
            powers = [1]
            while len(powers) < self.q - 1:
                nxt = self.mul[powers[-1]][g]
                if nxt == 1:
                    break
                powers.append(nxt)
            if len(set(powers)) == self.q - 1 and self.mul[powers[-1]][g] == 1:
                return powers
        raise AssertionError("No primitive element found")


def audit(field, variables=3):
    p, q = field.p, field.q
    powers = field.primitive_powers()
    probes = [[sum(x * y for x, y in zip(a, b)) % p for b in field.digits]
              for a in field.digits]
    for state in range(1, q):
        assert sum(probe[state] != 0 for probe in probes) == q - q // p
    supports = 1 << (1 << variables)
    nonzero_counts = [0] * supports
    fixed_trials = []
    uncovered = set(range(1, supports))
    for exponents in product(range(q - 1), repeat=variables):
        monomials = []
        for model in range(1 << variables):
            weight, exponent = 1, 0
            for i, e in enumerate(exponents):
                if model & (1 << i):
                    weight = field.mul[weight][powers[e]]
                    exponent += e
            assert weight == powers[exponent % (q - 1)]
            monomials.append(weight)
        values = [0] * supports
        for support in range(1, supports):
            last = support & -support
            values[support] = field.add[values[support ^ last]][monomials[last.bit_length()-1]]
            nonzero_counts[support] += int(values[support] != 0)
        for probe in probes:
            newly_hit = {support for support in uncovered if probe[values[support]]}
            if newly_hit:
                fixed_trials.append([probe[value] for value in values])
                uncovered.difference_update(newly_hit)
    point_count = (q - 1) ** variables
    assert min(nonzero_counts[1:]) * (q - 1) >= point_count * (q - 1 - variables)
    assert nonzero_counts[0] == 0 and not uncovered
    for support in range(supports):
        product_of_complements = 1
        for scalars in fixed_trials:
            product_of_complements *= 1 - pow(scalars[support], p - 1, p)
        assert (1 - product_of_complements) % p == int(support != 0)
    print(f"GF({q}) over GF({p}): {supports} model sets, {point_count} nonzero "
          f"evaluation points, {q} linear projections; minimum nonzero point "
          f"count {min(nonzero_counts[1:])}; {len(fixed_trials)} fixed probes "
          "give exact scalar decision on every set.")


def audit_unique_minimum(field):
    variables = 2
    supports = 1 << (1 << variables)
    isolated_counts = [0] * supports
    digit_base = 1 << (2 * variables).bit_length()
    assert field.q - 1 >= 4 * variables**2
    for weights in product(range(1, 2 * variables + 1), repeat=variables):
        model_weights = [sum(w for i, w in enumerate(weights) if model & (1 << i))
                         for model in range(1 << variables)]
        minima = []
        for support in range(supports):
            accepted = [w for i, w in enumerate(model_weights) if support & (1 << i)]
            unique = bool(accepted) and accepted.count(min(accepted)) == 1
            minima.append(unique)
            isolated_counts[support] += int(unique)
        nonzero = [0] * supports
        for y in range(1, field.q):
            powers = [1]
            for _ in range(max(2 * variables**2, digit_base * (digit_base - 1))):
                powers.append(field.mul[powers[-1]][y])
            low = [powers[i] for i in range(digit_base)]
            high = [powers[i * digit_base] for i in range(digit_base)]
            values = [0] * supports
            for support in range(1, supports):
                last = support & -support
                exponent = model_weights[last.bit_length() - 1]
                upper, lower = divmod(exponent, digit_base)
                split_power = field.mul[low[lower]][high[upper]]
                assert split_power == powers[exponent]
                values[support] = field.add[values[support ^ last]][split_power]
                nonzero[support] += int(values[support] != 0)
        for support, unique in enumerate(minima):
            if unique:
                assert nonzero[support] >= field.q - 1 - max(model_weights)
    weight_choices = (2 * variables) ** variables
    assert 2 * min(isolated_counts[1:]) >= weight_choices
    print(f"GF({field.q}) unique minimum: {supports} supports, {weight_choices} "
          f"weight vectors, {field.q-1} evaluation points; isolation and split "
          "table checks passed.")


if __name__ == "__main__":
    audit(SmallField(2, [1, 1, 0, 1]))
    audit(SmallField(3, [1, 0, 1]))
    audit_unique_minimum(SmallField(2, [1, 0, 1, 0, 0, 1]))
    audit_unique_minimum(SmallField(3, [1, -1, 0, 1]))
