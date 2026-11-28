"""Check bounded integer fingerprints and finite-field response dimensions."""
from itertools import product, combinations_with_replacement
from fractions import Fraction


def vector(matrix, column):
    return tuple(sum(a*b for a,b in zip(row,column)) for row in matrix)


def matrix(flat, d):
    return tuple(tuple(flat[i*d:(i+1)*d]) for i in range(d))


def integer_grid():
    mats=[matrix(v,2) for v in product((-1,0,1),repeat=4)]
    checked=0
    for A in mats:
        for B in mats:
            cols=tuple(zip(*B))
            true=tuple(zip(*(vector(A,c) for c in cols)))
            fingerprint=vector(A,vector(B,(1,5)))
            for C in mats:
                assert (fingerprint==vector(C,(1,5))) == (C==true)
                checked+=1
    return checked


def field_tests():
    count=0
    for d in range(1,6):
        for k in range(1,min(4,d)+1):
            for basis in combinations_with_replacement(range(1<<d),k):
                kernel=[x for x in range(1<<d)
                        if all((v&x).bit_count()%2==0 for v in basis)]
                assert len(kernel)>=1<<(d-k)
                count+=1
        assert all(any((x>>j)&1 for j in range(d)) for x in range(1,1<<d))
    return count


def mod_extension_sum(left, right):
    return tuple(a+b for a,b in zip(left,right))


def shift_alpha(x):
    return (2*x[-1],*x[:-1])


def algebraic_example():
    checks=0
    for d in range(2,6):
        zero=(0,)*d
        one=(1,)+(0,)*(d-1)
        alpha=shift_alpha(one)
        # Read coordinates symbolically in Q[X]/(X^d-2).
        assert mod_extension_sum(alpha,shift_alpha(tuple(-i for i in one)))==zero
        for e in product((-1,0,1),repeat=d):
            value=zero
            for coeff in reversed(e):
                value=mod_extension_sum(shift_alpha(value),(Fraction(coeff,7),*zero[1:]))
            assert (value==zero)==(not any(e))
            checks+=1
    return checks


def symmetric_plane_forms(p):
    """Exhaust pairs of binary forms and all restricted lines by projective points."""
    points = [(1, y) for y in range(p)] + [(0, 1)]
    forms = list(product(range(p), repeat=3))
    zero_sets = {}
    for a, b, c in forms:
        zero_sets[a, b, c] = {i for i, (x, y) in enumerate(points)
                              if (a*x*x + 2*b*x*y + c*y*y) % p == 0}
    pairs = 0
    anisotropic_pairs = 0
    for left, right in combinations_with_replacement(forms, 2):
        pairs += 1
        if zero_sets[left].isdisjoint(zero_sets[right]):
            anisotropic_pairs += 1
            for u, v in points:
                a, b, c = ((u*x + v*y) % p for x, y in zip(left, right))
                if (a*c - b*b) % p:
                    break
            else:
                raise AssertionError((p, left, right))
        # Every one-dimensional restriction needs exactly one nonzero value.
        for i in range(p+1):
            if i not in zero_sets[left] or i not in zero_sets[right]:
                assert any(i not in zero_sets[Q] for Q in (left, right))
    return pairs, anisotropic_pairs


def nonconstant_bit_top_coefficients(p):
    """Interpolate the top coefficient using Lagrange denominators on F_p."""
    denominators = []
    for a in range(p):
        value = 1
        for b in range(p):
            if b != a:
                value = (value * (a-b)) % p
        denominators.append(pow(value, -1, p))
    for bit_values in range(1, 2**p-1):
        coefficient = sum(denominators[a] for a in range(p) if bit_values >> a & 1) % p
        assert coefficient == -bit_values.bit_count() % p and coefficient != 0
    return 2**p-2


def unit_propagation(clauses):
    assignments = {}
    while clauses:
        unit = next((clause[0] for clause in clauses if len(clause) == 1), None)
        if unit is None:
            var = abs(clauses[0][0])
            return (unit_propagation(clauses + [(var,)]) or
                    unit_propagation(clauses + [(-var,)]))
        var, value = abs(unit), unit > 0
        if var in assignments and assignments[var] != value:
            return False
        assignments[var] = value
        simplified = []
        for clause in clauses:
            if unit in clause:
                continue
            updated = tuple(literal for literal in clause if literal != -unit)
            if not updated:
                return False
            simplified.append(updated)
        clauses = simplified
    return True


def decoder_formula(p, h, inputs):
    """Small truth-table version of the guarded arithmetic with fixed signs."""
    b = (p-1).bit_length()
    ids = {}
    clauses = []

    def fresh(key):
        if key not in ids:
            ids[key] = len(ids) + 1
        return ids[key]

    def append(clause):
        # Existentially split each long clause into width-three clauses.
        while len(clause) > 3:
            aux = fresh(('aux', len(clauses)))
            clauses.append((*clause[:2], aux))
            clause = (-aux, *clause[2:])
        clauses.append(clause)

    def pin(var, bit):
        append((var if bit else -var,))

    for a in range(0, p, h):
        pin(fresh(('marker', a)), 1)
        for t in range(b):
            pin(fresh(('value', t, a)), (a >> t) & 1)
    X = [[fresh(('decoded', i, t)) for t in range(b)] for i in range(len(inputs))]
    for i, x in enumerate(inputs):
        for k in range(h):
            v = (x+k) % p
            marker = fresh(('marker', v))
            bits = [fresh(('value', t, v)) for t in range(b)]
            for stored in range(1 << b):
                guard = [-marker] + [(-var if stored >> t & 1 else var)
                                     for t, var in enumerate(bits)]
                if stored >= p:
                    append(tuple(guard))
                    continue
                decoded = (stored-k) % p
                for t, var in enumerate(X[i]):
                    append((*guard, var if decoded >> t & 1 else -var))
    return clauses, X


def guarded_alias_checks():
    count = 0
    for p, h in ((2, 1), (3, 2), (5, 2)):
        for inputs in product(range(p), repeat=2):
            clauses, decoded = decoder_formula(p, h, inputs)
            assert all(1 <= len(clause) <= 3 for clause in clauses)
            for proposed in product(range(p), repeat=2):
                pins = [(var if proposed[i] >> t & 1 else -var,)
                        for i, bits in enumerate(decoded) for t, var in enumerate(bits)]
                assert unit_propagation(clauses + pins) == (inputs == proposed)
                count += 1
    return count


def sparse_access_transcripts(p):
    count = 0
    for h in range(1, p+1):
        table = {a: a//h + 1 for a in range(0, p, h)}
        transcripts = set()
        for x in range(p):
            for k in range(h):
                a = (x+k) % p
                index = table.get(a, 0)
                if index:
                    break
            else:
                raise AssertionError((p, h, x))
            decoded = a-k + (p if a == 0 and k else 0)
            assert decoded == x
            parity = (a % 2) ^ (k % 2) ^ int(a == 0 and k > 0 and p % 2 == 1)
            assert parity == x % 2
            transcripts.add((k, index))
            count += 1
        assert len(transcripts) == p
    return count


if __name__=='__main__':
    print('integer triples:',integer_grid())
    print('binary checksum collections:',field_tests())
    print('exact rational residuals in an algebraic power basis:',algebraic_example())
    for prime in (3, 5, 7):
        pairs, anisotropic = symmetric_plane_forms(prime)
        print(f'F_{prime} symmetric plane-form pairs: {pairs}, '
              f'with no common nonzero isotropic vector: {anisotropic}')
    print('top coefficients of nonconstant bits:',
          sum(nonconstant_bit_top_coefficients(p) for p in (2, 3, 5, 7, 11, 13)))
    print('ordinary 3-CNF guarded alias decisions:', guarded_alias_checks())
    print('sparse access parity and transcripts:',
          sum(sparse_access_transcripts(p) for p in (2, 3, 5, 7, 11, 13, 17, 31, 61, 97)))
