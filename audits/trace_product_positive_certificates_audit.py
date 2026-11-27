"""Exact GF(2) tests of the small positive-support polynomial spaces."""
from itertools import combinations

from trace_product_bias_audit import field


def support_code(m):
    """Kernel of evaluation on all zeros of Tr(uvw), using truth-vector columns."""
    dimension = 3*m
    q = 1 << m
    size = 1 << dimension
    table, trace = field(m)
    full = (1 << size) - 1
    ones = sum(1 << x for x in range(size)
               if trace[table[table[x % q][(x//q) % q]][x//(q*q)]])
    coords = [sum(1 << x for x in range(size) if x >> i & 1)
              for i in range(dimension)]
    pivots = {}
    kernel = []
    for deg in range(m+1):
        for variables in combinations(range(dimension), deg):
            values = full
            for i in variables:
                values &= coords[i]
            restricted = values & ~ones
            while restricted:
                leading = restricted.bit_length()
                if leading not in pivots:
                    pivots[leading] = restricted, values
                    break
                mask, lift = pivots[leading]
                restricted ^= mask
                values ^= lift
            if not restricted:
                assert values and (values & ~ones) == 0
                kernel.append(values)
    return size, kernel


def minimum_nonzero_weight(basis):
    if not basis:
        return None
    # Consecutive Gray-code words differ in bit index v_2(i).
    value = 0
    best = None
    for i in range(1, 1 << len(basis)):
        value ^= basis[(i & -i).bit_length() - 1]
        weight = value.bit_count()
        assert weight > 0
        best = weight if best is None else min(best, weight)
    return best


def main():
    expected = {1: (0, None), 2: (0, None), 3: (1, 196), 4: (13, 840)}
    for m in expected:
        size, basis = support_code(m)
        print(f"m={m}: kernel dimension {len(basis)}", flush=True)
        assert len(basis) <= 20
        least = minimum_nonzero_weight(basis)
        assert (len(basis), least) == expected[m]
        assert least is None or least * (1 << m) >= 2*size
        print(f"  minimum nonzero supported weight: {least}", flush=True)


if __name__ == "__main__":
    main()
