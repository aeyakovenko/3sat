"""Exhaust short native instruction trees on small cyclic selector promises."""
from functools import cache, reduce
from itertools import product
from operator import xor

from ramsey_dimacs_word_audit import calculate


def cover(value, length):
    mask = (1 << length) - 1
    rotated = ((value << 1) | (value >> (length - 1))) & mask
    return (value | rotated) == mask


def subdivide(value, length, index, method):
    left = (value >> index) & 1
    right = (value >> ((index + 1) % length)) & 1
    new_bit = left ^ right if method == "xor" else left | right
    low = (1 << (index + 1)) - 1
    return (value & low) | (new_bit << (index + 1)) | ((value & ~low) << 1)


def feasible(files, length, width, budget):
    """Track complete register columns and writable memory on the given files."""
    values = 1 << width
    universe = (1 << len(files)) - 1
    target = sum(1 << i for i, file in enumerate(files) if cover(file, length))
    constants = tuple((v,) * len(files) for v in range(values))
    memory = tuple(tuple((file >> (width * address)) % values for file in files)
                   for address in range(values))
    arithmetic = {
        (a, b): calculate(a, b, width) + (
            a // b if b else 0, a // b if b else values - 1,
            a % b if b else 0, a % b if b else a,
        ) for a, b in product(range(values), repeat=2)
    }

    @cache
    def op_results(left, right):
        return frozenset(zip(*(arithmetic[pair] for pair in zip(left, right))))

    @cache
    def compare(left, right):
        masks = [0, 0, 0]
        sign = values // 2
        for i, (a, b) in enumerate(zip(left, right)):
            for j, yes in enumerate((a == b, a < b, (a ^ sign) < (b ^ sign))):
                if yes:
                    masks[j] |= 1 << i
        return masks

    @cache
    def cuts(registers):
        return frozenset(cut for a, b in product(registers, repeat=2)
                         for cut in compare(a, b))

    @cache
    def loads(registers, mem):
        return frozenset(tuple(mem[address][i] for i, address in enumerate(addresses))
                         for addresses in registers)

    @cache
    def next_registers(registers, mem):
        result = set()
        for a, b in product(registers, repeat=2):
            result.update(op_results(a, b))
        result.update(loads(registers, mem))
        return result.difference(registers)

    @cache
    def search(remaining, domain, registers, mem):
        positive = domain & target
        negative = domain & ~target
        if not positive or not negative:
            return True
        if remaining == 0:
            return False
        comparisons = cuts(registers)
        if any((domain & cut) in (positive, negative) for cut in comparisons):
            return True
        if remaining == 1:
            return False
        if remaining == 2:
            # Without a load, indistinguishable register rows stay identical.
            # When an opposite-label pair agrees, the first of two instructions
            # must load, since the final instruction has to branch.
            variables = [v for v in registers if v not in constants]
            positive_rows = {tuple(v[i] for v in variables) for i in range(len(files))
                             if (positive >> i) & 1}
            must_load = any(tuple(v[i] for v in variables) in positive_rows
                            for i in range(len(files)) if (negative >> i) & 1)
            if not must_load:
                def one_guard(part):
                    return any(((c ^ target) & part) in (0, part) for c in comparisons)
                if any(one_guard(domain & c) and one_guard(domain & ~c) for c in comparisons):
                    return True
            results = loads(registers, mem) if must_load else next_registers(registers, mem)
            for value in results:
                for other in registers:
                    for a, b in ((other, value), (value, other)):
                        if any((domain & c) in (positive, negative) for c in compare(a, b)):
                            return True
            return False
        for cut in comparisons:
            yes, no = domain & cut, domain & ~cut
            if (yes and no and search(remaining - 1, yes, registers, mem)
                    and search(remaining - 1, no, registers, mem)):
                return True
        for column in next_registers(registers, mem):
            enlarged = tuple(sorted((*registers, column)))
            if search(remaining - 1, domain, enlarged, mem):
                return True
        if remaining >= 3:
            for addresses, data in product(registers, repeat=2):
                updated = tuple(
                    tuple(data[i] if address == j else cell[i]
                          for i, address in enumerate(addresses))
                    for j, cell in enumerate(mem)
                )
                if updated != mem and search(remaining - 1, domain, registers, updated):
                    return True
        return False

    result = search(budget, universe, constants, memory)
    # Each call handles an independent promise. Release its finite search tables.
    for fn in (search, next_registers, loads, cuts, compare, op_results):
        fn.cache_clear()
    return result


def upper_on_xor_image(value, gap):
    x, y = value & 7, value >> 3
    if gap == 0:
        return (((-x) % 8) & y) != 0
    if gap == 1:
        return (x & y) != 0
    if gap == 2:
        square = (x * x) % 8
        return y >= 2 if (square ^ 4) < (x ^ 4) else x >= 5
    if x < y:
        return x == 2
    quotient = x // y if y else 0
    return quotient > 1


def full_five_bit_upper(value):
    x, y = value & 7, value >> 3
    if x == y:
        return x > 2
    if y < 2:
        return (x & y) != 0
    if x < y:
        return x == 2
    return x >= 5


def quadratic_image():
    # Coefficient at mask s multiplies the product of source bits named by s.
    coefficients = (9, 14, 26, 30, 16, 10, 6, 0, 7, 12, 3, 0, 12, 0, 0, 0)
    assert all(not coefficient or mask.bit_count() <= 2
               for mask, coefficient in enumerate(coefficients))
    return [reduce(xor, (c for mask, c in enumerate(coefficients) if v & mask == mask), 0)
            for v in range(16)]


def affine_and_quadratic_clocks():
    source_covers = [v for v in range(16) if cover(v, 4)]
    assert len(source_covers) == 7 and reduce(xor, source_covers) == 15 and cover(15, 4)
    survivors = []
    for normal, offset in product(range(1, 32), range(2)):
        plane = [v for v in range(32) if (v & normal).bit_count() % 2 == offset]
        covered = [v for v in plane if cover(v, 5)]
        if len(covered) == 7 and cover(reduce(xor, covered), 5):
            survivors.append((normal, offset))
            assert feasible(plane, 5, 3, 5)
    assert survivors == [(7, 0), (14, 0), (19, 0), (25, 0), (28, 0)]
    image = quadratic_image()
    assert len(set(image)) == 16 and max(image) < 32
    assert all(cover(v, 4) == cover(z, 5) for v, z in enumerate(image))
    assert not feasible(image, 5, 3, 5)
    print("All verdict-preserving affine images take at most five; one quadratic image needs six.")


def verify_second_quadratic():
    coefficients = (60, 48, 50, 34, 44, 47, 6, 0, 46, 52, 51, 0, 10, 0, 0, 0,
                    31, 25, 51, 0, 55, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0)
    full_map = [reduce(xor, (c for s, c in enumerate(coefficients) if v & s == s), 0)
                for v in range(32)]
    assert all(not c or s.bit_count() <= 2 for s, c in enumerate(coefficients))
    assert len(set(full_map)) == 32 and max(full_map) < 64
    assert all(cover(v, 5) == cover(full_map[v], 6) for v in range(32))
    transported = [full_map[v] for v in quadratic_image()]
    assert sorted(transported) == [5, 15, 21, 22, 25, 27, 28, 31, 34, 41, 42, 45, 51, 52, 53, 59]
    assert not feasible(transported, 6, 3, 5)
    print("Successive quadratic maps on the same sixteen inputs: four, six, six.", flush=True)


def six_bit_upper(v):
    x, y = v & 7, v >> 3
    if x < y:
        return x >= 5 if (x ^ 4) < (2 ^ 4) else (y & 5) == 5
    if x < 5:
        return (x & y) == 3
    return y >= 5 if (y ^ 4) < (2 ^ 4) else x != 6


def main():
    assert not feasible(range(4), 2, 1, 2) and feasible(range(4), 2, 1, 3)
    assert not feasible(range(8), 3, 2, 3) and feasible(range(8), 3, 2, 4)
    assert not feasible(range(16), 4, 3, 4)
    for v in range(16):
        x, y = v & 7, v >> 3
        square = (x * x) % 8
        assert cover(v, 4) == (y != 0 if (square ^ 4) < (x ^ 4) else x >= 5)
    assert all(cover(v, 4) == ((v & 3) & (v >> 2) != 0) for v in range(16))
    assert not feasible(range(16), 4, 2, 3)
    assert all(full_five_bit_upper(v) == cover(v, 5) for v in range(32))
    assert not feasible(range(32), 5, 3, 5)
    print("Unrestricted complete clocks: four at four bits, six at five bits.", flush=True)
    affine_and_quadratic_clocks()
    verify_second_quadratic()
    assert all(cover(v, 6) == six_bit_upper(v) for v in range(64))
    # A full length-five source already needs six steps after adding a bit at gap zero.
    full_image = [subdivide(v, 5, 0, "xor") for v in range(32)]
    assert not feasible(full_image, 6, 3, 5)
    for method in ("xor", "or"):
        for gap in range(4):
            image = [subdivide(v, 4, gap, method) for v in range(16)]
            assert all(cover(v, 4) == cover(image[v], 5) for v in range(16))
            assert len(set(image)) == 16
            if method == "xor":
                assert all(upper_on_xor_image(v, gap) == cover(v, 5) for v in image)
            expected = gap == 1
            assert feasible(image, 5, 3, 4) == expected
            if expected:
                assert not feasible(image, 5, 3, 3)
            print(f"{method}, gap {gap}, four instructions feasible: {expected}")

    for i in range(4):
        first = [subdivide(v, 4, i, "xor") for v in range(16)]
        clocks = []
        for j in range(5):
            second = [subdivide(v, 5, j, "xor") for v in first]
            assert all(cover(v, 4) == cover(second[v], 6) for v in range(16))
            for budget in (3, 4, 5):
                if feasible(second, 6, 3, budget):
                    clocks.append(budget)
                    break
            else:
                raise AssertionError("No five-step upper on this second image")
        print(f"Second XOR insertion after first gap {i}: {clocks}", flush=True)


if __name__ == "__main__":
    main()
