"""Data-address and paired-input certificates for two-load five-slot native RAMs."""

from functools import lru_cache
from itertools import combinations_with_replacement, product
import sys
from operator import add, and_, eq, lt, mul, or_, sub, xor


def signed(x):
    return (x + 8) % 16 - 8


COMPARISONS = (eq, lt, lambda x, y: signed(x) < signed(y))
OPS = (
    and_, or_, xor, add, sub, mul,
    lambda x, y: x << y, lambda x, y: x >> y, lambda x, y: signed(x) >> y,
    lambda x, y: x << (y % 4), lambda x, y: x >> (y % 4), lambda x, y: signed(x) >> (y % 4),
    lambda x, y: (x << (y % 4)) | (x >> (4 - y % 4)),
    lambda x, y: (x >> (y % 4)) | (x << (4 - y % 4)),
) + COMPARISONS + tuple(lambda x, y, comp=comp: not comp(x, y) for comp in COMPARISONS)

POSITIVES = [(p, m) for p, m in product(range(1, 16), repeat=2) if not p & m]
SELF, OTHER_REGISTER = -2, -1


def possible_addresses(op, left, right, p, m):
    loads = {0, p, m}
    result = loads.copy()  # Allows the ALU output register to alias a LOAD destination.
    for _ in range(6):
        def values(operand):
            if operand == SELF:
                return result
            return loads if operand == OTHER_REGISTER else (operand,)

        added = {op(a, b) & 15 for a, b in product(values(left), values(right))}
        if added <= result:
            break
        result.update(added)
    return result


def address_survivors():
    result = set()
    for op in OPS:
        for left, right in product(range(SELF, 16), repeat=2):
            # d=-1 includes two indirect sites, or a direct load of scratch.
            remaining = set(range(-1, 4))
            for p, m in POSITIVES:
                reachable = possible_addresses(op, left, right, p, m)
                remaining = {d for d in remaining if {0, 1, 2, 3} <= reachable | {d}}
                if not remaining:
                    break
            if remaining:
                # The finite filter certifies precisely this structural condition.
                assert (left == SELF and right >= 0) or (right == SELF and left >= 0)
                unary = tuple(op(x if left == SELF else left,
                                 x if right == SELF else right) & 15 for x in range(16))
                result.update((unary, d) for d in remaining)
    return result


def order(x, y):
    return (x > y) - (x < y), (signed(x) > signed(y)) - (signed(x) < signed(y))


def address_kind(x):
    return min(x // 2, 2)  # Positive word, negative word, or untouched scratch.


def find_indistinguishable(clock, literals):
    fixed = set(clock) | set(literals) | {0}
    groups = {}
    for word in range(1, 16):
        signature = address_kind(word), tuple(order(word, c) for c in sorted(fixed))
        groups.setdefault(signature, []).append(word)
    group_at = {word: group for group in groups.values() for word in group}
    for p, m in POSITIVES:
        for pp, mm in product(group_at[p], group_at[m]):
            if pp & mm and order(p, m) == order(pp, mm):
                return (p, m), (pp, mm)
    return None


def can_visit_four(unary, loads, p, m):
    # Register 0 holds the ALU output; the only other load destination is register 1.
    memory = (p, p, m, m)

    @lru_cache(None)
    def walk(regs, seen, counts):
        if seen == 15:
            return True
        for site in range(3):
            used = list(counts)
            used[site] += 1
            if sum(used) + max(used) > 16:
                continue
            after = list(regs)
            marked = seen
            if site == 2:
                after[0] = unary[regs[0]]
            else:
                dest, operand = loads[site]
                address = regs[operand-5] if operand >= 5 else operand
                after[dest] = memory[address] if address < 4 else 0
                if address < 4:
                    marked |= 1 << address
            if tuple(after) == regs and marked == seen:
                continue
            if walk(tuple(after), marked, tuple(used)):
                return True
        return False

    return walk((0, 0), 0, (0, 0, 0))


def emit_aliased_palettes(surviving):
    maps = sorted({f for f, d in surviving})
    emitted = 0
    # Operand codes 0..3 select input cells, 4 represents any untouched
    # scratch address, and 5,6 select the registers R,S respectively.
    site_options = list(product(range(2), range(7)))
    for f in maps:
        for loads in combinations_with_replacement(site_options, 2):
            if not any(dest == 0 for dest, address in loads):
                continue
            if not any(address >= 5 for dest, address in loads):
                continue
            direct = next((a for dest, a in loads if a < 4), -1)
            if (f, direct) not in surviving:
                continue
            if all(can_visit_four(f, loads, p, m) for p, m in POSITIVES):
                print(*f, *loads[0], *loads[1])
                emitted += 1
    assert emitted == 31


if __name__ == '__main__':
    surviving = address_survivors()
    if '--emit-palettes' in sys.argv:
        emit_aliased_palettes(surviving)
        sys.exit(0)
    maps = sorted({f for f, d in surviving})
    assert len(POSITIVES) == 50 and len(surviving) == 13 and len(maps) == 9
    increment = tuple((x + 1) & 15 for x in range(16))
    assert {f for f, d in surviving if d == -1} == {increment}
    for literals in combinations_with_replacement(range(16), 3):
        assert any(not {even, even + 1}.intersection(literals) for even in (8, 10, 12, 14))
    print("Address filter: 13 map/address pairs, 9 distinct unary maps; only increment with no direct load.")
    count = 0
    for f in maps:
        clock = [0]
        for _ in range(6):
            clock.append(f[clock[-1]])
        for literals in combinations_with_replacement(range(16), 2):
            assert find_indistinguishable(clock, literals) is not None
            count += 1
    print(f"Dedicated result register: indistinguishable SAT/UNSAT inputs for all {count} cases.")
