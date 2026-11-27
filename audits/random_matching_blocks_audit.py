"""Finite tests for cycle partitions and adaptive omission of independent source rows."""

from itertools import permutations
from math import comb
from random import Random


def cycle_blocks(first, second, block):
    n = len(first)
    inv = {v: i for i, v in enumerate(first)}
    old = set()
    order = []
    for i in range(n):
        while i not in old:
            old.add(i)
            order.append(i)
            i = inv[second[i]]
    source = {v: i // block for i, v in enumerate(order)}
    target = {first[v]: b for v, b in source.items()}
    return source, target


def occupied(perms, source, target):
    return {(source[i], target[j]) for p in perms for i, j in enumerate(p)}


def check_cycles():
    rng = Random(639859)
    checks = 0
    for n in range(2, 17):
        first = rng.sample(range(n), n)
        tests = permutations(range(n)) if n < 8 else (rng.sample(range(n), n) for _ in range(30))
        for second in tests:
            third = rng.sample(range(n), n)
            for block in (1, 2, 3, 5, 8):
                source, target = cycle_blocks(first, second, block)
                k = (n + block - 1) // block
                assert len(occupied((first, second), source, target)) <= 3 * k
                assert len(occupied((first, second, third), source, target)) <= n + 3 * k
                checks += 1
    return checks


def inner_product_receiver(x, y, r):
    """Send parity and one unprobed coordinate's y bit; the coordinator knows x.

    Choice of the reserved coordinate depends on queried x[0], also known to
    the coordinator. The other queried source coordinates depend on y.
    """
    touched = 1
    reserved = 1 + (x & 1)
    parity = (x & y) & 1
    for i in range(1, r):
        if i != reserved and (y >> i) & 1:
            touched |= 1 << i
            parity ^= (x >> i) & 1
    msg = (y >> reserved & 1, parity)
    assert parity ^ ((x >> reserved) & msg[0] & 1) == ((x & y).bit_count() & 1)
    return touched, msg


def check_omissions():
    checks = 0
    for r in (3, 4, 5, 6, 7):
        for x in range(1 << r):
            rows = [inner_product_receiver(x, y, r) for y in range(1 << r)]
            for s in range(1 << r):
                by_message = {}
                count = 0
                for y, (touched, msg) in enumerate(rows):
                    if touched & s:
                        continue
                    count += 1
                    pattern = y & s
                    assert by_message.setdefault(msg, pattern) == pattern
                assert count <= 4 * (1 << (r - s.bit_count()))
                checks += 1
            for q in range(r + 1):
                assert sum(t.bit_count() <= q for t, _ in rows) <= comb(r, q) * (4 << q)
    return checks


if __name__ == "__main__":
    print(f"{check_cycles()} cycle partitions; {check_omissions()} adaptive omission bounds")
