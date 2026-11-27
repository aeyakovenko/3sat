"""Opposite parity DIMACS files and bit-probe replay through unresolved words."""

from argparse import ArgumentParser
from collections import defaultdict
from itertools import product
from random import Random
from subprocess import run


def padded(line, width):
    assert len(line) < width
    return line + b' ' * (width - 1 - len(line)) + b'\n'


def parity_file(roles, bits, tag, width=32):
    n = len(roles)
    assert n >= 2 and roles.count('tag') == 1
    names = [14 + j for j in range(n)]
    rows = [tuple(-v if mask >> (v - 1) & 1 else v for v in (1, 2, 3)) for mask in range(1, 8)]
    rows.extend(((12, 13, 1), (-12, -13, 1)))
    current = names[0]
    for j, value in enumerate(names[1:]):
        new = 14 + n + j
        for px, py, pz in product(range(2), repeat=3):
            if px ^ py != pz:
                rows.append(tuple(-t if b else t for t, b in zip((current, value, new), (px, py, pz), strict=True)))
        current = new
    rows.extend(((12, -current, 1), (-12, current, 1)))
    count = len(rows) + 2 * n
    raw = [padded(f'p cnf {current} {count}'.encode(), width)]
    for row in rows:
        raw.append(padded((' '.join(map(str, row)) + ' 0').encode(), width))
    for j, (role, bit) in enumerate(zip(roles, bits, strict=True)):
        if role == 'tag':
            assert not bit
            middle = f'{13 - tag} 1 2 0\n'.encode()
        elif role == 'query':
            middle = b'2 -1 3 0\n'
        else:
            assert role == 'ordinary'
            middle = b'-1 2 3 0\n'
        sign = b' ' if bit else b'-'
        raw.extend((middle + b' ' * (width - len(middle) - 1) + sign,
                    padded(f'{names[j]} 1 2 0'.encode(), width)))
    assert len(raw) == 6 * n + 8
    physical = b''.join(raw)
    lines = physical.splitlines()
    assert len(lines) == count + 1
    for line in lines[1:]:
        a, b, c, end = map(int, line.split())
        assert end == 0 and len({abs(a), abs(b), abs(c)}) == 3
    return physical


def audit_files(solver):
    n = 5
    checked = 0
    for tag_slot in range(n):
        roles = ['query' if j % 2 else 'ordinary' for j in range(n)]
        roles[tag_slot] = 'tag'
        for other in product(range(2), repeat=n - 1):
            bits = list(other)
            bits.insert(tag_slot, 0)
            files = [parity_file(roles, bits, t) for t in (0, 1)]
            assert sum((x ^ y).bit_count() for x, y in zip(*files, strict=True)) == 1
            for t, f in enumerate(files):
                if solver:
                    result = run([solver, '-q'], input=f, capture_output=True, check=False)
                    assert result.returncode == (10 if (sum(bits) % 2 == t) else 20)
                checked += 1
    print(f'{checked} proper files and all single-ordinary-bit parity changes verified')


def read_chain(base, unknown, writes, start, times, paid, raw_cache):
    """A starting origin can first reach at most one unshadowed unknown position.

    The optional oracle access happens only at the base graph's first unknown
    point since the most recent reset. The eager implementation is independent.
    """
    u = start
    paid.add(u)
    address = u
    for time in times:
        prior = next((value for when, target, value in reversed(writes)
                      if when < time and target == address), None)
        if prior is not None:
            u = prior
            paid.add(u)
            address = u
        elif address in unknown:
            if address not in raw_cache:
                raw_cache[address] = unknown[address]
            u = raw_cache[address]
            paid.add(u)
            address = u
        else:
            address = base[address]
    return address


def eager(base, unknown, writes, start, times):
    state = dict(base) | unknown
    used = 0
    address = start
    for time in times:
        while used < len(writes) and writes[used][0] < time:
            _, target, value = writes[used]
            state[target] = value
            used += 1
        address = state[address]
    return address


def audit_replay():
    rng = Random(20261127)
    cases = 0
    for size in range(6, 21):
        for _ in range(100):
            base = {x: rng.randrange(size) for x in range(size)}
            hidden = rng.sample(range(size), size // 2)
            symbols = rng.sample(range(size), 2)
            unknown = {x: rng.choice(symbols) for x in hidden}
            for x in unknown:
                base[x] = 0
            writes = [(t, rng.randrange(size), rng.randrange(size)) for t in sorted(rng.sample(range(50), 6))]
            raw_cache = {}
            all_origins = set()
            for _ in range(10):
                start = rng.randrange(size)
                times = sorted(rng.sample(range(50), 18))
                value = read_chain(base, unknown, writes, start, times, all_origins, raw_cache)
                assert value == eager(base, unknown, writes, start, times)
                cases += 1
            # First-hit is a function of an origin alone, even with returns to
            # an overwritten unknown address later in the same pointer chain.
            reached = defaultdict(set)
            for origin in all_origins:
                seen = set()
                address = origin
                while address not in seen and address not in unknown:
                    seen.add(address)
                    address = base[address]
                if address in unknown:
                    reached[origin].add(address)
            covered = set().union(*reached.values()) if reached else set()
            assert set(raw_cache) <= covered and len(raw_cache) <= len(all_origins)
    print(f'{cases} time-sensitive chains matched eager memory and the first-hit probe budget')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--solver', help='verify all files with this CaDiCaL binary')
    audit_files(parser.parse_args().solver)
    audit_replay()
