"""Check adaptive indirect writes, batched messages, and equal-length proper DIMACS."""

from itertools import product
from math import gcd
from random import Random


def run_case(initial, start, stride, cut, reads, radius, choices=None):
    domain = len(initial)
    period = domain // gcd(domain, stride)
    passes = (reads + period - 1) // period
    halo = radius * passes
    alphabet = set(initial)
    moved = {
        (value + stride * s) % domain
        for value in alphabet
        for s in range(halo + 1)
    }
    orbit = [(start + i * stride) % domain for i in range(period)]
    owners = [int(a >= cut) for a in orbit]
    transitions = sum(owners[i] != owners[i - 1] for i in range(period))
    assert transitions <= 2 * abs(stride)
    phase_count = 1
    records = 0
    pending = {}
    active = owners[0]
    memory = initial[:]
    shadows = [
        {i: value for i, value in enumerate(initial) if int(i >= cut) == owner}
        for owner in (0, 1)
    ]
    control = 1
    peer_control = control
    local = inside = from_inside = 0
    for i in range(reads):
        p = orbit[i % period]
        owner = owners[i % period]
        if owner != active:
            records += len(pending)
            shadows[owner].update(pending)
            pending.clear()
            active = owner
            phase_count += 1
            assert control == peer_control
        x = memory[p]
        y = shadows[owner][p]
        assert x == y
        # Two independent copies of the controller, including data-dependent skips.
        control = (control * 5 + x + p + 1) % 97
        peer_control = (peer_control * 5 + y + p + 1) % 97
        choice = control % (radius + 2) - 1 if choices is None else choices[i]
        peer_choice = peer_control % (radius + 2) - 1 if choices is None else choices[i]
        assert choice == peer_choice
        is_local = any(orbit[(i + b) % period] == x for b in range(-halo, halo + 1))
        assert is_local or x in moved or p in moved
        if choice < 0:
            continue
        payload = orbit[(i + choice) % period]
        memory[x] = payload
        if int(x >= cut) == owner:
            shadows[owner][y] = payload
        else:
            pending[y] = payload
            if is_local:
                local += 1
            elif x in moved:
                inside += 1
            else:
                from_inside += 1
    records += len(pending)
    shadows[1 - active].update(pending)
    assert memory == [shadows[int(a >= cut)][a] for a in range(domain)]
    assert phase_count <= transitions * passes + 1
    assert from_inside <= passes * len(moved)
    assert records <= (
        phase_count * ((2 * halo + 2) * transitions + len(moved))
        + passes * len(moved)
    )
    return local, inside, from_inside


def emit_equal(a, b, width):
    """Use width bytes per aligned block and exactly eight proper clauses per bit."""
    assert len(a) == len(b) and width >= 3
    k = len(a)
    bits = (k + 2).bit_length()

    def digits(index):
        return ''.join('0' * (width - 1) + bit for bit in f'{index:0{bits}b}')

    bound = '1' + digits((1 << bits) - 1)
    header = f'p cnf {bound} {8*k}\n'
    header += ' ' * (-len(header) % width)

    def literal(index, positive):
        return ' ' * (width - 2) + (' ' if positive else '-') + '1' + digits(index)

    def half(vector):
        return ''.join(
            literal(i, sign) + literal(k + 1, u) + literal(k + 2, v)
            + ' 0\n' + ' ' * (width - 3)
            for i, sign in enumerate(vector, 1) for u, v in product((0, 1), repeat=2)
        )

    left, right = header + half(a), half(b)
    assert len(left) % width == 0
    data = left + right
    words = {data[i:i + width] for i in range(0, len(data), width)}
    assert len(words) <= 13
    return data


def audit_formula(a, b, width):
    data = emit_equal(a, b, width)
    fields = data.split()
    assert fields[:2] == ['p', 'cnf']
    variables, rows = int(fields[2]), int(fields[3])
    clauses = [list(map(int, fields[i:i + 4])) for i in range(4, len(fields), 4)]
    assert len(clauses) == rows
    ids = sorted({abs(lit) for c in clauses for lit in c if lit})
    assert max(ids) <= variables and len(ids) == len(a) + 2
    assert all(c[-1] == 0 and len({abs(x) for x in c[:3]}) == 3 for c in clauses)
    compiled = [[(ids.index(abs(x)), x > 0) for x in c[:3]] for c in clauses]
    sat = any(
        all(any(values[j] == sign for j, sign in clause) for clause in compiled)
        for values in product((0, 1), repeat=len(ids))
    )
    assert sat == (a == b)


def arbitrary_payload_equality(k, alice, bob):
    beta = [3*i+1 for i in range(k)]
    gamma = [3*i+2 for i in range(k)]
    remote = [3*k+2*i+1 for i in range(k)]
    memory = [0]*(5*k)
    for i in range(k):
        memory[3*i] = (alice >> i) & 1
        memory[remote[i]-1] = (bob >> i) & 1
    memory[beta[0]] = gamma[0]
    for i in range(k-1):
        memory[memory[beta[i]]] = beta[i+1]
        memory[memory[gamma[i]]] = gamma[i+1]
    for i in range(k):
        bit = memory[3*i]
        memory[memory[beta[i]]] = remote[i]
        memory[memory[gamma[i]]] = bit
    return all(memory[j-1] == memory[j] for j in remote)


def main():
    exhaust = 0
    for config in product(range(3), repeat=3):
        for start in range(3):
            for schedule in product((-1, 0, 1, 2, 3), repeat=3):
                run_case(list(config), start, 1, 2, 3, 3, schedule)
                exhaust += 1
    rng = Random(199311)
    charges = [0, 0, 0]
    for _ in range(3000):
        size = rng.randrange(7, 66)
        palette = rng.sample(range(size), rng.randrange(1, min(5, size)))
        sample = [rng.choice(palette) for _ in range(size)]
        step = rng.choice((-4, -3, -2, -1, 1, 2, 3, 4))
        period = size // gcd(size, step)
        result = run_case(sample, rng.randrange(size), step, rng.randrange(1, size),
                          rng.randrange(1, 5 * period + 1), rng.randrange(7))
        charges = [x + y for x, y in zip(charges, result)]
    assert all(charges)
    formulas = 0
    for k in range(1, 4):
        for a, b in product(product((0, 1), repeat=k), repeat=2):
            for width in (3, 4, 7):
                audit_formula(a, b, width)
                formulas += 1
    for k in range(1, 7):
        for alice, bob in product(range(2**k), repeat=2):
            assert arbitrary_payload_equality(k, alice, bob) == (alice == bob)
    print('Arbitrary payloads delivered equality on 5,460 two-pass test inputs')
    print(f'{exhaust} exhaustive traces, 3000 adaptive traces, {formulas} DIMACS files')
    print(f'foreign events by charge (local, destination, source): {charges}')


if __name__ == '__main__':
    main()
