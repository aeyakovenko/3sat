#!/usr/bin/env python3
"""A fixed guest submits an ordinary bounded-path CNF about its own quiet prefix.

Its public header is the six-bit program tag followed by n zero padding bits.
The guest rotates a phase and keeps a latch initially off. It records n*n quiet
updates, submits power-of-two path-checker stages until one recognizes that
prefix, then latches on the returned YES. Its three-bit proposed phase cycle
is part of the input. The positive front checks a real assignment on the
actual bytes. A miss simply continues. The first successful stage satisfies
n*n <= T < 2*n*n. The bounded-path file has O(T + log n) variables and
clauses and O((T + log n) log(T + n + 2)) ASCII bytes. The byte comparison
and model evaluation take polynomial time in n on this family.

The fixed path checker rotates the phase for n*n updates; a post-reply query
additionally consumes one recorded answer bit. It checks the claimed phase
cycle and zero latch throughout, and idles to the supplied stage bound T.
An accepting path must complete all required updates. All rows are unrolled
in proper three-literal DIMACS clauses. Metadata is carried by signed, pinned
variables immediately after seven false-anchor clauses, without comments.
The post-reply replay query describes the actual bit when the guest drives it.
The separate closed-observation compiler specializes the front to its known
public header. It compares each file bit, evaluates every canonical clause on
the reconstructed path, and connects its return directly to the latch. Its
terminal-zero CNF has no supplied reply bit.

This models a concrete staged guest and its finite-state path checker. Python
operations for emitting and reading bytes are outside the logical stage-row
clock. No unrestricted universal-guest interpreter or learned SAT decider is
embedded in the CNF. Run this file directly for the reproducible experiment.
"""

from dataclasses import dataclass
from itertools import product


TAG = (1, 0, 1, 1, 0, 1)
ANCHORS = tuple(tuple(-v if bit else v for v, bit in enumerate(bits, 1))
                for bits in product((0, 1), repeat=3) if any(bits))
OK, BAD = 4, 5


@dataclass(frozen=True)
class Header:
    n: int
    stage: int
    mode: int  # 0 = prefix, 1 = recorded NO, 2 = recorded YES
    cycle: tuple


def gamma(n):
    if n < 1:
        raise ValueError("positive field required")
    digits = tuple(map(int, bin(n)[2:]))
    return (0,) * (len(digits) - 1) + digits


def header_bits(h):
    return TAG + gamma(h.n) + gamma(h.stage) + (h.mode >> 1, h.mode & 1) + h.cycle


def public_cycle(n):
    return tuple(int((n + t) % 3 == 0) for t in range(3))


def proper(clause):
    """Pinning anchors 1 and 2 to false preserves each shortened clause."""
    return tuple(clause) + tuple(range(1, 4 - len(clause)))


def literals(line):
    a, b, c, end = map(int, line.split())
    if end != 0 or not a or not b or not c or len({abs(a), abs(b), abs(c)}) != 3:
        raise ValueError("three distinct nonzero variable names are required")
    return a, b, c


def read_header(raw):
    rows = iter(raw.splitlines())
    next(rows)
    for _ in ANCHORS:
        next(rows)
    index = 6

    def bit():
        nonlocal index
        value, one, two = literals(next(rows))
        if (abs(value), one, two) != (index, 1, 2):
            raise ValueError("bad public bit")
        index += 1
        return int(value > 0)

    def integer():
        zeros = 0
        while not bit():
            zeros += 1
        value = 1
        for _ in range(zeros):
            value = 2 * value + bit()
        return value

    if tuple(bit() for _ in TAG) != TAG:
        raise ValueError("unknown program")
    n, stage = integer(), integer()
    mode = 2 * bit() + bit()
    cycle = tuple(bit() for _ in range(3))
    if mode > 2 or stage > len(raw) or stage & (stage - 1):
        raise ValueError("bad stage or record type")
    return Header(n, stage, mode, cycle)


def dimensions(h):
    first = 6 + len(header_bits(h))
    return first, first + 4 * (h.stage + 1) - 1


def clauses(h):
    bits = header_bits(h)
    first, _ = dimensions(h)
    yield from ANCHORS
    for v, b in enumerate(bits, 6):
        yield proper((v if b else -v,))

    def equiv(dst, src):
        return (proper((-dst, src)), proper((dst, -src)))

    length = h.n ** 2 + int(h.mode != 0)
    # Variable 6 is the initial one of the fixed tag.
    yield from equiv(OK, 6 if h.stage >= length else -6)
    yield from equiv(BAD, -OK)
    for j in range(4):
        true = j < 3 and j == h.n % 3
        yield proper((first + j if true else -(first + j),))
    for t in range(h.stage + 1):
        row = first + 4 * t
        logical = min(t, length)
        if t:
            prior = row - 4
            for j in range(3):
                source = (j - 1) % 3 if t <= length else j
                yield from equiv(row + j, prior + source)
            if h.mode and t == length:
                # The high bit of the two-bit mode is exactly the recorded YES.
                yield from equiv(row + 3, first - 5)
            else:
                yield from equiv(row + 3, prior + 3)
        if t <= length:
            yield from equiv(row, first - 3 + logical % 3)
            if t:  # row zero already pins the latch off
                yield proper((-(row + 3),))
    yield proper((OK,))


def emit(h):
    _, count = dimensions(h)
    lines = [b"%d %d %d 0\n" % clause for clause in clauses(h)]
    return b"p cnf %d %d\n" % (count, len(lines)) + b"".join(lines)


def path_assignment(h):
    """Compute the actual path independently of the literal emitter."""
    bits = header_bits(h)
    first, count = dimensions(h)
    values = [False] * (count + 1)
    values[6:first] = bits
    values[OK] = h.stage >= h.n * h.n + (h.mode != 0)
    values[BAD] = not values[OK]
    phase, latch = h.n % 3, False
    for tick in range(h.stage + 1):
        if 0 < tick <= h.n * h.n:
            phase = (phase + 1) % 3
        elif tick == h.n * h.n + 1 and h.mode:
            phase = (phase + 1) % 3
            latch = h.mode == 2
        row = first + 4 * tick
        values[row:row + 4] = [phase == j for j in range(3)] + [latch]
    return values


def read_dimacs(raw):
    lines = raw.splitlines()
    p, cnf, n, m = lines[0].split()
    if (p, cnf) != (b"p", b"cnf") or int(m) != len(lines) - 1:
        raise ValueError("bad DIMACS header")
    n = int(n)
    terms = tuple(literals(line) for line in lines[1:])
    if len({tuple(sorted(row)) for row in terms}) != len(terms):
        raise ValueError("duplicate clause")
    if {abs(lit) for row in terms for lit in row} != set(range(1, n + 1)):
        raise ValueError("names must be dense and in range")
    return n, terms


def front(raw):
    """One-sided. The only YES branch compares the entire file and a model."""
    try:
        h = read_header(raw)
        if h.n ** 2 + (h.mode != 0) > h.stage or raw != emit(h):
            return False
        n, terms = read_dimacs(raw)
        values = path_assignment(h)
        return len(values) == n + 1 and all(
            any(values[abs(lit)] == (lit > 0) for lit in clause) for clause in terms)
    except (ValueError, StopIteration, IndexError):
        return False


def prove_unsat(raw):
    """Verify the anchor gadget, then issue only forced unit assignments."""
    _, terms = read_dimacs(raw)
    for bits in product((False, True), repeat=3):
        assignment = (None, *bits)
        satisfies = all(any(assignment[abs(l)] == (l > 0) for l in c) for c in terms[:7])
        if satisfies != (not any(bits)):
            return False
    values = {1: False, 2: False, 3: False}
    while True:
        initial = len(values)
        for clause in terms:
            undecided = []
            for lit in clause:
                if abs(lit) not in values:
                    undecided.append(lit)
                elif values[abs(lit)] == (lit > 0):
                    break
            else:
                if not undecided:
                    return True
                if len(undecided) == 1:
                    lit = undecided[0]
                    values[abs(lit)] = lit > 0
        if len(values) == initial:
            return False


def run_guest(n):
    """Only plan data fixed before the call: width and the correct phase cycle."""
    cycle = public_cycle(n)
    phase = n % 3
    latch = False
    for t in range(n * n + 1):
        assert (phase == 0) == cycle[t % 3] and not latch
        if t < n * n:
            phase = (phase + 1) % 3
    stage, count, total_bytes = 1, 0, 0
    while True:
        raw = emit(Header(n, stage, 0, cycle))
        count += 1
        total_bytes += len(raw)
        reply = front(raw)
        if reply:
            break
        assert prove_unsat(raw)
        stage *= 2
    assert n * n <= stage < 2 * n * n
    tampered = raw[:-len(b"4 1 2 0\n")] + b"5 1 2 0\n"
    assert raw.endswith(b"4 1 2 0\n") and len(raw) == len(tampered)
    assert sum(a != b for a, b in zip(raw, tampered)) == 1
    assert not front(tampered) and prove_unsat(tampered)
    # The same guest that made the real call consumes its actual return.
    latch |= reply
    phase = (phase + 1) % 3
    assert (phase == 0) == cycle[(n * n + 1) % 3] and latch
    post_stage = 1 << (n * n).bit_length()
    post = emit(Header(n, post_stage, 1 + int(reply), cycle))
    assert not front(post) and prove_unsat(post)
    return count, total_bytes, stage, len(raw)



def closed_observation(h, raw):
    """Compile the selected call's latch directly, with no trusted answer bit.

    For files of this fixed length and header, the source front's only remaining
    tests are full-byte equality and the canonical parsed model check. Compile
    these two tests rather than running a general Python interpreter in CNF.
    Observe immediately after this call, before a later call could change it.
    """
    expected = emit(h)
    if read_header(raw) != h or len(expected) != len(raw) or h.stage < h.n ** 2:
        raise ValueError("this specialization requires the same eligible public header and length")
    _, terms = read_dimacs(expected)
    path = path_assignment(h)
    out = list(ANCHORS)
    values = [False] * 4

    def var(value):
        values.append(bool(value))
        return len(values) - 1

    def pin(value):
        name = var(value)
        out.append(proper((name if value else -name,)))
        return name

    def value(lit):
        return values[abs(lit)] == (lit > 0)

    def both(a, b):
        y = var(value(a) and value(b))
        out.extend((proper((-y, a)), proper((-y, b)), (y, -a, -b)))
        return y

    accepts = pin(True)
    for byte, ref in zip(raw, expected):
        for j in range(8):
            data = pin((byte >> j) & 1)
            match = data if (ref >> j) & 1 else -data
            accepts = both(accepts, match)
    variables = [None] + [pin(b) for b in path[1:]]
    for clause in terms:
        a, b, c = [variables[abs(lit)] * (1 if lit > 0 else -1) for lit in clause]
        first_two_false = both(-a, -b)
        clause_false = both(first_two_false, -c)
        accepts = both(accepts, -clause_false)
    # Latch starts zero and this is its only possible update before observation.
    out.append(proper((-accepts,)))
    raw_observation = (b"p cnf %d %d\n" % (len(values) - 1, len(out))
                       + b"".join(b"%d %d %d 0\n" % c for c in out))
    return raw_observation, values

def main():
    calls = byte_count = 0
    for n in (1, 2, 3, 5, 8, 12):
        count, amount, stage, accepted_size = run_guest(n)
        calls += count
        byte_count += amount
        print(f"padding={n} accepted_stage={stage} accepted_bytes={accepted_size} latch=1")
    # Even a reconstructed canonical path with a false cycle must fail.
    for n in (1, 2, 3):
        true_cycle = public_cycle(n)
        stage = 1 << (n * n).bit_length()
        for cycle in product((0, 1), repeat=3):
            for mode in (0, 1, 2):
                raw = emit(Header(n, stage, mode, cycle))
                answer = front(raw)
                assert answer != prove_unsat(raw)
                # For n=1 the prefix need not sample the entire 3-cycle.
                length = n * n + (mode != 0)
                good = all(cycle[t % 3] == true_cycle[t % 3] for t in range(length + 1))
                assert answer == (mode != 2 and good)
    closed_counts = []
    for n in (1, 2):
        stage = 1 << (n * n - 1).bit_length()
        h = Header(n, stage, 0, public_cycle(n))
        raw = emit(h)
        altered = raw[:-len(b"4 1 2 0\n")] + b"5 1 2 0\n"
        for payload in (raw, altered):
            observation, model = closed_observation(h, payload)
            _, terms = read_dimacs(observation)
            zero_possible = all(any(model[abs(l)] == (l > 0) for l in c) for c in terms)
            assert zero_possible == (payload == altered)
            assert prove_unsat(observation) == front(payload) == (not zero_possible)
        closed_counts.append((len(terms), len(observation)))
    print(f"Closed receipt-free observation CNFs (clauses, bytes): {closed_counts}")
    print(f"PASS: {calls} actual SAT calls, {byte_count} queried bytes, six same-length "
          "UNSAT edits, six UNSAT post-reply observations, 72 cycle/reply controls")


if __name__ == "__main__":
    main()
