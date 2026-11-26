"""Exact-length F_2 row spaces for three forecast candidates at every B=2**h.

Two-block timestamps t=u+B*v are read in h columns (one bit each of u,v),
least significant first within each block. The transition matrices below are
fixed once, independently of h. Run with Python 3, without dependencies.

With seeds -2,-1, the true recurrence first has ones through B-2. Its long
tap first reaches seed -2 at B-1 and cancels the other left tap. The odd
chain then stays zero because its right tap is two steps back. Even times
B through 2B-2 still see a one at the long odd tap; at 2B this reaches the
first zero odd time B-1 and the even chain dies as well.
"""

from collections import deque


# Lag a is C*B+c. These three monomials give the actual recurrence defect
# y(t) + y(t-1)y(t-2) + y(t-B-1)y(t-2) in characteristic two.
MONOMIALS = (((0, 0),), ((0, 1), (0, 2)), ((1, 1), (0, 2)))
PULSES = (None, -1, 1)  # add [3*t = B+delta] to the candidate, when specified
CAP = 4


def initial(term, delta):
    # place, low u, low complement B-1-u, high v, parity of u, pulse carries
    carries = tuple(-(3*c+delta) for _, c in term) if delta is not None else ()
    return (1, 0, 0, 0, 0, carries)


def advance(state, column):
    place, u, complement, v, parity, carries = state
    low, high = column % 2, column // 2
    # Testing 3*u = B + (3*c+delta) emits zero low bits and a final carry 1.
    updated = []
    for carry in carries:
        total = None if carry is None else carry + 3*low
        updated.append(None if total is None or total % 2 else total//2)
    return (min(CAP, 2*place), min(CAP, u+place*low),
            min(CAP, complement+place*(1-low)), min(CAP, v+place*high),
            low if place == 1 else parity, tuple(updated))


def final_bit(state, term):
    place, u, complement, v, parity, carries = state
    if place < CAP:  # only h >= 2 is claimed
        return 0

    def at_least(C, c):
        # t >= C*B+c for the small offsets used here, including negative c.
        if v > C:
            return True
        if v == C:
            return u >= c
        return v+1 == C and complement < -c

    for i, (C, c) in enumerate(term):
        # At lag zero: ones on [-2,B-2], then on the even points in
        # [B,2B-1]. This includes exactly the two historical seeds.
        early = at_least(C, c-2) ^ at_least(C+1, c-1)
        late = (parity == c%2) and (at_least(C+1, c) ^ at_least(C+2, c))
        pulse = bool(carries) and v == C and carries[i] == 1
        if not (early ^ late ^ pulse):
            return 0
    return 1


def matrices():
    # Synchronous products within monomials, direct sums across monomials.
    # All candidates read the same word, with separate terminal columns.
    transitions = [[] for _ in range(4)]
    start, sinks = 0, [0]*len(PULSES)
    for candidate, delta in enumerate(PULSES):
        for term in MONOMIALS:
            base = len(transitions[0])
            first = initial(term, delta)
            ids, pending = {first: base}, deque([first])
            start |= 1 << base
            while pending:
                state = pending.popleft()
                if final_bit(state, term):
                    sinks[candidate] |= 1 << ids[state]
                for column, matrix in enumerate(transitions):
                    successor = advance(state, column)
                    if successor not in ids:
                        ids[successor] = base + len(ids)
                        pending.append(successor)
                    matrix.append(1 << ids[successor])
    return start, transitions, sinks


def apply_matrix(row, matrix):
    result = 0
    while row:
        bit = row & -row
        result ^= matrix[bit.bit_length()-1]
        row ^= bit
    return result


def reduced_basis(rows):
    # A canonical basis is needed for exact equality of spaces across lengths.
    basis = {}
    for row in rows:
        for pivot in sorted(basis, reverse=True):
            if row & (1 << pivot):
                row ^= basis[pivot]
        if row:
            pivot = row.bit_length()-1
            for j in basis:
                if basis[j] & (1 << pivot):
                    basis[j] ^= row
            basis[pivot] = row
    return tuple(basis[j] for j in sorted(basis))


def propagate(space, layers):
    for matrices in layers:
        space = reduced_basis(apply_matrix(row, matrix) for row in space for matrix in matrices)
    return space


def valid_after_every_repetition(start, prefix, block, suffix, sinks):
    """Work in the span of *all* repetitions, independently of a length cycle."""
    assert block
    reachable = propagate((start,), prefix)
    while True:
        enlarged = reduced_basis((*reachable, *propagate(reachable, block)))
        if enlarged == reachable:
            break
        reachable = enlarged
    terminal = propagate(reachable, suffix)
    return tuple(all((row & sink).bit_count() % 2 == 0 for row in terminal) for sink in sinks)


def exact_length_cycle(start, transitions, sinks):
    space, seen, good = (start,), {}, []
    while space not in seen:
        seen[space] = len(good)
        good.append(tuple(all((row & sink).bit_count()%2 == 0 for row in space)
                          for sink in sinks))
        space = reduced_basis(apply_matrix(row, matrix) for row in space for matrix in transitions)
    begin = seen[space]
    return good, begin, len(good)-begin


def reference(h, start, transitions, sinks):
    B = 1 << h
    true = {-2: 1, -1: 1}
    candidates = [dict(true) for _ in PULSES]
    good = [True]*len(PULSES)
    for t in range(B*B):
        true[t] = (true.get(t-1, 0) ^ true.get(t-B-1, 0)) & true.get(t-2, 0)
        proposed = int(t < B-1 or (B <= t < 2*B and t%2 == 0))
        assert proposed == true[t]
        row = start
        for j in range(h):
            symbol = ((t >> j) & 1) | (((t >> (h+j)) & 1) << 1)
            row = apply_matrix(row, transitions[symbol])
        for i, (history, delta) in enumerate(zip(candidates, PULSES)):
            history[t] = proposed ^ int(delta is not None and 3*t == B+delta)
            defect = history[t] ^ ((history.get(t-1, 0) ^ history.get(t-B-1, 0))
                                   & history.get(t-2, 0))
            assert (row & sinks[i]).bit_count()%2 == defect, (h, t, delta)
            good[i] &= not defect
    return tuple(good)


def main():
    start, transitions, sinks = matrices()
    good, begin, period = exact_length_cycle(start, transitions, sinks)

    def extrapolate(h):
        return good[h if h < begin else begin + (h-begin)%period]

    checks = 0
    for h in range(2, 8):
        assert extrapolate(h) == reference(h, start, transitions, sinks)
        checks += len(PULSES) * 4**h
    # 3 divides 2**h-1 exactly at even lengths, and 2**h+1 at odd lengths.
    # The first changed bit must itself be a defect in a causal recurrence.
    for h in (*range(2, 2+2*len(good)), 10**6, 10**6+1):
        assert extrapolate(h) == (True, h%2 == 1, h%2 == 0)
    for first_length, increment, tail in ((2, 1, 0), (2, 2, 0), (2, 2, 1)):
        actual = valid_after_every_repetition(start, [transitions]*first_length,
                                              [transitions]*increment, [transitions]*tail, sinks)
        base = first_length + tail
        assert actual == (True, increment % 2 == 0 and base % 2 == 1,
                          increment % 2 == 0 and base % 2 == 0)
    print(f'{checks} individual defect checks; exact row-space cycle starts at '
          f'h={begin} with period {period}; candidate validity alternates')


if __name__ == '__main__':
    main()
