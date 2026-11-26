"""Finite comparison of sparse RAM executions and candidate conflict transversals."""

from itertools import combinations
from random import Random


def subsets(universe):
    for size in range(len(universe) + 1):
        for choice in combinations(universe, size):
            yield frozenset(choice)


def conflicts(events):
    latest = {}
    errors = set()
    for operation, address, value in events:
        if operation == "store":
            latest[address] = value
        elif value != latest.get(address, 0):
            errors.add(address)
    return frozenset(errors)


def accepted_candidates(program, verdict, alphabet):
    def visit(time, register, prefix):
        if time == len(program):
            if verdict[register]:
                yield conflicts(prefix)
            return
        op, address, offset = program[time][register]
        if op == "store":
            yield from visit(time + 1, register, prefix + [(op, address, offset)])
        elif op == "load":
            for value in range(alphabet):
                yield from visit(time + 1, (value + offset) % alphabet,
                                 prefix + [(op, address, value)])
        else:
            yield from visit(time + 1, (register + offset) % alphabet, prefix)
    return set(visit(0, 0, []))


def accepts_projection(program, verdict, alphabet, keep):
    def visit(time, register, memory):
        if time == len(program):
            return verdict[register]
        op, address, offset = program[time][register]
        if op == "store":
            following = memory.copy()
            if address in keep:
                following[address] = offset
            return visit(time + 1, register, following)
        if op == "load":
            choices = (memory.get(address, 0),) if address in keep else range(alphabet)
            return any(visit(time + 1, (value + offset) % alphabet, memory)
                       for value in choices)
        return visit(time + 1, (register + offset) % alphabet, memory)
    return visit(0, 0, {})


def check_machine(program, verdict, alphabet):
    all_conflicts = accepted_candidates(program, verdict, alphabet)
    sets = list(subsets(range(alphabet)))
    disabling = [keep for keep in sets if all(keep & errors for errors in all_conflicts)]
    for keep in sets:
        assert accepts_projection(program, verdict, alphabet, keep) == (keep not in disabling)
    # Append an isolated read from a fresh cell, discarding its value.
    # Each accepting core candidate has an honest and an erroneous suffix.
    augmented = all_conflicts | {errors | {alphabet} for errors in all_conflicts}
    extended_sets = subsets(range(alphabet + 1))
    extended = [s for s in extended_sets if all(s & errors for errors in augmented)]
    core_min = min((len(s) for s in disabling), default=None)
    extended_min = min((len(s) for s in extended), default=None)
    assert core_min == extended_min
    # A fault-activated sentinel instead introduces a singleton conflict set.
    with_sentinels = all_conflicts | {frozenset([a]) for a in (alphabet, alphabet + 1)}
    requiring = [s for s in subsets(range(alphabet + 2)) if all(s & d for d in with_sentinels)]
    sentinel_min = min((len(s) for s in requiring), default=None)
    assert sentinel_min == (None if core_min is None else core_min + 2)
    return core_min


def check_alias_example():
    alphabet = 4
    # G = 3. Its reply becomes the destination of the following store.
    program = [
        [("load", 3, 0)] * alphabet,
        [("store", register, 1) for register in range(alphabet)],
        [("load", 1, 0)] * alphabet,
    ]
    verdict = [False, True, True, True]
    assert not accepts_projection(program, verdict, alphabet, {1, 3})
    assert accepts_projection(program, verdict, alphabet, {1})
    assert accepts_projection(program, verdict, alphabet, {3})
    assert check_machine(program, verdict, alphabet) == 2


def main():
    check_alias_example()
    rng = Random(318)
    alphabet = 4
    census = {}
    for _ in range(200):
        program = [[(rng.choice(("load", "store", "arithmetic")),
                     rng.randrange(alphabet), rng.randrange(alphabet))
                    for _ in range(alphabet)] for _ in range(5)]
        verdict = [rng.choice((True, False)) for _ in range(alphabet)]
        size = check_machine(program, verdict, alphabet)
        census[size] = census.get(size, 0) + 1
    print("200 adaptive machines and 1 alias example passed")
    print("minimum-certificate census", census)


if __name__ == "__main__":
    main()
