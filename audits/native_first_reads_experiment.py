"""Exhaustive last-writer and block-rank check for a two-cell bit RAM."""

from itertools import product


def replay(op, state, incoming):
    writes = {}
    first_reads = {}

    def read(address):
        if address in writes:
            return writes[address]
        first_reads[address] = incoming(address)
        return first_reads[address]

    x = read(state ^ (op & 1))
    y = read(x ^ ((op >> 1) & 1))
    writes[y ^ ((op >> 2) & 1)] = state ^ x ^ y
    z = read(x ^ y)
    return z ^ state, first_reads, writes


def genuine_run(program, start, initial):
    states = [start]
    blocks = []
    last_writer = [None, None]
    dependencies = []
    memory = list(initial)
    for i, op in enumerate(program):
        block = replay(op, states[-1], memory.__getitem__)
        next_state, first_reads, writes = block
        states.append(next_state)
        blocks.append(block)
        dependencies.append({a: last_writer[a] for a in first_reads if last_writer[a] is not None})
        for address, value in writes.items():
            memory[address] = value
            last_writer[address] = i
    return states, blocks, dependencies


def rank_replay(program, states, genuine, dependencies, ranks, patch, initial):
    canonical = {}
    for i in sorted(range(len(program)), key=ranks.__getitem__):
        def incoming(address):
            source = dependencies[i].get(address)
            if patch and source is not None and ranks[source] >= ranks[i]:
                return genuine[i][1][address]
            for j in reversed(range(i)):
                if ranks[j] < ranks[i] and address in canonical[j][2]:
                    return canonical[j][2][address]
            return initial[address]

        canonical[i] = replay(program[i], states[i], incoming)
    return [canonical[i] for i in range(len(program))]


def run():
    initial = (0, 1)
    tested = misleading = rejected = 0
    for program in product(range(8), repeat=3):
        for start in (0, 1):
            states, genuine, dependencies = genuine_run(program, start, initial)
            for ranks in product(range(3), repeat=3):
                for patch in (False, True):
                    blocks = rank_replay(program, states, genuine, dependencies, ranks, patch, initial)
                    if patch:
                        assert blocks == genuine
                    memory = list(initial)
                    controllers_join = True
                    first_reads_glue = True
                    for i, (state, first_reads, writes) in enumerate(blocks):
                        controllers_join &= state == states[i + 1]
                        first_reads_glue &= all(memory[a] == v for a, v in first_reads.items())
                        for address, value in writes.items():
                            memory[address] = value
                    passes = controllers_join and first_reads_glue
                    assert not passes or blocks == genuine
                    misleading += controllers_join and blocks != genuine
                    rejected += not passes
                    tested += 1
    assert (tested, misleading, rejected) == (55296, 4348, 14044)
    print(f'{tested:,} cases, {misleading:,} spurious replays with matching controllers, '
          f'{rejected:,} rejected by the full check')


if __name__ == '__main__':
    run()
