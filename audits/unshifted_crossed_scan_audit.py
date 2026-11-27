"""Exhaust small memories and partial scan orbits for M[M[p]] := p."""
from itertools import product


def underlying(memory):
    return {(min(a, b), max(a, b)) for a, b in enumerate(memory)}


def inspect(initial, order):
    mem = list(initial)
    image = set(mem)
    graph = underlying(mem)
    previous = None
    previous_clean = False
    losses = 0
    for period in range(1, 2*len(image)+3):
        start_size = len(graph)
        for p in order:
            loaded = mem[p]
            mem[loaded] = p
            after = underlying(mem)
            assert after <= graph
            for a, b in graph - after:
                assert a in image and b in image
                losses += 1
            graph = after
        assert losses <= len(image)
        assert mem[order[-1]] == loaded
        state = (tuple(mem), loaded)
        clean = len(graph) == start_size
        if previous_clean and clean:
            assert state == previous
            return period
        previous = state
        previous_clean = clean
    raise AssertionError("No repeated clean-period boundary within the image bound")


def main():
    cases = 0
    worst = 0
    for size in range(1, 7):
        for initial in product(range(size), repeat=size):
            for length in range(1, size+1):
                # Every fixed list of distinct addresses is conjugate by address
                # relabeling to precisely one such prefix length. All maps occur.
                used = inspect(initial, range(length))
                worst = max(worst, used)
                cases += 1
    prologues = 0
    for initial in product(range(3), repeat=3):
        for address, payload in product(range(3), repeat=2):
            altered = list(initial)
            altered[address] = payload
            assert len(set(altered)) <= len(set(initial)) + 1
            inspect(altered, (2, 0))
            prologues += 1
    print(f"{cases} memory/orbit cases through size 6; two clean periods by pass {worst}.")
    print(f"{prologues} preliminary-store cases on a partial nonconsecutive scan.")


if __name__ == "__main__":
    main()
