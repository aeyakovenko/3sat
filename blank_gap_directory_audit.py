"""Exhaust an interval directory for never-seen RAM input words.

Positions are ranks in a public order. A directory lookup uses the key's
stored interval ID and that interval's two endpoints. The fork counts one
logical lookup per first contact with a previously uncached gap or exposed
word. Each logical lookup costs a constant number of native probes.
"""

from itertools import combinations


class Directory:
    def __init__(self, size):
        self.owner = [0] * size
        self.bounds = {0: (0, size)} if size else {}
        self.fresh = 1
        self.moves = [0] * size

    def copy(self):
        result = object.__new__(Directory)
        result.owner = self.owner.copy()
        result.bounds = self.bounds.copy()
        result.fresh = self.fresh
        result.moves = self.moves.copy()
        return result

    def lookup(self, key):
        owner = self.owner[key]
        return self.bounds[owner] if owner is not None else None

    def remove(self, key):
        owner = self.owner[key]
        if owner is None:
            raise ValueError("already exposed")
        lo, hi = self.bounds[owner]
        small, large = (lo, key), (key + 1, hi)
        if small[1] - small[0] > large[1] - large[0]:
            small, large = large, small
        self.owner[key] = None
        if large[0] == large[1]:
            del self.bounds[owner]
            return
        self.bounds[owner] = large
        if small[0] < small[1]:
            new = self.fresh
            self.fresh += 1
            self.bounds[new] = small
            for other in range(*small):
                self.owner[other] = new
                self.moves[other] += 1


class Fork:
    def __init__(self, directory, active):
        self.directory = directory
        self.active = active
        self.exposed = set()
        self.gaps = []
        self.lookups = 0

    def read(self, key):
        # A cached gap can contain the distinguished word. It still returns
        # the active packet there. All other dummy values are slot-specific.
        if key == self.active:
            return ("active", key)
        if key in self.exposed:
            return ("exposed", key)
        if any(lo <= key < hi for lo, hi in self.gaps):
            return ("dummy", key)
        self.lookups += 1
        bounds = self.directory.lookup(key)
        if bounds is None:
            self.exposed.add(key)
            return ("exposed", key)
        self.gaps.append(bounds)
        return ("dummy", key)


def reference_gaps(size, exposed):
    gaps = []
    lo = 0
    for key in (*sorted(exposed), size):
        if lo < key:
            gaps.append((lo, key))
        lo = key + 1
    return gaps


def validate(directory, exposed):
    size = len(directory.owner)
    gaps = reference_gaps(size, exposed)
    assert sorted(directory.bounds.values()) == gaps
    for key in range(size):
        expected = next((gap for gap in gaps if gap[0] <= key < gap[1]), None)
        assert directory.lookup(key) == expected
        if expected:
            lo, hi = expected
            assert (hi - lo + 1) * 2 ** directory.moves[key] <= size + 1
        assert 2 * 2 ** directory.moves[key] <= size + 1
    return gaps


def fork_states(directory, exposed, gaps):
    """Every possible next read from every reachable abstract cache state.

    Within one gap all first reads install identical endpoints. Subsequent
    reads of any subset of that gap have the same effect on the cache.
    """
    size = len(directory.owner)
    checks = 0
    for active in set(range(size)) - exposed:
        groups = {key: ("exposed", key) for key in exposed}
        for lo, hi in gaps:
            for key in range(lo, hi):
                if key != active:
                    groups[key] = ("gap", (lo, hi))
        representatives = {group: key for key, group in groups.items()}
        for count in range(len(representatives) + 1):
            for cached in combinations(representatives, count):
                fork = Fork(directory, active)
                for group in cached:
                    fork.read(representatives[group])
                assert fork.lookups == count
                # Restore the same abstract starting state before each trial.
                for key in range(size):
                    trial = Fork(directory, active)
                    trial.gaps = fork.gaps.copy()
                    trial.exposed = fork.exposed.copy()
                    kind = "active" if key == active else "exposed" if key in exposed else "dummy"
                    assert trial.read(key) == (kind, key)
                    assert trial.lookups == int(key != active and groups[key] not in cached)
                    checks += 1
    return checks


def exhaust(size):
    seen_states = set()
    prefixes = complete = cache_checks = maximum_moves = 0

    def visit(directory, exposed):
        nonlocal prefixes, complete, cache_checks, maximum_moves
        prefixes += 1
        gaps = validate(directory, exposed)
        if exposed not in seen_states:
            seen_states.add(exposed)
            cache_checks += fork_states(directory, exposed, gaps)
        if len(exposed) == size:
            complete += 1
            maximum_moves = max(maximum_moves, sum(directory.moves))
            return
        for key in range(size):
            if key in exposed:
                continue
            child = directory.copy()
            child.remove(key)
            visit(child, exposed | {key})

    visit(Directory(size), frozenset())
    assert len(seen_states) == 2 ** size
    return prefixes, complete, cache_checks, maximum_moves


def main():
    totals = [0, 0, 0]
    for size in range(9):
        prefixes, complete, checks, maximum = exhaust(size)
        for i, count in enumerate((prefixes, complete, checks)):
            totals[i] += count
        print(f"P={size}: {complete} orders, maximum {maximum} reassigned keys in total")
    print(f"{totals[0]} deletion prefixes; {totals[1]} complete orders; "
          f"{totals[2]} fork-cache transitions.")


if __name__ == "__main__":
    main()
