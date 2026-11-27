"""Check the interval representation on finite self-marking RAM executions."""

from itertools import product


def next_address(op, p, x, q):
    if op == 'p+x':
        return (p+x) % q
    if op == 'p-x':
        return (p-x) % q
    return (x-p) % q


def color_runs(op, q, marker, length):
    if op == 'x-p':
        order = []
        previous = None
        v = 0
        while True:
            order.append(v)
            others = {(-v) % q, (marker-v) % q} - {v, previous}
            if not others:
                break
            assert len(others) == 1
            previous, v = v, others.pop()
    else:
        increment = marker if op == 'p+x' else -marker
        order = [(i*increment) % q for i in range(q)]
        boundary = next(i for i in range(q)
                        if inside(order[i-1], q, length) != inside(order[i], q, length))
        order = order[boundary:] + order[:boundary]
    assert len(set(order)) == len(order) == q
    runs = []
    for v in order:
        if not runs or inside(runs[-1][-1], q, length) != inside(v, q, length):
            runs.append([])
        runs[-1].append(v)
    assert len(runs) <= 2*abs(marker)+1
    return runs


def inside(v, q, length):
    return min(v, q-v) <= length


def check_cover(mask, runs):
    extra = 0
    for run in runs:
        part = tuple(mask >> v & 1 for v in run)
        components = sum(b and (i == 0 or not part[i-1]) for i, b in enumerate(part))
        touching = int(part[0] != 0) + int(part[-1] != 0)
        if all(part):
            touching = 1
        extra += components - touching
    assert extra <= 1


def audit(op, q, marker, memory, p, runs):
    written = 0
    seen = set()
    cuts = 0
    while (p, written) not in seen:
        seen.add((p, written))
        previously_marked = written >> p & 1
        x = marker if previously_marked else memory[p] if p < len(memory) else 0
        written |= 1 << p
        new = next_address(op, p, x, q)
        if p < len(memory) and not previously_marked:
            assert not inside(new, q, len(memory))
            check_cover(written, runs)
            cuts += 1
        p = new
    return cuts


def main():
    traces = cuts = 0
    for q, length in ((32, 3), (64, 4)):
        for marker, op in product((-3, -1, 1, 3), ('p+x', 'p-x', 'x-p')):
            runs = color_runs(op, q, marker, length)
            for memory in product((q//3, q//2), repeat=length):
                for p in range(q):
                    cuts += audit(op, q, marker, memory, p, runs)
                    traces += 1
    print(f"{traces} complete finite traces and {cuts} fresh-physical-read cuts checked")


if __name__ == "__main__":
    main()
