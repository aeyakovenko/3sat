"""Exhaust one-pass writer charges and verify cumulative changed-address bounds."""

from itertools import combinations, permutations, product


def pass_audit(original, initial, exceptional, scan, delta):
    memory = list(initial)
    ports = set(original)
    assert ports <= exceptional
    assert all(a in exceptional or x == original[a] for a, x in enumerate(memory))
    writers, second = {}, set()
    out = set(exceptional)
    for i, address in enumerate(scan):
        x = memory[address]
        if address not in exceptional and x not in ports:
            k = writers[address]
            assert k < i and scan[k] in exceptional and k not in second
            second.add(k)
        memory[x] = scan[(i + delta) % len(scan)]
        writers[x] = i
        out.add(x)
        assert len(out) <= 3*len(exceptional)
    return memory, out


def main():
    count = 0
    for n in [3, 4]:
        for ports in combinations(range(n), 2):
            for original in product(ports, repeat=n):
                if len(set(original)) < 2:
                    continue
                for address, init_value in product(range(n), repeat=2):
                    initial = list(original)
                    initial[address] = init_value
                    initial_exceptions = set(ports) | {address}
                    for scan in permutations(range(n)):
                        for delta in [0, 1]:
                            mem, exc = initial, initial_exceptions
                            for _ in range(3):
                                mem, exc = pass_audit(original, mem, exc, scan, delta)
                            count += 1
    print(f"Verified three passes for {count:,} initialized cyclic scans.")


if __name__ == "__main__":
    main()
