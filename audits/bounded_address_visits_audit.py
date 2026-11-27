"""Check incremental radix-table migration and its lifetime physical probe cap."""
from collections import Counter
from itertools import product
from random import Random


class Machine:
    def __init__(self, bits, digit_bits):
        self.digit_bits = digit_bits
        self.fanout = 1 << digit_bits
        self.depth = (bits + digit_bits - 1) // digit_bits
        self.memory = {}
        self.probes = Counter()
        self.total = 0
        self.cursor = 1
        self.root = self.new_header()

    def reserve(self, size):
        start = self.cursor
        self.cursor += size
        return start

    def read(self, address):
        self.probes[address] += 1
        self.total += 1
        return self.memory.get(address, 0)

    def write(self, address, value):
        self.probes[address] += 1
        self.total += 1
        self.memory[address] = value

    def new_header(self, source=None):
        if source is None:
            source = self.reserve(self.fanout)
        header = self.reserve(3)
        self.write(header, source)
        self.write(header + 1, self.reserve(self.fanout))
        # Unused addresses start at zero, including the migration cursor.
        return header

    def visit(self, header, digit, parent_slot):
        source = self.read(header)
        target = self.read(header + 1)
        index = self.read(header + 2)
        self.write(target + index, self.read(source + index))
        if index + 1 == self.fanout:
            successor = self.new_header(target)
            if parent_slot is None:
                self.root = successor
            else:
                self.write(parent_slot, successor)
        else:
            self.write(header + 2, index + 1)
        return (target if digit <= index else source) + digit

    def access(self, address, value=None):
        """Read, or store the supplied integer; CPU state uses only scalars."""
        header = self.root
        parent_slot = None
        for level in reversed(range(self.depth)):
            digit = (address >> (level * self.digit_bits)) & (self.fanout - 1)
            slot = self.visit(header, digit, parent_slot)
            if level == 0:
                if value is None:
                    return self.read(slot)
                self.write(slot, value)
                return None
            header = self.read(slot)
            if header == 0:
                if value is None:
                    return 0
                header = self.new_header()
                self.write(slot, header)
            parent_slot = slot


def check(trace, bits, digit_bits):
    machine = Machine(bits, digit_bits)
    reference = {}
    for address, value in trace:
        previous_cost = machine.total
        result = machine.access(address, value)
        if value is None:
            assert result == reference.get(address, 0)
        else:
            reference[address] = value
            assert result is None
        assert machine.total - previous_cost <= 12 * machine.depth
    assert max(machine.probes.values()) <= 2 * machine.fanout + 2
    return max(machine.probes.values())


def main():
    actions = tuple(product((0, 3), (None, 0, 7)))
    traces = 0
    maximum = 0
    for trace in product(actions, repeat=6):
        maximum = max(maximum, check(trace, 2, 1))
        traces += 1
    print(f"{traces} exhaustive length-6 streams (radix 2), largest cell probe count {maximum}")
    rng = Random(8107)
    for digit_bits in (1, 2, 3, 4):
        traces = []
        for _ in range(35):
            requests = []
            hot = 0
            for i in range(500):
                if i % 47 == 0:
                    hot = rng.randrange(1024)
                address = hot if rng.randrange(4) else rng.randrange(1024)
                value = None if rng.randrange(2) else rng.randrange(6)
                requests.append((address, value))
            traces.append(requests)
        maximum = max(check(trace, 10, digit_bits) for trace in traces)
        print(f"radix {1 << digit_bits}: {len(traces)} clustered 500-step streams, "
              f"largest cell probe count {maximum}")


if __name__ == "__main__":
    main()
