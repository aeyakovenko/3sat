"""Exhaust binary-branch native-word RAM programs on selected tiny SAT inputs."""

from functools import lru_cache
from itertools import product
from operator import and_, or_, xor, add, sub, mul, eq, lt


def mask(values):
    return sum(1 << i for i, value in enumerate(values) if value)


class Machine:
    def __init__(self, width, samples):
        self.width = width
        self.size = 1 << width
        self.word_mask = self.size - 1
        self.domain = (1 << len(samples)) - 1
        self.constants = tuple((c,) * len(samples) for c in range(self.size))
        self.memory = tuple(zip(*samples)) + (self.constants[0],) * (self.size - 2)
        signed = lambda a: (a + self.size // 2) % self.size - self.size // 2
        self.comparisons = (eq, lt, lambda a, b: signed(a) < signed(b))
        self.operations = (
            and_, or_, xor, add, sub, mul, lambda a, b: a << b, lambda a, b: a >> b,
            lambda a, b: signed(a) >> b, lambda a, b: a << (b % width),
            lambda a, b: a >> (b % width), lambda a, b: signed(a) >> (b % width),
            lambda a, b: (a << (b % width)) | (a >> (width - b % width)),
            lambda a, b: (a >> (b % width)) | (a << (width - b % width)),
        ) + self.comparisons + tuple(lambda a, b, op=op: not op(a, b) for op in self.comparisons)

    @lru_cache(None)
    def pair_cuts(self, a, b):
        return {mask(map(op, u, v)) for u, v in ((a, b), (b, a)) for op in self.comparisons}

    @lru_cache(None)
    def cuts(self, registers):
        cuts = {0, self.domain}
        for i, a in enumerate(registers):
            for b in self.constants + registers[:i]:
                cuts.update(self.pair_cuts(a, b))
        return cuts

    @lru_cache(None)
    def alu(self, registers):
        words = self.constants + registers
        return {tuple(op(a, b) & self.word_mask for a, b in zip(u, v))
                for u, v in product(words, repeat=2) for op in self.operations}

    @lru_cache(None)
    def output_bits(self, word):
        return {mask((x >> j) & 1 for x in word) for j in range(self.width)}

    @staticmethod
    def load(memory, address):
        return tuple(memory[addr][i] for i, addr in enumerate(address))

    @staticmethod
    def store(memory, address, value):
        return tuple(tuple(value[i] if addr == cell else memory[cell][i]
                           for i, addr in enumerate(address)) for cell in range(len(memory)))

    def decision_search(self, target, free_bits=False):
        def may_return(domain, regs):
            if domain & target in (0, domain):
                return True
            if free_bits:
                matches = (0, domain) if free_bits == "complement" else (0,)
                return any(((bit ^ target) & domain) in matches
                           for r in regs for bit in self.output_bits(r))
            return False

        @lru_cache(None)
        def search(domain, regs, memory, steps):
            if may_return(domain, regs):
                return True
            if steps == 0:
                return False
            if steps == 1 and not free_bits:
                return any(domain & (cut ^ target) in (0, domain) for cut in self.cuts(regs))

            for cut in self.cuts(regs):
                left = domain & cut
                right = domain ^ left
                if left and right and search(left, regs, memory, steps - 1):
                    if search(right, regs, memory, steps - 1):
                        return True

            words = self.constants + regs
            results = self.alu(regs) | {self.load(memory, address) for address in words}
            for result in results.difference(words):
                if steps == 1:
                    if may_return(domain, (result,)):
                        return True
                    continue
                if search(domain, tuple(sorted(regs + (result,))), memory, steps - 1):
                    return True

            # A store needs a subsequent load; with constant-verdict leaves
            # there must also be a subsequent comparison.
            if steps >= (2 if free_bits else 3):
                updates = {self.store(memory, a, v) for a, v in product(words, repeat=2)}
                for updated in updates - {memory}:
                    if search(domain, regs, updated, steps - 1):
                        return True
            return False

        return lambda domain, steps: search(domain, (), self.memory, steps)


def sat(positive, negative, k):
    return any(assignment and not positive & ~assignment and not negative & assignment
               for assignment in range(1 << k))


def minimum_suites(machine, target, full_search):
    # These predictors all start by loading both input words. The last
    # two instructions are two branching comparisons, or an ALU and a comparison.
    registers = tuple(sorted(machine.memory[:2]))
    words = machine.constants + registers
    cuts = machine.cuts(registers)
    oriented = cuts | {cut ^ machine.domain for cut in cuts}
    predictions = {(root & yes) | ((machine.domain ^ root) & no)
                   for root, yes, no in product(oriented, repeat=3)}
    for value in machine.alu(registers):
        for word in words:
            predictions.update(machine.pair_cuts(value, word))
    predictions |= {result ^ machine.domain for result in predictions}

    # Mark a suite if one predictor agrees throughout it; close under deletion.
    covered = bytearray(machine.domain + 1)
    for prediction in predictions:
        covered[machine.domain ^ prediction ^ target] = 1
    for suite in range(machine.domain, 0, -1):
        if covered[suite]:
            bits = suite
            while bits:
                bit = bits & -bits
                covered[suite ^ bit] = 1
                bits ^= bit
    assert all(covered[suite] for suite in range(len(covered)) if suite.bit_count() <= 5)
    candidates = [s for s in range(len(covered)) if s.bit_count() == 6 and not covered[s]]
    minimum = [s for s in candidates if not full_search(s, 4)]
    assert minimum == [5570, 5576, 5584]
    assert len(predictions) == 3692
    return minimum


def check_four_load_prefix():
    # k=8, n=16: four dense four-bit words. Restrict each word to 0 or 1.
    inputs = list(product((0, 1), repeat=4))
    columns = tuple(zip(*inputs))
    blank = (0,) * len(inputs)
    memory = columns + (blank,) * 12
    literals = tuple((c,) * len(inputs) for c in range(16))
    target = mask(not ((p0 & m0) or (p1 & m1)) for p0, p1, m0, m1 in inputs)
    states = {()}
    for _ in range(4):
        next_states = set(states)
        for regs in states:
            for address in literals + regs:
                value = Machine.load(memory, address)
                if value not in literals and value not in regs:
                    next_states.add(tuple(sorted(regs + (value,))))
        states = next_states
    signed = lambda a: (a + 8) % 16 - 8
    for regs in states:
        for a, b in product(literals + regs, repeat=2):
            for compare in (eq, lt, lambda x, y: signed(x) < signed(y)):
                outcome = mask(map(compare, a, b))
                assert outcome not in (target, target ^ 65535)
    print(f"Sixteen-bit catalog: {len(states)} four-load register sets, no final comparison works.")


def check_no_alu_fixture():
    outcomes = {}
    for x0, x1, y0, y1 in product((0, 1), repeat=4):
        p0, p1, m0, m1 = 4+x0, 4+x1, 8+y0, 8+y1
        actual = sat(p0 | (p1 << 4), m0 | (m1 << 4), 8)
        assert actual == (not (x0 and y0) and not (x1 and y1))
        outcomes[(x0, x1, y0, y1)] = actual
    for i in range(4):
        assert any(value != outcomes[bits[:i] + (1-bits[i],) + bits[i+1:]]
                   for bits, value in outcomes.items())
    # Use bitmasks for all sets of literal load addresses and of injected
    # nonzero low literals. More sites at the same address cannot help.
    for literal_loads in range(16):
        for injected in range(0, 16, 2):
            for indirect in (0, 1):
                sites = literal_loads.bit_count() + injected.bit_count() + indirect
                if sites <= 3:
                    reachable = literal_loads | ((1 | injected) if indirect else 0)
                    assert reachable.bit_count() <= 3
    print("Five-slot looping, no ALU: address bound and all four essential inputs verified.")


def main():
    check_four_load_prefix()
    check_no_alu_fixture()
    samples = [(i % 4, i // 4) for i in range(16)]
    native = Machine(2, samples)
    pair_target = mask(sat((x & 1) | ((y & 1) << 1), (x >> 1) | (y & 2), 2)
                       for x, y in samples)
    plane_target = mask(sat(p, m, 2) for p, m in samples)
    assert not native.decision_search(pair_target)(native.domain, 4)
    print("Four-bit variable-pair encoding: no program in four steps.", flush=True)
    plane_search = native.decision_search(plane_target)
    assert not plane_search(native.domain, 4)
    for suite in minimum_suites(native, plane_target, plane_search):
        rows = [i for i in range(16) if suite >> i & 1]
        assert all(plane_search(suite ^ (1 << i), 4) for i in rows)
        print("Minimum four-step hitting set:",
              [(samples[i], (plane_target >> i) & 1) for i in rows], flush=True)

    three_bit_samples = [(p, m) for m in range(4, 8) for p in range(4)]
    larger = Machine(3, three_bit_samples)
    six_target = mask(sat(p, m, 3) for p, m in three_bit_samples)
    assert not larger.decision_search(six_target)(larger.domain, 4)
    print("Six-bit sign planes: no four-step program even on the 16 pinned inputs.", flush=True)

    for k in (1, 2, 3):
        all_negative = (1 << k) - 1
        for p, m in product(range(1 << k), repeat=2):
            assert sat(p, m, k) == (m != all_negative and (p & m) == 0)
    for x, y in samples:
        pair_program = x != 3 and (y < 2 if x == 2 else y < 3)
        assert pair_program == bool(pair_target >> (x + 4*y) & 1)
    print("Upper programs checked on every input at each claimed size.", flush=True)

    for mode in ("plain", "complement"):
        free = native.decision_search(plane_target, free_bits=mode)
        three = free(native.domain, 3)
        four = free(native.domain, 4)
        assert not three and four == (mode == "complement")
        print(f"Free register-bit return ({mode}): depth three {three}, depth four {four}", flush=True)
    for p, m in samples:
        output_bit = not (p & 1) if m == 1 else not (m & (2 if p >= 2 else 1))
        assert output_bit == sat(p, m, 2)


if __name__ == "__main__":
    main()
