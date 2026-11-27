"""Check a moving register file against direct guest reads and writes."""

from random import Random


class Machine:
    def __init__(self, initial, size, need):
        self.mem = list(initial)
        self.size = size
        self.need = need
        self.blocks = len(initial)//size
        self.looks = 0
        self.moves = 0
        self.wraps = 0
        self.start = self.blocks-1
        self.holes = self.probe(self.start)
        assert self.holes is not None
        self.value = self.mem[self.holes[0]]
        for j in self.holes:
            self.mem[j] = 0

    def probe(self, block):
        self.looks += 1
        sites = range(block*self.size, (block+1)*self.size)
        for i in sites:
            hits = [j for j in sites if self.mem[j] == self.mem[i]]
            if len(hits) >= self.need:
                return hits[:self.need]
        return None

    def load(self, i):
        return self.value if i in self.holes else self.mem[i]

    def store(self, i, z):
        if i in self.holes:
            if z == self.value:
                return
            for distance in range(1, self.blocks):
                new = (self.start+distance) % self.blocks
                holes = self.probe(new)
                if holes is not None:
                    break
            else:
                raise AssertionError('lack of eligible alternate block')
            previous = self.value
            self.value = self.mem[holes[0]]
            for old, fresh in zip(self.holes, holes):
                self.mem[fresh] = self.mem[old]
                self.mem[old] = previous
            self.moves += 1
            self.wraps += int(new < self.start)
            self.start, self.holes = new, holes
        self.mem[i] = z


def main():
    rng = Random(0x7511)
    checks = moves = wraps = looks = 0
    for bits, size, need in ((7,8,3), (8,8,4), (8,16,5), (9,16,6)):
        q = 1 << bits
        for seed in range(6):
            ref = [0]*q
            for i in range(q//6):
                ref[i] = (i+seed+2)%q
            sim = Machine(ref, size, need)
            regs = [0]*need
            for turn in range(2200):
                if turn%125 == 0:
                    blob = (turn//125+seed)%4
                    # Fresh logical phases with a new common word. Every
                    # completed initialization still has eligible alternate
                    # blocks; the two large constant runs meet in its middle.
                    for i in range(q):
                        sim.store(i,blob)
                        ref[i]=blob
                elif turn%4 == 0:
                    j=rng.randrange(need)
                    regs[j]=rng.randrange(q)
                    sim.mem[sim.holes[j]]=regs[j]
                else:
                    i=rng.choice(sim.holes) if turn%3 else rng.randrange(q)
                    # Avoid destroying the extensive common value during a phase.
                    z=(turn//125+seed)%4 if turn%5==0 else rng.randrange(q)
                    sim.store(i,z)
                    ref[i]=z
                assert [sim.mem[j] for j in sim.holes] == regs
                assert all(sim.load(i)==ref[i] for i in range(q))
                checks+=1
            moves+=sim.moves
            wraps+=sim.wraps
            looks+=sim.looks
    print(f'{checks:,} complete logical/physical comparisons, {moves:,} moves, '
          f'{wraps:,} wraparounds, {looks:,} block inspections')


if __name__ == '__main__':
    main()
