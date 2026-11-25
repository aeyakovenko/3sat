"""Audit compulsory reads coupled to writes of the following read address."""
from itertools import product
from random import Random


class Walk:
    def __init__(self, memory):
        self.data = dict(memory)
        self.head = 0
        self.steps = 0

    def visit(self, next_head):
        value = self.data.get(self.head, 0)
        self.data[value] = next_head
        self.head = next_head
        self.steps += 1
        return value


class Emulator:
    def __init__(self, data, w):
        self.mask = (1 << w) - 1
        q = 1 << (2*w)
        self.address_base = q//2
        self.value_base = q//2 + (1 << w)
        self.y, self.h = q-1, q-2
        host_bytes = 2*w//8
        words = [int.from_bytes(data[i:i+host_bytes], 'little')
                 for i in range(0, len(data), host_bytes)]
        assert len(data) >= 2*host_bytes and all(9 <= c <= 127 for c in data)
        assert all(len(words) <= v < self.address_base for v in words[:len(data)//host_bytes])
        self.walk = Walk(enumerate(words))
        step = self.walk.visit
        first = step(1)
        seed = step(self.y)
        observed = (step(seed), step(self.h), step(self.y))
        assert observed == (0, self.y, 0)
        assert self.walk.data[self.y] == self.h
        for j in range(len(words)):
            if j == 0:
                raw = first
            else:
                step(j)
                raw = step(self.y)
            assert raw == words[j]
            self.access(2*j, raw & self.mask)
            if 2*j+1 <= self.mask:
                self.access(2*j+1, raw >> w)
        assert self.walk.steps <= 5 + 10*len(words)

    def access(self, a, new=None):
        assert 0 <= a <= self.mask and self.walk.head == self.y
        step = self.walk.visit
        port = step(self.address_base + a)
        old = step(self.h)
        assert port == self.h
        assert old == 0 or self.value_base <= old <= self.value_base+self.mask
        value = old-self.value_base if old else 0
        payload = value if new is None else new
        assert 0 <= payload <= self.mask
        target = step(self.value_base+payload)
        scratch = step(self.y)
        assert target == self.address_base+a and scratch in (0,self.h)
        return value


def trial(data, w, rng):
    em = Emulator(data, w)
    width = w//8
    reference = {i//width: int.from_bytes(data[i:i+width], 'little')
                 for i in range(0,len(data),width)}
    addresses = [*reference, em.mask, 0, 1, 2, 9]
    for a in addresses:
        assert em.access(a) == reference.get(a,0)
    for _ in range(200):
        a = rng.choice(addresses) if rng.randrange(2) else rng.randrange(em.mask+1)
        v = rng.choice([0, 1, em.mask, rng.randrange(em.mask+1)])
        before = em.walk.steps
        assert em.access(a,v) == reference.get(a,0)
        reference[a] = v
        assert em.access(a) == v and em.walk.steps == before+8


def main():
    rng = Random(6137)
    # Two equal seed words, plus final bytes that numerically address original input.
    for w in (8,16,24,32):
        unit = 2*w//8
        for padding, final in product(range(unit), (9,10,32,49,127)):
            data = bytes([32])*(60*unit) + bytes([final])*padding
            trial(data,w,rng)
    for i in range(150):
        w = rng.choice((8,16,24,32))
        # Limit to the guest address capacity.
        length = rng.randrange(20, min(600,(1<<w)*(w//8))+1)
        trial(bytes(rng.randrange(9,128) for _ in range(length)),w,rng)
    print('250 protected-byte input copies and 50,000 read/write pairs verified')


if __name__ == '__main__':
    main()
