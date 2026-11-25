"""Audit sparse-prefix simulation at lookahead two, including wrap and truncation."""
from itertools import permutations, product
from random import Random


def check(initial, successor, start, steps):
    orbit = [start]
    while (nxt := successor[orbit[-1]]) != start:
        orbit.append(nxt)
    period = len(orbit)
    memory = list(initial)
    sparse = {}
    locked = False
    h = len(set(initial))
    for i in range(steps):
        a, b, c = (orbit[(i+j) % period] for j in range(3))
        actual = memory[a]
        simulated = b if locked else sparse.get(a, initial[a])
        assert simulated == actual
        memory[actual] = c
        locked = locked or simulated == b
        if not locked:
            sparse[simulated] = c
            passes = (i+period)//period
            assert len(sparse) <= (passes+1)**2*h
    return locked


def main():
    total = locks = 0
    for d in range(1,5):
        for image in product(range(d), repeat=d):
            for perm in permutations(range(d)):
                for start in range(d):
                    locks += check(image, perm, start, 4*d+1)
                    total += 1
    rng = Random(33)
    for _ in range(400):
        n = rng.randrange(5, 250)
        perm = list(range(n)); rng.shuffle(perm)
        image = rng.choices(range(n),k=n)
        check(image,perm,rng.randrange(n),rng.randrange(20*n))
    assert 0 < locks < total
    print(f'{total} exhaustive initializations, {locks} entered the forced succession; 400 larger scans passed')


if __name__ == '__main__':
    main()
