"""Check the non-expanding dense-core transform and exact guest memory layout."""

from itertools import product
from random import Random


def parse(blob):
    head, body = blob.split(b"\n", 1)
    prefix, kind, bound, count = head.split()
    assert (prefix, kind) == (b"p", b"cnf")
    tokens = [int(s) for s in body.split()]
    assert len(tokens) == 4 * int(count)
    assert all(tokens[i] == 0 for i in range(3, len(tokens), 4))
    clauses = [tuple(tokens[i:i+3]) for i in range(0, len(tokens), 4)]
    assert all(len({abs(v) for v in c}) == 3 for c in clauses)
    assert all(1 <= abs(v) <= int(bound) for c in clauses for v in c)
    return clauses


def core(blob):
    clauses = parse(blob)
    names = sorted({abs(x) for c in clauses for x in c}, key=lambda a: (len(str(a)), -a))
    dense = {a: i for i, a in enumerate(names, 1)}
    assert all(len(str(i)) <= len(str(a)) for a, i in dense.items())
    triples = sorted({tuple(sorted(dense[abs(v)] * (1 if v > 0 else -1) for v in c))
                      for c in clauses})
    encoded = ('p cnf %d %d\n' % (len(names), len(triples))
               + '\n'.join('%d %d %d 0' % c for c in triples)).encode()
    assert len(encoded) <= len(blob)
    assert parse(encoded) == triples
    actual = {abs(v) for c in triples for v in c}
    assert actual == set(range(1, len(names) + 1))
    # Stronger than checking only the final SAT verdict.
    for bits in product((False, True), repeat=len(names)):
        def value(formula, assignment):
            return all(any(assignment[abs(v)] == (v > 0) for v in clause)
                       for clause in formula)
        assert value(clauses, dict(zip(names, bits))) == value(triples, dict(enumerate(bits, 1)))
    return encoded


def width(bits):
    return 16 * (((bits + 1).bit_length() + 15) // 16)


def guest_memory(blob, encoded):
    host = width(8 * len(blob))
    guest = width(8 * len(encoded))
    assert guest <= host
    hbytes = host // 8
    packed = [int.from_bytes(encoded[i:i+hbytes], 'little')
              for i in range(0, len(encoded), hbytes)] + [0]
    words = []
    for offset in range(0, 8 * len(encoded), guest):
        i, j = divmod(offset, host)
        window = packed[i] | (packed[i+1] << host)
        words.append((window >> j) & ((1 << guest) - 1))
    step = guest // 8
    expected = [int.from_bytes(encoded[i:i+step], 'little')
                for i in range(0, len(encoded), step)]
    # The untouched addresses were initially zero. Check clearing against an
    # adversarial nonzero value at every touched address after the guest image.
    touched = len(words) + 5
    memory = [13] * touched
    memory[:len(words)] = words
    memory[len(words):] = [0] * (touched - len(words))
    assert memory == expected + [0] * 5
    return guest < host


def main():
    rng = Random(9027)
    narrower = 0
    for trial in range(321):
        names = rng.sample([1, 2, 3, 7, 10, 11, 19, 90, 100, 909, 10000, 10**70 + 1],
                           rng.randint(3, 8))
        chosen = [[a * rng.choice((-1, 1)) for a in rng.sample(names, 3)]
                  for _ in range(rng.randint(1, 14))]
        lines = []
        for _ in range(rng.randint(1, 42)):
            clause = rng.sample(rng.choice(chosen), 3)
            fields = [('-' if a < 0 else '') + '0'*rng.randrange(3) + str(abs(a)) for a in clause]
            lines.append(rng.choice([' ', '\t', '   ']).join(fields + ['0']))
        header = f'p cnf {max(names)} {len(lines)}\n'
        raw = (header + '\n'.join(lines) + (' ' * 9000 if trial % 20 == 0 else '')).encode()
        narrower += guest_memory(raw, core(raw))
    assert narrower > 0
    print(f'321 length, assignment and guest-layout checks; {narrower} strict width decreases')


if __name__ == '__main__':
    main()
