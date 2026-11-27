"""Check the literal switch bytes and the positive/negative RAM-pair instances."""
from itertools import product

import pycosat


def template(block_count):
    limit = 30 * block_count + 3
    names = set(range(12, limit + 1, 10))
    rows = []
    # Each choice of signs forbids its unique all-false literal evaluation.
    for assignment in range(1, 8):
        rows.append([-(i+1) if assignment & (1 << i) else i+1 for i in range(3)])
    for var in sorted(set(range(4, limit+1)) - names):
        rows.append([-var, 1, 2])
    for group in range(block_count):
        triple = [10 * (3*group + i + 1) + 2 for i in range(3)]
        for assignment in range(7):
            rows.append([-v if assignment & (1 << i) else v for i, v in enumerate(triple)])

    output = bytearray(f"p cnf {limit} {len(rows)}\n".encode("ascii"))
    sites, clause_sites = [], []
    gap = b" " * (64 * (block_count+2).bit_length())
    for i, row in enumerate(rows):
        live = []
        for lit in row:
            output.extend(str(lit).encode("ascii"))
            if i >= len(rows) - 7*block_count and lit > 0:
                live.append(len(sites))
                sites.append(len(output)-1)
            output.extend(gap)
        output.extend(b"0\n")
        if live:
            clause_sites.append(live)
    width = 12 * (8*len(output)+1).bit_length()
    assert len({(8*pos)//width for pos in sites}) == 12*block_count
    assert all(8*(b-a) > 2*width for a, b in zip(sites, sites[1:]))
    assert all(output[pos] == ord("2") for pos in sites)
    return output, sites, clause_sites


def evaluate(image, sites, enable):
    physical = image[:]
    for i, offset in enumerate(sites):
        if not enable & (1 << i):
            physical[offset] ^= 1
    lines = physical.decode("ascii").splitlines()
    _, _, names, count = lines[0].split()
    clauses = []
    for line in lines[1:]:
        row = [int(token) for token in line.split()]
        assert len(row) == 4 and row[3] == 0 and len({abs(x) for x in row[:3]}) == 3
        clauses.append(row[:3])
    assert len(clauses) == int(count)
    assert {abs(x) for c in clauses for x in c} == set(range(1, int(names)+1))
    models = list(pycosat.itersolve(clauses))
    assert len(models) <= 1
    return bool(models)


if __name__ == "__main__":
    image, sites, clauses = template(1)
    verdicts = [evaluate(image, sites, mask) for mask in range(1 << len(sites))]
    assert sum(verdicts) == 189
    assert all(answer == all(any(mask >> i & 1 for i in c) for c in clauses)
               for mask, answer in enumerate(verdicts))
    pairs = []
    for selection in product(*clauses):
        positive = sum(1 << i for i in selection)
        for last in selection:
            negative = positive ^ (1 << last)
            assert verdicts[positive] and not verdicts[negative]
            pairs.append((positive, negative))
    assert len(set(pairs)) == 168
    for blocks in range(2, 9):
        image, sites, clauses = template(blocks)
        chosen = [c[(j+blocks) % len(c)] for j, c in enumerate(clauses)]
        positive = sum(1 << i for i in chosen)
        assert evaluate(image, sites, positive)
        assert not evaluate(image, sites, positive ^ (1 << chosen[-1]))
    print("Parsed and solved every one-block mask: 4096 files, 189 unique positives.")
    print("Checked all 168 minimal-positive/last-read pairs and physical examples through eight blocks.")
