"""Check all pinnings and cuts of a four-site binary tensor ring."""

from itertools import product


def rank(rows, prime):
    matrix = [row.copy() for row in rows]
    pivot = 0
    for col in range(len(matrix[0])):
        found = next((i for i in range(pivot, len(matrix)) if matrix[i][col]), None)
        if found is None:
            continue
        matrix[pivot], matrix[found] = matrix[found], matrix[pivot]
        inverse = pow(matrix[pivot][col], -1, prime)
        for i in range(pivot+1, len(matrix)):
            factor = inverse*matrix[i][col] % prime
            matrix[i] = [(u-factor*v) % prime for u,v in zip(matrix[i], matrix[pivot])]
        pivot += 1
        if pivot == len(matrix):
            break
    return pivot


def contracted(tables, p):
    result = {}
    for x in product(range(2), repeat=4):
        value = 0
        for w in product(range(2), repeat=4):
            term = 1
            for i in range(4):
                term *= tables[i][4*x[i]+2*w[i-1]+w[i]]
            value += term
        result[x] = value % p
    return result


def check(tensor, n, p):
    tested = 0
    # Status 0 and 1 are pinnings. Status 2 is a row bit, 3 a column bit.
    for status in product(range(4), repeat=n):
        nr, nc = status.count(2), status.count(3)
        matrix = [[0] * 2**nc for _ in range(2**nr)]
        for x, value in tensor.items():
            if any(a < 2 and a != b for a,b in zip(status,x)):
                continue
            i = j = 0
            for a,b in zip(status,x):
                if a == 2:
                    i = 2*i+b
                elif a == 3:
                    j = 2*j+b
            matrix[i][j] = value
        if rank(matrix, p) != 2**min(nr,nc):
            return tested
        tested += 1
    return tested


def distinctness_degree(w):
    n, h = 2**w, 2*w
    bits = n*h
    values = bytearray(1 << bits)
    for assignment in range(len(values)):
        records = {(assignment >> (h*i)) & ((1 << h)-1) for i in range(n)}
        values[assignment] = len(records) == n
    for i in range(bits):
        block = 1 << i
        for base in range(0, len(values), 2*block):
            for j in range(base, base+block):
                values[j+block] ^= values[j]
    return max(mask.bit_count() for mask, coefficient in enumerate(values) if coefficient)


def main():
    p = 1009
    tables = [
        [864, 394, 776, 911, 430, 41, 265, 988],
        [523, 497, 414, 940, 802, 849, 310, 991],
        [488, 366, 597, 913, 929, 223, 516, 142],
        [288, 143, 773, 97, 633, 818, 256, 931],
    ]
    total = check(contracted(tables, p), 4, p)
    assert total == 256
    # At three sites the all-pairs sign already works over F3. At four,
    # the forced sign pattern at every 2-face fails a balanced cut.
    for n, succeeds in [(3, True), (4, False)]:
        phase = {x: pow(2, sum(x)*(sum(x)-1)//2, 3)
                 for x in product(range(2), repeat=n)}
        assert (check(phase, n, 3) == 4**n) == succeeds
    assert [distinctness_degree(w) for w in (1,2)] == [2,8]
    print(f"{total} full-rank pinned cuts on one four-vertex trivalent cycle over F_{p}; "
          "the F_3 sign-pattern tests agree at three and four sites. List degrees are 2 and 8.")


if __name__ == "__main__":
    main()
