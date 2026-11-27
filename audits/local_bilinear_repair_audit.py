"""Enumerate the local bilinear span and all error matrices for the 3-bit gate example."""


def dot(x, y):
    return (x & y).bit_count() % 2


def outer(x, y):
    result = 0
    for i in range(3):
        if (x >> i) & 1:
            result |= y << (3 * i)
    return result


def rank(matrix):
    image = {0}
    for i in range(3):
        row = (matrix >> (3 * i)) & 7
        image |= {v ^ row for v in image}
    return len(image).bit_length() - 1


def main():
    for a in range(8):
        for b in range(8):
            val = sum(dot(n, b) for n in range(1, 8) if a in (0, n))
            assert val % 2 == dot(a, b)
    span = {0}
    for n in range(1, 8):
        for left in range(8):
            if not dot(left, n):
                term = outer(left, n)
                span |= {x ^ term for x in span}
    identity = sum(1 << j for j in (0, 4, 8))
    assert span == {matrix for matrix in range(512) if not dot(matrix, identity)}
    assert min(rank(identity ^ x) for x in span) == 1
    for matrix in range(512):
        bias_sum = sum((-1) ** dot(outer(a, b), matrix) for a in range(8) for b in range(8))
        assert bias_sum == 64 >> rank(matrix)
    print("64 inputs, complete 256-matrix local span and all 512 binary biases passed")


if __name__ == "__main__":
    main()
