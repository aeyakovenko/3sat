"""Check the dense ASCII 3-SAT projection of the scalar product-verification bit."""

from itertools import product


MAX_NAME = 17777


def identifier(bits):
    """Write the twelve bits as four octal digits following a decimal 1."""
    return int("1" + format(bits, "04o"))


def correct(bits):
    a, b, c = bits & 15, (bits >> 4) & 15, bits >> 8
    for i in range(2):
        for j in range(2):
            entry = sum(((a >> (2 * i + k)) & 1) * ((b >> (2 * k + j)) & 1) for k in range(2))
            if entry % 2 != ((c >> (2 * i + j)) & 1):
                return False
    return True


def record(name):
    return f"{name} 1 2 0\n".encode("ascii")


def audit():
    values = {identifier(bits): correct(bits) for bits in range(4096)}
    assert len(values) == 4096 and sum(values.values()) == 256
    prefix = []
    for assignment in product((False, True), repeat=3):
        if any(assignment):
            prefix.append([(-i if bit else i) for i, bit in enumerate(assignment, 1)])
    surviving = [x for x in product((False, True), repeat=3)
                 if all(any(x[abs(lit) - 1] == (lit > 0) for lit in row) for row in prefix)]
    assert surviving == [(False, False, False)]
    for name in range(4, MAX_NAME + 1):
        prefix.append([name if values.get(name, False) else -name, 1, 2])
    printed = "".join(" ".join(map(str, row)) + " 0\n" for row in prefix)
    decoded = [list(map(int, line.split())) for line in printed.splitlines()]
    assert len(decoded) == 17781
    assert all(row[-1] == 0 and len({abs(j) for j in row[:-1]}) == 3 for row in decoded)
    pinned = {abs(row[0]): row[0] > 0 for row in decoded[7:]}
    assert set(pinned) == set(range(4, MAX_NAME + 1))
    for bits in range(4096):
        row = record(identifier(bits))
        selected, first, second, end = map(int, row.split())
        assert (first, second, end) == (1, 2, 0)
        assert pinned[selected] == correct(bits)
        for i in range(12):
            changed = record(identifier(bits ^ (1 << i)))
            assert len(changed) == len(row)
            assert sum((x ^ y).bit_count() for x, y in zip(row, changed)) == 1
            if i >= 8 and correct(bits):
                assert not pinned[int(changed.split()[0])]
    print("17781 fixed proper clauses, 4096 record verdicts, 49152 one-bit changes")


if __name__ == "__main__":
    audit()
