"""Check homogeneous DIMACS word edits and their five-instruction triple test."""
from itertools import product


TAIL = b"3 1 2 0\n"


def word_pair(width_bytes):
    base = TAIL.ljust(width_bytes - 1, b" ") + b"-"
    return base, base[:-1] + b" "


def encode(width_bytes, number, edits):
    gadget = []
    for forbidden in product((0, 1), repeat=3):
        if any(forbidden):
            literals = [-i if value else i for i, value in enumerate(forbidden, 1)]
            gadget.append((" ".join(map(str, literals)) + " 0\n").encode())
    prefix = f"p cnf 3 {number + 8}\n".encode() + b"".join(gadget)
    prefix += b" " * ((-len(prefix) - 1) % width_bytes) + b"-"
    words = word_pair(width_bytes)
    return prefix + b"".join(words[int(i in edits)] for i in range(number)) + TAIL


def entails_sat(data):
    header, *rest = data.decode().splitlines()
    _, _, variables, number = header.split()
    tokens = list(map(int, " ".join(rest).split()))
    clauses = []
    assert len(tokens) == 4 * int(number)
    for start in range(0, len(tokens), 4):
        *clause, zero = tokens[start:start + 4]
        assert zero == 0 and len(set(map(abs, clause))) == 3
        clauses.append(clause)
    return any(all(any(assignment[abs(lit) - 1] == (lit > 0) for lit in row)
                   for row in clauses)
               for assignment in product((False, True), repeat=int(variables)))


def main():
    checked_files = 0
    for width in (12, 16, 60, 570):
        original = encode(width, 7, set())
        for switches in product((0, 1), repeat=7):
            edits = {i for i, bit in enumerate(switches) if bit}
            file = encode(width, 7, edits)
            changed_bytes = [i for i, (a, b) in enumerate(zip(original, file)) if a != b]
            assert len(changed_bytes) == len(edits)
            assert all(i % width == width - 1 for i in changed_bytes)
            assert entails_sat(file) == (not edits)
            checked_files += 1

    periods = (60, 570, 1080, 1590)
    for width in periods:
        mod = 256**width
        scale = mod // 256
        a, b = [int.from_bytes(x, "little") for x in word_pair(width)]
        highs = [((x % mod) // scale) for x in (a*a, a*b, b*b)]
        assert highs == [38, 143, 248]
        for x, y, z in product((a, b), repeat=3):
            assert ((x*y) % mod < z) == (x == y == z == a)

    prefix = int.from_bytes(TAIL, "little")
    u = 255*prefix - 32*256**len(TAIL)
    assert u*u < 256**59
    assert pow(256, 510, 255**2) == 1
    print(f"{checked_files} strict DIMACS files; eight triple patterns at each of {periods} bytes")
    print("Top bytes of the three products: 38, 143, 248; word-size period verified")


if __name__ == "__main__":
    main()
