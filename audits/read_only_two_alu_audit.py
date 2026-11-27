"""Check the aligned sensitive DIMACS base and the instruction support cases."""

from collections import Counter
from itertools import combinations, product


def aligned_base(j):
    count = 10**j
    byte_length = 128 * (j + 1) * count
    width = 16 * (((8 * byte_length + 1).bit_length() + 15) // 16)
    word_bytes = width // 8
    assert word_bytes >= 4

    def field(data):
        assert len(data) <= word_bytes
        return data.ljust(word_bytes)

    header = field(b"p") + field(b" cnf") + field(b" 3")
    header += b"1".rjust(word_bytes) + b"0" * j
    header += b" " * ((-len(header) - 1) % word_bytes) + b"\n"
    clauses = []
    for assignment in product((0, 1), repeat=3):
        if assignment != (1, 0, 0):
            clauses.append(tuple(i * (-1 if b else 1)
                                 for i, b in enumerate(assignment, 1)))
    clauses.extend([(1, 2, 3)] * (count - len(clauses)))
    output = bytearray(header)
    for clause in clauses:
        for lit in clause:
            output.extend(field(f" {'-' if lit < 0 else ' '}{abs(lit)}".encode()))
        output.extend(field(b" 0"))
        output.extend(b" " * (word_bytes - 1) + b"\n")
    assert len(output) <= byte_length
    output.extend(b" " * (byte_length - len(output)))
    return bytes(output), word_bytes, len(header), count


def violated(assignment, clause):
    return all(assignment[abs(lit) - 1] != (lit > 0) for lit in clause)


def audit_base(j):
    source, word_bytes, first_clause, count = aligned_base(j)
    header, contents = source.split(b"\n", 1)
    assert header.split() == [b"p", b"cnf", b"3", str(count).encode()]
    lines = [line.split() for line in contents.splitlines() if line.strip()]
    assert len(lines) == count
    assert all(len(line) == 4 and line[-1] == b"0" for line in lines)
    clauses = [tuple(map(int, line[:-1])) for line in lines]
    frequencies = Counter(clauses)
    penalties = {
        a: sum(k for c, k in frequencies.items() if violated(a, c))
        for a in product((False, True), repeat=3)
    }
    assert [a for a, v in penalties.items() if v == 0] == [(True, False, False)]
    assert all(b % 4 == 0 for b in source[::word_bytes])
    residues = set()
    for i in range(7, count):
        sign = first_clause + 5 * i * word_bytes + 1
        assert source[sign - 1:sign + 2] == b"  1"
        changed = b"-" + source[sign + 1:sign + word_bytes - 1]
        edited = (int(changed), *clauses[i][1:])
        assert all(v - violated(a, clauses[i]) + violated(a, edited) > 0
                   for a, v in penalties.items())
        residues.add((sign // word_bytes) % 4)
    assert residues == set(range(4))
    return word_bytes * 8, count - 7


def support_cases():
    operands = [set(a) for n in (0, 1, 2) for a in combinations("pyx", n)]
    cases = Counter()
    for address, accumulator in product(operands, repeat=2):
        if "p" not in address:
            case = "cursor forgets old p"
        elif address == {"p"}:
            case = "public unary cursor"
        elif address == {"p", "x"}:
            case = "cursor uses p and raw x"
        else:
            assert address == {"p", "y"}
            if "y" not in accumulator:
                case = "accumulator forgets old y"
            elif "x" not in accumulator:
                case = "no raw operand in either update"
            else:
                assert accumulator == {"y", "x"}
                case = "jointly persistent row"
        cases[case] += 1
    assert sorted(cases.values()) == [1, 2, 4, 7, 7, 28]
    return sum(cases.values())


if __name__ == "__main__":
    for j in (2, 3):
        width, alternatives = audit_base(j)
        print(f"j={j}: w={width}, {alternatives} single-word UNSAT alternatives")
    print(f"{support_cases()} ordered operand-support pairs")
