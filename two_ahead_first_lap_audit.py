"""Check first-lap locks and embed their triggering word in proper DIMACS files."""

from itertools import permutations, product

from public_crossed_communication_audit import emit_equal


def check_memory(initial, order):
    size = len(initial)
    memory = list(initial)
    image = set(initial)
    destinations = set()
    locked = False
    witnessed = False
    for i in range(3 * size):
        position, successor, payload = (order[(i+j) % size] for j in range(3))
        reply = memory[position]
        if i < size and position not in image:
            if not locked:
                assert reply == initial[position]
            if initial[position] == successor:
                assert reply == successor
                witnessed = True
        if locked:
            assert reply == successor
        if i < size and not locked and reply != successor:
            destinations.add(reply)
            assert len(destinations) <= 2 * len(image)
        locked |= reply == successor
        memory[reply] = payload
    return witnessed


def trap_length(width, stride):
    tail = 10
    for used in range(1, width // 8):
        address = tail - stride
        bits = width * address + 8 * used
        if bits + 2 > 1 << (width - 16):
            assert 0 < address < tail + abs(stride) + 1
            assert (bits + 1).bit_length() <= width
            assert (bits + 1).bit_length() > width - 16
            return address, tail, used, bits
        tail = 256 * tail + 32
    raise AssertionError("no fitting tail")


def check_file(left, right, stride):
    width = 32
    word_bytes = width // 8
    address, tail, used, bits = trap_length(width, stride)
    core = emit_equal(left, right, word_bytes).encode("ascii")
    assert len(core) <= word_bytes * address // 2
    packed = core.ljust(word_bytes * address, b" ") + b" " * (used - 1) + b"\n"
    assert len(packed) * 8 == bits
    words = [int.from_bytes(packed[i:i+word_bytes], "little")
             for i in range(0, len(packed), word_bytes)]
    assert words[address] == tail == address + stride
    assert address not in set(words) | {0}
    assert len(set(words)) <= 15

    tokens = packed.split()
    assert tokens[:2] == [b"p", b"cnf"]
    bound, rows = map(int, tokens[2:4])
    literals = list(map(int, tokens[4:]))
    assert len(literals) == 4 * rows
    clauses = [literals[i:i+3] for i in range(0, len(literals), 4)]
    names = sorted({abs(lit) for clause in clauses for lit in clause})
    assert literals[3::4] == [0] * rows and 1 <= names[0] <= names[-1] <= bound
    assert all(len({abs(lit) for lit in clause}) == 3 for clause in clauses)
    sat = any(all(any(assignment[names.index(abs(lit))] == (lit > 0)
                      for lit in clause) for clause in clauses)
              for assignment in product((0, 1), repeat=len(names)))
    assert sat == (left == right)


def main():
    scans = seeds = 0
    for size in range(1, 6):
        for initial in product(range(size), repeat=size):
            for order in permutations(range(size)):
                seeds += check_memory(initial, order)
                scans += 1
    layouts = files = 0
    for stride in (-13, -3, -1, 1, 3, 13):
        for width in range(48, 1025, 16):
            address, tail, _, bits = trap_length(width, stride)
            assert width < address < bits and bits + 2 <= (1 << width) // 128
            assert address < 9 << (width - 8)
            assert address != tail
            layouts += 1
        for left, right in product(product((0, 1), repeat=3), repeat=2):
            check_file(left, right, stride)
            files += 1
    print(f"{scans} scan initializations ({seeds} had a fresh seed), "
          f"{layouts} width/stride layouts, {files} proper padded equality files")


if __name__ == "__main__":
    main()
