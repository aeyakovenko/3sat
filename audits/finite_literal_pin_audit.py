"""Check equal-length proper restrictions and assignment search with fallible candidates."""

from itertools import product

from table_probe_context_audit import satisfiable


def encoded(clauses, bound, byte_length=None):
    header = f"p cnf {bound} {len(clauses)}\n"
    records = [" ".join(map(str, clause)) + " 0\n" for clause in clauses]
    raw = (header + "".join(records)).encode("ascii")
    if byte_length is None:
        return raw
    assert len(raw) <= byte_length
    return raw.ljust(byte_length, b" ")


def parse_sparse(file):
    header, body = file.split(b"\n", 1)
    kind, syntax, bound, count = header.split()
    assert (kind, syntax) == (b"p", b"cnf")
    words = tuple(map(int, body.split()))
    assert len(words) == 4 * int(count)
    assert words[3::4] == (0,) * int(count)
    clauses = [words[i:i+3] for i in range(0, len(words), 4)]
    for clause in clauses:
        assert len(set(map(abs, clause))) == 3
        assert all(0 < abs(lit) <= int(bound) for lit in clause)
    return clauses


def add_pin(clauses, variable, value):
    y, z = [other for other in (1, 2, 3) if other != variable][:2]
    lit = variable if value else -variable
    clauses.extend((lit, sy * y, sz * z) for sy, sz in product((-1, 1), repeat=2))


def evaluates(clauses, assignment):
    return all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)


def verified_search(clauses, names, bound, length, candidates):
    for query in candidates:
        prefix = clauses.copy()
        assignment = {}
        for name in names:
            restricted = prefix.copy()
            add_pin(restricted, name, False)
            verdict = query(encoded(restricted, bound, length))
            if verdict is None:
                break
            assignment[name] = not verdict
            if verdict:
                prefix = restricted
            else:
                add_pin(prefix, name, True)
        else:
            if evaluates(clauses, assignment):
                return True
    return False


def check():
    formulas = restrictions = searches = 0
    wrong = [lambda _: None, lambda _: False, lambda _: True,
             lambda data: bool(sum(data) % 3)]
    correct = lambda data: satisfiable(parse_sparse(data))
    for names in ((1, 2, 3), (1, 10**29 + 7, 10**31 + 11), (19, 47, 83)):
        bound = max(names) + 10**60  # Valid unused identifiers.
        all_clauses = [tuple(i*s for i, s in zip(names, signs))
                       for signs in product((-1, 1), repeat=3)]
        for mask in range(1 << len(all_clauses)):
            clauses = [clause for i, clause in enumerate(all_clauses) if mask >> i & 1]
            assignments = [dict(zip(names, bits)) for bits in product((False, True), repeat=3)]
            models = [assignment for assignment in assignments if evaluates(clauses, assignment)]
            full = clauses.copy()
            for name in names:
                add_pin(full, name, False)
            length = len(encoded(full, bound)) + 20
            for pins in product((None, False, True), repeat=3):
                guarded = clauses.copy()
                imposed = {name: value for name, value in zip(names, pins) if value is not None}
                for name, value in imposed.items():
                    add_pin(guarded, name, value)
                raw = encoded(guarded, bound, length)
                assert len(raw) == length
                expected = any(all(assignment[x] == value for x, value in imposed.items())
                               for assignment in models)
                assert correct(raw) == expected
                restrictions += 1
            assert not verified_search(clauses, names, bound, length, wrong) or bool(models)
            assert verified_search(clauses, names, bound, length, wrong + [correct]) == bool(models)
            searches += 2
            formulas += 1
    print(f"{formulas} formulas, {restrictions} same-length restrictions, "
          f"{searches} verified searches with fallible oracles")


if __name__ == "__main__":
    check()
