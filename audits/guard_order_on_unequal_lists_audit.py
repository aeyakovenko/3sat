"""Exact quantifier orders for detecting false acceptance on equal inputs."""
from itertools import combinations, combinations_with_replacement, product


def state_partitions(labels, states):
    # Label new boundary states in order of first observation.
    def extend(current, used):
        if len(current) == labels:
            yield tuple(current)
            return
        for value in range(min(used+1, states)):
            yield from extend(current + [value], max(used, value+1))
    yield from extend([], 0)


def quantifier_orders():
    count = 0
    for states, guards, label_max in [(2, 1, 5), (2, 2, 5), (2, 3, 5), (2, 4, 5), (3, 2, 5)]:
        for labels in range(2, label_max+1):
            pairs = tuple(combinations(range(labels), 2))
            parts = tuple(state_partitions(labels, states))
            reports = []
            for row in parts:
                singles = tuple(row.count(row[x]) == 1 for x in range(labels))
                differences = tuple(row[x] != row[z] for x, z in pairs)
                reports.append((singles, differences))
            best_file = best_path = 0
            for family in combinations_with_replacement(reports, guards):
                file_count = min(map(sum, zip(*(s for s, _ in family))))
                path_count = min(map(sum, zip(*(d for _, d in family))))
                assert file_count <= path_count
                best_file = max(best_file, file_count)
                best_path = max(best_path, path_count)
                count += 1
            assert best_file == (guards if labels <= states else guards*(states-1)//labels)
            if labels <= states**guards:
                assert best_path >= 1
            else:
                assert best_path == 0
    return count


def field_eval(coefficients, point, prime):
    acc = 0
    for c in reversed(coefficients):
        acc = (point*acc+c) % prime
    return acc


def vanish_on(points, prime):
    coefficients = [1]
    for point in points:
        answer = [0] * (len(coefficients)+1)
        for i, c in enumerate(coefficients):
            answer[i] -= point*c
            answer[i+1] += c
        coefficients = [c % prime for c in answer]
    return coefficients


def fingerprint_checks():
    vectors = choices = 0
    for m, prime in [(2, 5), (3, 7), (4, 7)]:
        for delta in product(range(prime), repeat=m):
            if any(delta):
                assert sum(field_eval(delta, s, prime) == 0 for s in range(prime)) < m
                vectors += 1
        for size in range(m):
            for seeds in combinations(range(prime), size):
                delta = vanish_on(seeds, prime)
                assert len(delta) <= m and any(delta)
                assert all(field_eval(delta, s, prime) == 0 for s in seeds)
                choices += 1
    return vectors, choices


def one_backward_read():
    total = 0
    for m, alphabet in [(3, 2), (4, 2), (2, 3)]:
        inputs = list(product(range(alphabet), repeat=m))
        for x, y, reported in product(inputs, repeat=3):
            i = next((i for i in range(m) if y[i] != reported[i]), None)
            accept = i is not None and x[i] != y[i]
            assert not accept or x != y
            if reported == x:
                assert accept == (x != y)
            total += 1
    return total


def proper_list_formula(x, y, alphabet):
    m = len(x)
    capacity = alphabet + 2*m + m-1 + 3
    h0,h1,h2 = range(capacity-2, capacity+1)
    clauses = []
    for forbidden in product((0,1), repeat=3):
        if any(forbidden):
            clauses.append(tuple(-v if bit else v for v, bit in zip((h0,h1,h2), forbidden)))
    def add(*clause):
        clauses.append(clause + (h0,h1)[:3-len(clause)])
    rails = []
    for i in range(m):
        z = alphabet+1+i
        b = alphabet+1+m+i
        a = 1+x[i]
        other = 1+y[i]
        add(-z,a)
        add(z,-a)
        for zv,ov,bv in product((0,1), repeat=3):
            if (zv ^ ov) != bv:
                add(*(-v if value else v for v,value in zip((z,other,b), (zv,ov,bv))))
        rails.append(b)
    out = rails[0]
    for i,b in enumerate(rails[1:]):
        nxt = alphabet+2*m+1+i
        add(-out,nxt)
        add(-b,nxt)
        add(out,b,-nxt)
        out = nxt
    add(out)
    assert all(len(c)==3 and len({abs(v) for v in c}) == 3 for c in clauses)
    return capacity, clauses


def exhaustive_proper_files():
    checked = 0
    for m, alphabet in [(1,2),(2,2),(2,3),(3,2)]:
        vectors = list(product(range(alphabet), repeat=m))
        for x,y in product(vectors, repeat=2):
            capacity, clauses = proper_list_formula(x,y,alphabet)
            masks = [(sum(1 << (v-1) for v in c if v>0),
                      sum(1 << (-v-1) for v in c if v<0)) for c in clauses]
            found = any(all((pos & assignment) or (neg & ~assignment)
                            for pos,neg in masks) for assignment in range(1 << capacity))
            assert found == (x != y)
            checked += 1
    return checked


if __name__ == '__main__':
    print(f'{quantifier_orders()} guard-state families, exhausting both quantifier orders.')
    vectors, choices = fingerprint_checks()
    print(f'{vectors} nonzero difference polynomials and {choices} chosen seed sets.')
    print(f'{one_backward_read()} genuine/forged executions with at most one backward query.')
    print(f'{exhaustive_proper_files()} proper 3-CNF files checked by exhaustive truth assignments.')
