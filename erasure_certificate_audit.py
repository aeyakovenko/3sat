"""Check optimal erased-input certificates on a known zero anchor and on physical DIMACS."""
from itertools import combinations, product


def assignments(n):
    return product((0, 1), repeat=n)


def table_bit(table, bits):
    index = sum(bit << i for i, bit in enumerate(bits))
    return (table >> index) & 1


def accepts(table, positive, r, s, t, bits):
    a, b, v = bits[:r], bits[r:2*r], bits[2*r:2*r+s]
    bad = any(left and right for left, right in zip(a, b))
    full = all(left or right for left, right in zip(a, b))
    if positive:
        return not bad and (not full or any(table_bit(table, b+v+w) for w in assignments(t)))
    return bad or (full and not table_bit(table, b+v))


def qbf(table, r, s, t):
    return any(all(any(table_bit(table, u+v+w) for w in assignments(t))
                   for v in assignments(s)) for u in assignments(r))


def minimum_zero_certificate(dimension, predicate):
    zero = (0,)*dimension
    bad = [bits for bits in assignments(dimension) if predicate(bits) != predicate(zero)]
    for size in range(dimension+1):
        for fixed in combinations(range(dimension), size):
            if all(any(bits[i] for i in fixed) for bits in bad):
                return size
    raise AssertionError("complete assignment is always a certificate")


def audit_optima():
    total = 0
    for positive, r, s, t in [(True, 1, 1, 1), (True, 2, 1, 0),
                              (True, 2, 0, 1), (False, 2, 1, 0)]:
        for table in range(1 << (1 << (r+s+t))):
            pred = lambda bits: accepts(table, positive, r, s, t, bits)
            actual = minimum_zero_certificate(2*r+s, pred)
            expected = r if qbf(table, r, s, t) else r+1
            assert actual == expected
            total += 1
    print(f"{total} matrices across four quantifier shapes matched the exact certificate size")


class ProperCircuit:
    """Build proper ternary rows for a small test circuit with deterministic gates."""
    def __init__(self, marker_count):
        self.marker_count = marker_count
        self.maximum = 10 * marker_count + 9
        self.rows = []
        self.used = set()
        for forbidden in range(1,8):
            self.add([-(i+1) if forbidden >> i & 1 else i+1 for i in range(3)])
        self.witness_names = []
        self.source_comment = None
        self.inputs = []
        self.reject = []
        self.accept = []
        for j in range(1, marker_count+1):
            base = 10*j
            states = [base+d for d in (0,1,2,3,6,7)]
            for left,right in combinations(states, 2):
                self.add([-left,-right])
            self.inputs.append(self.either([base+1,base+3,base+7]))
            self.reject.extend([base,base+1])
            self.accept.extend([base+6,base+7])

    def new(self):
        self.maximum += 1
        return self.maximum

    def add(self, literals):
        assert len(set(map(abs, literals))) == len(literals)
        for dummy in range(1,4):
            if len(literals) < 3 and all(abs(lit) != dummy for lit in literals):
                literals = literals + [dummy]
        assert len(literals) == 3
        self.rows.append(tuple(literals))
        self.used.update(map(abs,literals))

    def conjunction(self, literals):
        values = iter(literals)
        result = next(values)
        for other in values:
            if other == result:
                continue
            if other == -result:
                return 1  # deliberately pinned false
            gate = self.new()
            self.add([-gate,result])
            self.add([-gate,other])
            self.add([gate,-result,-other])
            result = gate
        return result

    def either(self, literals):
        return -self.conjunction([-lit for lit in literals])

    def constrain(self, table, positive, r, s, t):
        bits = self.inputs
        a, b, v = bits[:r], bits[r:2*r], bits[2*r:2*r+s]
        w = [self.new() for _ in range(t)]
        self.witness_names = w
        source = b + v + w
        terms = [self.conjunction([var if bit else -var for var,bit in zip(source,row)])
                 for row in assignments(len(source)) if table_bit(table, row)]
        phi = self.either(terms) if terms else 1
        no_witness_ones = self.conjunction([-var for var in w]) if w else -1
        bad = self.either([self.conjunction([x,y]) for x,y in zip(a,b)])
        full = self.conjunction([self.either([x,y]) for x,y in zip(a,b)])
        if positive:
            active = self.conjunction([full,phi])
            inactive = self.conjunction([-full,no_witness_ones])
            normal = self.conjunction([-bad,self.either([active,inactive])])
        else:
            normal = self.either([bad,self.conjunction([full,-phi])])
        self.finish(normal, no_witness_ones)

    def finish(self, normal, no_witness_ones):
        escape = self.either(self.accept)
        selected = self.either([self.conjunction([-escape,normal]),
                                self.conjunction([escape,no_witness_ones])])
        self.add([self.conjunction([-self.either(self.reject),selected])])
        for name in range(1, self.maximum+1):
            if name not in self.used:
                self.add([-name])

    def document(self, digits):
        prefix = "" if self.source_comment is None else "c source " + self.source_comment.hex() + "\n"
        prefix += "c try-zero " + " ".join(map(str, self.witness_names)) + "\n"
        prefix += f"p cnf {self.maximum} {len(self.rows)+len(digits)}\n"
        prefix += "".join(" ".join(map(str,row)) + " 0\n" for row in self.rows)
        data = bytearray(prefix.encode("ascii"))
        offsets = []
        for j,d in enumerate(digits, start=1):
            data.extend(b" " * 24)
            data.extend(str(10*j+d).encode("ascii"))
            offsets.append(len(data)-1)
            data.extend(b" 1 2 0\n")
        return bytes(data), offsets


def dimacs_models(document):
    """Parse serialized bytes and independently count using ordinary DPLL."""
    header,*lines = [line for line in document.splitlines() if not line.startswith(b"c ")]
    _,_,n,m = header.split()
    rows = [tuple(map(int,line.split())) for line in lines]
    assert len(rows) == int(m) and all(len(row) == 4 and row[-1]==0 for row in rows)
    clauses = [row[:-1] for row in rows]
    assert all(len(set(map(abs,row)))==3 for row in clauses)
    assert {abs(l) for row in clauses for l in row} == set(range(1,int(n)+1))
    def count(clauses, fixed):
        while clauses:
            if any(not row for row in clauses):
                return 0
            unit = next((row[0] for row in clauses if len(row)==1), None)
            if unit is None:
                # The seven pins entail 1,2,3 are false. Branch on those
                # names first if still present; both branches are counted.
                branch = min(abs(lit) for row in clauses for lit in row)
                return count([(branch,),*clauses],fixed) + count([(-branch,),*clauses],fixed)
            fixed = fixed | {abs(unit)}
            clauses = [tuple(lit for lit in row if lit != -unit) for row in clauses if unit not in row]
        return 1 << (int(n)-len(fixed))
    return count(clauses,set())


def audit_enlarged_cube():
    for positive, t, table in [(True, 1, 0b11001100), (True, 1, 0),
                               (False, 0, 0b1000), (False, 0, 0b1111)]:
        p = 3  # one left bit, one right bit and one universal bit
        def original(bits):
            return accepts(table, positive, 1, 1, t, bits)
        def enlarged(bits):
            if any(bits[p:2*p]):
                return False
            if any(bits[2*p:]):
                return True
            return original(bits[:p])
        assert minimum_zero_certificate(3*p, enlarged) == p + minimum_zero_certificate(p, original)
        # Reading a record reveals a data bit and both flags together.
        for fixed in combinations(range(p), p-1):
            missed = next(i for i in range(p) if i not in fixed)
            values = [0]*(3*p)
            values[(p if positive else 2*p) + missed] = 1
            assert enlarged(tuple(values)) != positive
    print("Four full nine-bit cubes matched the exact bit and digit certificate bounds")


def audit_physical():
    normal_count = neighbor_count = 0
    for positive,r,s,t,table in [(True,1,1,1,0b11110000), (True,1,1,1,0b11001100), (False,1,1,0,0b1000)]:
        d = 2*r+s+1
        circuit = ProperCircuit(d)
        circuit.constrain(table,positive,r,s,t)
        base, positions = circuit.document((2,)*d)
        for bits in assignments(d):
            normal, offsets = circuit.document(tuple(2+bit for bit in bits))
            assert offsets == positions
            assert all(base[i]^normal[i] == (bits[positions.index(i)] if i in positions else 0)
                       for i in range(len(base)))
            a,b,v = bits[:r],bits[r:2*r],bits[2*r:2*r+s]
            expected = int(accepts(table,positive,r,s,t,bits))
            if positive and all(x+y==1 for x,y in zip(a,b)):
                expected = sum(table_bit(table,b+v+w) for w in assignments(t))
            assert dimacs_models(normal)==expected
            normal_count += 1
            for pos in positions:
                for flip, models in [(2,0),(4,1)]:
                    changed = bytearray(normal)
                    changed[pos] ^= flip
                    assert (changed[pos]^normal[pos]).bit_count()==1
                    assert dimacs_models(changed)==models
                    neighbor_count += 1
                mixed = bytearray(normal)
                mixed[pos] ^= 6
                assert dimacs_models(mixed) == 0
    print(f"{normal_count} normal DIMACS files and {neighbor_count} one-bit force-verdict edits checked")


def audit_source_transfer():
    # One proper clause per forbidden assignment. The complete 8-row source
    # is UNSAT. Removing any subset gives a known number of witnesses.
    templates = [0, 1, 19, 96, 127, 173, 254, 255]
    checked = 0
    for template in templates:
        circuit = ProperCircuit(3)
        w = [circuit.new() for _ in range(3)]
        circuit.witness_names = w
        clauses = []
        outputs = []
        for row in range(8):
            if (template >> row) & 1:
                polarity = [(-1 if (row >> j) & 1 else 1) for j in range(3)]
                clauses.append(tuple(sign*(j+1) for j,sign in enumerate(polarity)))
                outputs.append(circuit.either([sign*var for var,sign in zip(w,polarity)]))
        source = f"p cnf 3 {len(clauses)}\n" + "".join(
            " ".join(map(str,row)) + " 0\n" for row in clauses)
        circuit.source_comment = source.encode("ascii")
        circuit.finish(circuit.conjunction(outputs) if outputs else -1,
                       circuit.conjunction([-variable for variable in w]))
        for digits in [(2,2,2),(2,3,3),(3,2,3),(3,3,3),(6,3,2),(3,0,2),(6,2,5)]:
            document, marks = circuit.document(digits)
            assert bytes.fromhex(document.splitlines()[0].split()[-1].decode()) == source.encode()
            assert all(document[i] == ord(str(digit)) for i,digit in zip(marks,digits))
            expected = 8-template.bit_count()
            if any(digit in (0,1,4,5) for digit in digits):
                expected = 0
            elif any(digit in (6,7) for digit in digits):
                expected = 1
            assert dimacs_models(document) == expected
            checked += 1
    print(f"{checked} compiled source SAT files checked, including the stored source and overrides")


if __name__ == "__main__":
    audit_optima()
    audit_enlarged_cube()
    audit_physical()
    audit_source_transfer()
