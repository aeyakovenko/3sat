"""Finite, exact checks of the hidden-shift identities and physical layout.

The small proper files use direct Walsh butterflies, not the enormous upstream
recursive Fourier templates. No SAT solver or external Python package is used.
"""
from itertools import product
from random import Random


def walsh(values):
    result = list(values)
    span = 1
    while span < len(result):
        for block in range(0, len(result), 2 * span):
            for off in range(span):
                left, right = block + off, block + off + span
                a, b = result[left], result[right]
                result[left], result[right] = (a+b) % 5, (a-b) % 5
        span *= 2
    return result


def field_shift(values, shift):
    freq = walsh(values)
    signs = [1]
    for bit in range((len(values)-1).bit_length()):
        other = -1 if shift >> bit & 1 else 1
        signs.extend([other*s for s in signs])
    scale = pow(len(values), -1, 5)
    return [(scale*x) % 5 for x in walsh([s*z for s,z in zip(signs, freq)])]


def zeta(values, upper=False):
    result = list(values)
    for bit in range((len(result)-1).bit_length()):
        for i in range(len(result)):
            if bool(i >> bit & 1) != upper:
                result[i] ^= result[i ^ (1 << bit)]
    return result


def gf4_mul(a, b):
    value = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
    return value ^ (7 if value & 4 else 0)


def gf4_translate(coefficients, offsets):
    products = [1]
    for offset in offsets:
        products += [gf4_mul(x, offset) for x in products]
    weighted = zeta([gf4_mul(x,y) for x,y in zip(coefficients,products)], upper=True)
    return [gf4_mul(x,gf4_mul(y,y)) for x,y in zip(weighted,products)]


def audit_fields():
    assert [gf4_mul(a,a) for a in range(4)] == [0,1,3,2]
    assert [4,2,2,4] == [3*3 % 5, (1-2)*3 % 5, (1-2)*3 % 5,3*3 % 5]
    rng = Random(8185)
    cases = 0
    for k in range(9):
        v = 1 << k
        vectors = product(range(2), repeat=v) if k <= 3 else (
            [rng.randrange(4) for _ in range(v)] for _ in range(4))
        for values in vectors:
            values = list(values)
            offsets = range(v) if k <= 4 else rng.sample(range(v), 12)
            for s in offsets:
                desired = [values[j^s] for j in range(v)]
                assert field_shift(values, s) == desired
                coeff = gf4_translate(zeta(values), [2]*k)
                moved = gf4_translate(coeff, [2 ^ (s >> j & 1) for j in range(k)])
                assert zeta(moved) == desired
                cases += 1
    return cases


class Formula:
    """Two shared, fresh padding variables; the legal inputs are given by pins."""

    def __init__(self):
        self.last = 2
        self.rows = []

    def fresh(self):
        self.last += 1
        return self.last

    def clause(self, *lits):
        assert len({abs(x) for x in lits}) == len(lits)
        pads = list(range(1, 4-len(lits)))
        assert all(abs(x) > 2 for x in lits)
        for signs in product((-1,1), repeat=len(pads)):
            self.rows.append(lits + tuple(d*s for d,s in zip(pads,signs)))

    def equality(self, x, y):
        self.clause(-x,y)
        self.clause(x,-y)

    def field(self):
        bits = [self.fresh() for _ in range(5)]
        for i in range(5):
            for j in range(i):
                self.clause(-bits[i], -bits[j])
        # (b0 OR ... OR b4) using a chain of two fresh variables.
        s,t = self.fresh(),self.fresh()
        self.clause(bits[0],bits[1],s)
        self.clause(-s,bits[2],t)
        self.clause(-t,bits[3],bits[4])
        return bits

    def input(self, allowed):
        bits = self.field()
        for i in set(range(5)) - set(allowed):
            self.clause(-bits[i])
        return bits

    def gate(self, left, right, op):
        assert left is not right
        out = self.field()
        for a,b in product(range(5),repeat=2):
            self.clause(-left[a],-right[b],out[op(a,b) % 5])
        return out

    def transform(self, values):
        result = list(values)
        step = 1
        while step < len(result):
            for base in range(0,len(result),2*step):
                for index in range(base,base+step):
                    a,b = result[index],result[index+step]
                    result[index] = self.gate(a,b,lambda x,y:x+y)
                    result[index+step] = self.gate(a,b,lambda x,y:x-y)
            step *= 2
        return result

    def serialize(self):
        width = self.last.bit_length()
        def letter(i):
            return '7' + format(i,'0%db' % width).translate(str.maketrans('01','12'))
        def signed(i):
            return ('-' if i < 0 else '') + letter(abs(i))
        header = f"p cnf {letter((1<<width)-1)} {len(self.rows)}"
        return '\n'.join([header]+[' '.join(map(signed,row))+' 0' for row in self.rows]).encode(), letter


def check_files(k):
    n = Formula()
    v = 1 << k
    inp = [n.input((0,1)) for _ in range(v)]
    signs = [n.input((1,4)) for _ in range(k)]
    phases = [n.input((1,))]
    for s in signs:
        phases += [n.gate(old,s,lambda a,b:a*b) for old in phases]
    outputs = n.transform([n.gate(u,z,lambda a,b:a*b)
                           for u,z in zip(n.transform(inp),phases)])
    scale = pow(v,-1,5)
    normalized = [n.gate(old,phases[0],lambda a,b:a*b*scale) for old in outputs]
    claimed = [n.fresh() for _ in range(v)]
    for y,word in zip(claimed,normalized):
        n.equality(y,word[1])
    raw,letter = n.serialize()
    lines=raw.splitlines()
    bound,count = map(int, lines[0].split()[2:])
    assert count == len(lines)-1
    rows=[]
    for line in lines[1:]:
        a,b,c,z=map(int,line.split())
        assert z==0 and len({abs(a),abs(b),abs(c)})==3
        assert max(abs(a),abs(b),abs(c))<=bound
        rows.append((a,b,c))

    # Both padding signs are present in every padded clause. Fixing both
    # common dummies arbitrarily yields an equivalent instance. The remaining
    # Tseitin and one-hot gates propagate forward under complete input pins.
    paddings={int(letter(1)):True,int(letter(2)):True}
    retained=[]
    for row in rows:
        if any(abs(lit) in paddings and lit>0 for lit in row):
            continue
        retained.append(tuple(lit for lit in row if abs(lit) not in paddings))

    def force(assumptions):
        value=dict(assumptions)
        while True:
            before=len(value)
            for row in retained:
                if any(value.get(abs(lit))==(lit>0) for lit in row):
                    continue
                pending=[lit for lit in row if abs(lit) not in value]
                if not pending:
                    return False
                if len(pending)==1:
                    lit=pending[0]
                    value[abs(lit)]=(lit>0)
            if len(value)==before:
                # Every surviving clause already has a satisfied literal.
                assert all(any(value.get(abs(lit))==(lit>0) for lit in row) for row in retained)
                return True

    total=0
    for x in range(1<<v):
        for s in range(v):
            correct=sum(((x>>(j^s))&1)<<j for j in range(v))
            for y in [correct, correct ^ (1 << (x % v))]:
                fixed={}
                for i,word in enumerate(inp):
                    digit=(x>>i)&1
                    fixed[int(letter(word[digit]))]=True
                for i,word in enumerate(signs):
                    fixed[int(letter(word[4 if s>>i & 1 else 1]))]=True
                for i,bit in enumerate(claimed):
                    fixed[int(letter(bit))]=bool(y>>i & 1)
                assert force(fixed)==(correct==y)
                total+=1
    return total,len(raw)


def audits_layout():
    rng=Random(5243)
    trials=0
    for _ in range(100):
        A,W= rng.randrange(3,10),rng.randrange(2,17)
        sigma=rng.randrange(W,A*W)
        h=W.bit_length()+rng.randrange(2,6)
        radix=1<<h
        multiplicity,remainder=divmod(radix,W)
        slots=multiplicity*sigma+remainder*A
        assert slots*W-sigma*radix==remainder*(A*W-sigma)
        k=rng.randrange(24,180)
        current,batches=k,1
        depth=0
        while current>1 and current-current//A>=h:
            child=current//A
            child_batches=1<<(current-child-h)
            batches*=child_batches
            depth+=1
            assert batches==1<<(k-child-depth*h)
            current=child
        widths=sorted([1<<rng.randrange(2,11) for _ in range(28)],reverse=True)
        tip=widths[0]
        for size in widths:
            assert tip%size==0
            tip+=size
        trials+=1
    return trials


if __name__=='__main__':
    print('finite-field shift cases:',audit_fields())
    print('dyadic padding and tree counts:',audits_layout())
    for k in (1,2):
        print('serialized checks and bytes, k =',k,check_files(k))
