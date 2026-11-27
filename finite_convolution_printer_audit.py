"""Deterministic primitive-root preparation over GF(2) for small odd orders."""


def quotient_remainder(x, mod):
    degree = mod.bit_length()-1
    quotient = 0
    while x and x.bit_length()-1 >= degree:
        shift = x.bit_length()-1-degree
        quotient ^= 1 << shift
        x ^= mod << shift
    return quotient,x


def gcd(x,y):
    while y:
        x,y=y,quotient_remainder(x,y)[1]
    return x


def multiply(x,y):
    result=0
    while y:
        entry=y & -y
        result ^= x << (entry.bit_length()-1)
        y ^= entry
    return result


def power(x,n,mod):
    result=1
    while n:
        if n&1: result=quotient_remainder(multiply(result,x),mod)[1]
        n//=2
        x=quotient_remainder(multiply(x,x),mod)[1]
    return result


def fixed_vectors(mod):
    n=mod.bit_length()-1
    pivots={}
    kernel=[]
    for j in range(n):
        image=quotient_remainder(1 << (2*j),mod)[1] ^ (1<<j)
        arg=1<<j
        while image:
            lead=image.bit_length()-1
            if lead not in pivots:
                pivots[lead]=image,arg
                break
            change,preimage=pivots[lead]
            image ^= change
            arg ^= preimage
        if not image:
            assert quotient_remainder(multiply(arg,arg),mod)[1]==arg
            kernel.append(arg)
    return kernel


def factors(mod):
    kernel=fixed_vectors(mod)
    if len(kernel)==1:
        return [mod]
    witness=next(x for x in kernel if x not in (0,1))
    left,right=gcd(mod,witness),gcd(mod,witness^1)
    assert 1<left<mod and 1<right<mod and multiply(left,right)==mod
    return factors(left)+factors(right)


def prime_divisors(n):
    primes=[]
    p=2
    while p*p<=n:
        if n%p==0:
            primes.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1:primes.append(n)
    return primes


def main():
    orders=terms=root_powers=0
    for n in range(1,128,2):
        poly=(1<<n)^1
        parts=factors(poly)
        assert len(parts)==len(set(parts))
        product=1
        for f in parts:
            product=multiply(product,f)
            assert len(fixed_vectors(f))==1
        assert product==poly
        primes=prime_divisors(n)
        f=next(g for g in parts if all(power(2,n//p,g)!=1 for p in primes))
        assert power(2,n,f)==1
        # Distinct powers in the target, without relying on factorization of n.
        assert len({power(2,e,f) for e in range(n)})==n
        for d in range(1,n+1):
            if n%d==0:
                element=power(2,n//d,f)
                assert power(element,d,f)==1
                assert all(power(element,d//p,f)!=1 for p in prime_divisors(d))
                root_powers+=1
        terms+=len(parts)
        orders+=1
    print(f'{orders} odd orders, {terms} irreducible factors, {root_powers} divisor roots')


if __name__=='__main__':
    main()
