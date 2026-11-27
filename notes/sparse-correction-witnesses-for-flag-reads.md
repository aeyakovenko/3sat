# Sparse correction sets for verifying a RAM flag read

A write-once dictionary starts at zero, writes a one at each address in a list $X$, and reads the addresses in a second list $Y$. Each list contains $N=2^w$ distinct addresses of $3w+1$ bits. The OR of the replies is one exactly when the lists intersect. The November 24 preprint's list-distinctness volume theorem, through the journal's signed two-list reduction, gives a lower bound of $\Omega(Nw^{1+\sigma_p})$ for a trivalent bit tensor network over any fixed prime field $\mathbb F_p$ deciding whether every reply is zero. Here $\sigma_p>0$ is the exponent supplied by the preprint. The following consequence uses that theorem as an external input. [Preprint's volume theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build/obstruction.tex) · [Transfer to two individually distinct lists](matrix-list-unit-sat.md#one-sat-answer-tensor-with-two-ordered-lists-of-literal-positions)

## One evaluation per candidate correction set

Fix $0\le b\le M$. A certificate is a subset $S$ of a public set of $M$ possible corrections, with $|S|\le b$. A Boolean circuit $V(x,S)$ checks it. On each input $x$, suppose acceptance is upward closed within this capacity. Write $\mathcal C_x$ for its inclusion-minimal accepted sets. Every superset of an accepted set within capacity is admissible, and each set has one encoding. Additional free proof bits would change the multiplicities.

For $0\le j\le b$, let

$$
\lambda_j=\sum_{r=0}^{b-j}(-1)^r {M-j\choose r}.
$$

For any fixed core $C$ of size at most $b$, the total weight of its supersets of size at most $b$ is one. Indeed, each $\lambda_{|S|}$ is the sum of $(-1)^{|U|-|S|}$ over $S\subseteq U,\ |U|\le b$. Summing first over $C\subseteq S\subseteq U$ gives $(1-1)^{|U|-|C|}$, leaving only $U=C$. This is Möbius inversion on a truncated Boolean lattice. [Rota, *On the Foundations of Combinatorial Theory I*](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rota1.pdf)

The scalar

$$
Z(x)=\sum_{|S|\le b}\lambda_{|S|}\,V(x,S)
 =\sum_{\substack{\varnothing\ne J\subseteq\mathcal C_x\\
                    |\bigcup_{C\in J} C|\le b}}(-1)^{|J|+1}
$$

is the ordinary Euler characteristic of the complex whose faces are the jointly admissible subfamilies of minimal corrections. The equality follows by inclusion–exclusion on the cones of supersets of the minimal sets. Their intersection is the cone on their union when that union fits, and empty otherwise. A rejected input has $Z=0$. On an accepted input for which all minimal corrections fit together, $Z=1$, however many different witnesses pass the verifier.

The left-hand side has a trivalent realization with **one** copy of $V$ and volume

$$
O\bigl(Nw+\operatorname{size}(V)+b\log(2M+2)\bigr).
$$

Circuit size charges gates and wires. Guess an active prefix of $b$ slots, enforce strictly increasing identifiers in $[M]$ and zero inactive slots. Its active length has a unique boundary among $b+1$ possibilities. At boundary $j$ multiply by the field constant $\lambda_j\bmod p$, using a unary weight for each boundary flag. Pin the verifier output to one. All gates and copying use bounded arity, and each set has one internal evaluation. The constants depend only on $M,b,p$.

## What a small verifier must permit

Suppose $\exists S\,V(x,S)$ decides either the all-zero answer or its complement on every promised pair of lists. If the displayed volume is $o(Nw^{1+\sigma_p})$, **at every sufficiently large $w$ some accepted input has $Z(x)=0\bmod p$**. Otherwise $Z^{p-1}$ gives the exact acceptance bit everywhere, at the cost of $p-1$ copies over this fixed field. Complementation also costs linear volume, by summing a constant and the negative of the scalar with a selector bit, pinning inactive internal wires to zero. Either polarity would then compute the excluded all-zero test.

On that input the union of the minimal accepted corrections occupies more than $b$ distinct positions. More precisely their complex of jointly admissible subfamilies has Euler characteristic divisible by $p$. This measures how the certificates differ even when raw witness counts are large because the circuit accepts arbitrary padding. For example, three different singleton cores at capacity two have three admissible pairs and no admissible triple. Their Euler characteristic is zero over the integers. The correction supports can already defeat the scalar test with three positions. A RAM can execute the dictionary directly in $O(N)$ word operations.

## Checking the role of collisions

Let $c$ be the number of matching pairs of indices across the two lists. A circuit of size $O(Nw)$ certifies a hit by guessing one pair and comparing the two selected addresses. With $b$ candidate pairs in a sorted certificate and acceptance when any selected pair matches, the minimal sets are exactly the $c$ singleton hits when $b\ge1$. Thus $Z=\sum_{r=1}^b(-1)^{r+1}\binom cr$. For $1\le c\le b$ this is one. For $c=p^h>b$ it vanishes modulo $p$, since $(1+z)^{p^h}=1+z^{p^h}$ in the field. Such instances exist whenever $p^h\le N$. Guessing up to $b$ distinct matching pairs in sorted order and requiring *every* selected pair to match gives the same alternating sum by weighting the positive lengths and excluding the empty list. This supplies an exact $O((b+1)Nw)$-volume test on the promise $c\le b$.

The number $c$ counts conflicts between the addresses in the two physical input lists. A program that redirects every read after the first hit to a permanent zero cell sees at most one hit in its actual dictionary reads, even if all $N$ input addresses match. On the diagonal example $X=Y$, the fixed two-list test still has $N$ candidate hits. The sparsity promise on the input lists cannot be deduced from the masked reply string. [Actual masked RAM execution](one-hot-memory-history-of-unit-sat.md) · [Related modular witness-count bounds](matrix-witness-divisibility.md)

## Finite check

This checks the integer identity for 15,914 choices of universe, capacity and up to three generating sets, including redundant generators.

~~~python
from functools import reduce
from itertools import combinations
from math import comb
from operator import or_

checked = 0
for M in range(6):
    for b in range(M + 1):
        sets = [s for s in range(1 << M) if s.bit_count() <= b]
        weight = [sum((-1)**r * comb(M-j, r) for r in range(b-j+1))
                  for j in range(b+1)]
        for h in range(min(3, len(sets)) + 1):
            for cores in combinations(sets, h):
                mass = sum(weight[s.bit_count()] for s in sets
                           if any((c & s) == c for c in cores))
                chi = sum((-1)**(r+1) for r in range(1, h+1)
                          for part in combinations(cores, r)
                          if reduce(or_, part, 0).bit_count() <= b)
                assert mass == chi
                if cores and reduce(or_, cores, 0).bit_count() <= b:
                    assert mass == 1
                checked += 1
assert checked == 15_914
~~~
