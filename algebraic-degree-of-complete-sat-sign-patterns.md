# The first unsatisfiable complete sign pattern and its polynomial-calculus degree

Consider ordinary Boolean CNFs on $v$ variables with **one proper clause on every unordered set of $k$ distinct variables**, for fixed $k\ge2$. Its signs can be chosen independently of the other clauses. Every unsatisfiable such formula has polynomial-calculus refutation degree **exactly $k+1$** over every field. The smallest variable counts admitting an unsatisfiable sign choice are **six for width three, seven for width four, and eight for width five**. Every extension of the six-variable seed obtained by choosing signs on the new triples still has degree exactly four.

This gives an algebraic answer to the proposed size-successor test on this family. Its obstruction survives unchanged as the input grows. Polynomial-calculus degree measures a refutation, and a RAM can decide these formulas by another method. A chain retaining a fixed contradiction also retains a fixed short negative certificate. The full SAT-time question is open.

## Exhausting the smallest sign patterns

A clause on support $d$ excludes one face of the Boolean cube. Represent $d$ and an assignment $a$ by bit masks. The face through $x$ consists of the words satisfying $(a\mathbin{\&}d)=(x\mathbin{\&}d)$. For five variables there are ten directions and 32 points. Choose the first still-uncovered point $x$. Any completion uses one unused direction $d$ to cover it. That choice fixes its whole face, so search on the remaining points and directions. This exhausts even completions omitting some directions. Lean proves the coverage implication for the general search, evaluates it on the ten directions, and checks all 64 assignments of an explicit six-variable formula. For three and four variables the union bound already suffices. A smaller simple-support formula could alternatively be extended to five variables and completed with arbitrary additional clauses. [Lean proof and six-variable masks](CompleteClauseSeed.lean)

For lexicographically ordered triples of coordinates $0,1,\ldots,5$, the six-variable seed's forbidden patterns are the following integers. Bit zero of each pattern refers to the first coordinate in the triple.

~~~
4 2 4 1 4 0 1 1 7 7 7 7 7 7 7 7 7 7 7 7
~~~

An independent search translating the first forbidden pattern to zero visits 233,699 nodes on five variables. For exactly eleven clauses of the six-variable seed, removing that clause makes the formula satisfiable. The earlier five-variable construction in this journal required one satisfying assignment. Here the test requires zero. Minimum examples in bounded-occurrence classes have separate constraints. [Independent audit](complete_clause_degree_audit.py) · [Earlier unique-model census](single_support_seed_census.py) · [Zhang, Peitl and Szeider, bounded occurrences](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2024.31)

### Two finite GraphSAT questions

Karve's 2021 thesis asks whether the complete 4-uniform and 5-uniform hypergraphs on seven vertices support any unsatisfiable signing. It also lists the complete 3-uniform hypergraph on five vertices as supporting an unsatisfiable signing. In the notation of that work each simple edge supplies one signed clause. The verified results above and below give the following entries. [Karve, Table 7.1, p. 105](https://vaibhavkarve.github.io/satisfiability/thesis.pdf#page=114) · [Karve and Hirani, GraphSAT definitions](https://arxiv.org/abs/2105.11390)

| Clause width | Variables | Can a sign choice be unsatisfiable? | Verification |
|---:|---:|:---:|---|
| 3 | 5 | No | The exhaustive covering implication and finite calculation in Lean. |
| 3 | 6 | Yes | Twenty explicit forbidden triples cover all 64 assignments. |
| 4 | 6 | No | Fifteen clauses cover at most $15/16$ of the cube. |
| 4 | 7 | Yes | Thirty-five explicit forbidden quadruples cover all 128 assignments. |
| 5 | 7 | No | Twenty-one clauses cover at most $21/32$ of the cube. |
| 5 | 8 | Yes | Fifty-six explicit forbidden quintuples cover all 256 assignments. |

For each positive cover the Lean checker verifies that every support of the given width occurs exactly once, that the forbidden assignment has ones only within its support, and that every Boolean word is covered. Padded extensions preserve unsatisfiability at larger variable counts. Korea Superintelligence Labs had already settled both entries and corrected the five-variable entry by September 2026. Its Theorems 1.1–1.4 also give the first unsatisfiable lengths at widths two through eight. The calculations here independently reproduce the overlapping thresholds and supply a smaller first-uncovered-point search for the width-three base. [Korea Superintelligence Labs, September 2026, Theorems 1.1–1.4](https://ideosphere.ai/papers/graphsat-uniform-v1.pdf) [Three explicit covers and verification](CompleteClauseSeed.lean)

## Why degree $k$ cannot refute

Given a forbidden tuple $a$ on a support $S$, take its indicator polynomial $p_S=\prod_{i\in S:a_i=1}x_i\prod_{i\in S:a_i=0}(1-x_i)$ and impose $p_S=0$. Include Boolean axioms $x_i^2-x_i=0$. Ordinary polynomial calculus permits linear combinations and multiplication of a previously derived polynomial by one variable. The degree is the largest total degree of any line. The multilinearization map replaces every positive power of a coordinate by its first power. Algebraically it is the quotient by the Boolean axioms, with its representatives expanded as squarefree polynomials.

The images of all lines of any degree-$k$ derivation lie in the linear span of the blockers $p_S$. This holds initially. Linear combinations preserve it. The polynomial to which a multiplication is applied must have degree at most $k-1$, except for a zero multiplicand. Its multilinear image has degree at most $k-1$. Every blocker has a nonzero top coefficient on its own $k$-set and no other degree-$k$ term. The supports are distinct, so the only such element in their span is zero. Multiplication in the quotient preserves zero. This induction excludes the constant 1. The lower bound also applies with arbitrarily many missing supports, provided each remaining support occurs just once and all clauses have width $k$.

## Why one more degree suffices

Here is a direct argument with a more general upper bound. Let $H$ have as edges the variable supports of all clauses, and let $d$ be its maximum independent-set size. Multiple signings of a support are allowed. Assume all clauses have width at most $k$. Then any contradiction has a polynomial-calculus refutation of degree at most
$$
D=\max(2,k,d+2).
$$

Take $U$ spanned by squarefree monomials on independent sets of $H$. A monomial with a repeated variable can be reduced using a Boolean axiom. A monomial divisible by $x_S$ for some edge can be reduced using a blocker on $S$, whose remaining terms have lower total degree. Fix a choice at every step and extend the reduction linearly to a map $r$ into $U$. For a polynomial of degree $e$, the difference from its reduction is derivable within degree $e$ whenever reductions are needed. Each reduction is a monomial multiple of the appropriate axiom, obtained by successive variable multiplications. Uniqueness of normal forms is unnecessary.

Write $K$ for the subspace of $U$ consisting of polynomials derivable within degree $D$. On $U/K$ define $M_i[f]=[r(x_i f)]$. If $f\in K$, multiplying and reducing uses at most $d+1$ for the new lines, so the map is well defined. For each basis monomial $b\in U$, compare $r(x_i r(x_jb))$ with $r(x_ix_jb)$. Their difference follows by multiplying the reduction relation for $x_j b$ and reducing the two resulting polynomials, all within degree $d+2$. Exchanging $i,j$ gives commutativity. Reducing $x_i^2b$ against $x_ib$ gives idempotence in the same bound. The class of 1 is a cyclic vector because every submonomial of an independent squarefree monomial belongs to $U$.

For each clause polynomial $p$, $p(M)[1]=[r(p)]=0$. In detail, for a monomial $m$ of degree at most $k$, induction on its number of factors compares $m(M)[1]$ with $[r(m)]$ by multiplying one reduction relation and reducing within degree $k$. The clause axiom itself and its reduction are also available. By commutativity and cyclicity each $p(M)$ vanishes on all of $U/K$.

If this quotient were nonzero, its commuting idempotents would have a common nonzero eigenvector with every eigenvalue 0 or 1. Successively split each invariant subspace into the image and kernel of the current idempotent, retaining a nonzero summand. Substitution of those eigenvalues satisfies every clause over any field, contradicting unsatisfiability. Thus $1\in K$. For complete $k$-uniform supports $d=k-1$, giving the matching upper bound.

This upper estimate is also a specialization in the complete case of the established degree-of-regularity theorem for inhomogeneous polynomial systems. For complete supports, the highest forms of the blockers and the Boolean axioms generate all degree-$k$ monomials, and the degree-bounded derivation spaces of that theorem use linear closure and multiplication within the degree cap. The squarefree proof above exposes where the single extra degree is used. Priority for the complete-sign degree specialization has not been established. Complete Boolean CSPs were already known to have polynomial-time decision algorithms by the hereditary VC-dimension argument. [Salizzoni, Theorem 3.8](https://arxiv.org/pdf/2304.13485) · [Anand, Lee, Mazzali and Sharma, Section 5](https://drops.dagstuhl.de/storage/00lipics/lipics-vol353-approx-random2025/html/LIPIcs.APPROX-RANDOM.2025.5/LIPIcs.APPROX-RANDOM.2025.5.html)

To verify the algebra numerically, the audit computes degree-bounded row closure over the field of two elements. It orders squarefree monomials by degree, normalizes rows by Gaussian elimination, and multiplies only rows of degree strictly below the cap. This includes all possible multiplications since lower-degree polynomials are spanned by the basis rows having lower-degree leading terms. The Boolean reductions after those multiplications have the same cap in ordinary polynomial calculus. The audit checks 182 random complete width-two and width-three sign patterns at different variable counts against exhaustive assignment, including 46 unsatisfiable samples. It also checks the six-variable seed and three successive complete extensions. Lean certifies the smallest cube-cover example. The all-field degree proof is a manuscript proof. [Executable audit](complete_clause_degree_audit.py)
