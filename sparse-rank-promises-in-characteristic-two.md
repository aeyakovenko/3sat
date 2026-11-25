# Sparse rank promises for signed vector queries in characteristic two

Let a query to a binary $d\times d$ matrix $E$ return $Ex$ or $E^{\mathsf T}x$ for a chosen binary vector $x$. A depth-$q$ representation is a linear combination of transcript indicators using at most $q$ queries each. On the promise $\operatorname{rank} E\in\{0\}\cup S$, the target is $[E=0]$. The coefficient field has characteristic two. There are no constraints on the number of terms or on values at unpromised ranks. Fixing a path in an adaptive tree fixes its queries and answers, so the transcript definition includes adaptive tests. All linear systems below have entries in $\mathbb F_2$, and extending that field preserves their consistency.

At $d=4$, the promise $S=\{1,4\}$ takes **three** queries, although the two singleton promises take two and one respectively. There is also a three-way obstruction. The promise $S=\{1,3,4\}$ takes four queries, and each two-element subset takes at most three. For example, the upper bound for $\{1,4\}$ can be seen directly. Multiply the two-query test for zero on ranks zero and one by $\sum_{x\ne0}[Ex=0]$. The latter factor takes one query per term and is one on singular matrices and zero on invertible ones. [Two-query rank-one test](residual-lines-and-the-ranks-needed-for-matrix-verification.md)

## Exact census

Each entry lists the positive rank sets with the indicated optimum. Digits within parentheses list the elements of a single set. The empty set always costs zero.

| Dimension | One query | Two queries | Three queries | Four queries |
|---|---|---|---|---|
| 1 | (1) | | | |
| 2 | (2) | (1), (1,2) | | |
| 3 | (3) | (1), (2), (1,3), (2,3) | (1,2), (1,2,3) | |
| 4 | (4) | (1), (3), (3,4) | (2), (1,3), (1,4), (2,3), (2,4), (2,3,4) | (1,2), (1,2,3), (1,2,4), (1,3,4), (1,2,3,4) |

Every lower bound in this table holds at larger dimensions for the same fixed $S$. Place the smaller matrix in the upper left corner and pad with zeros. A larger vector query then becomes a single smaller query with known zero padding.

## Exact reduction by an odd-order group

Identify $\mathbb F_2^d$ with $\mathbb F_{2^d}$, and write $M_a$ for multiplication by $a\ne0$ in a fixed binary basis. The action $E\mapsto M_a E M_b$ has group order $(2^d-1)^2$. It preserves rank and sends transcript indicators to transcript indicators of the same depth. Summing over the group is a projection onto invariant functions because its order is odd. If a representation exists on the promise, averaging it still represents the target there. Conversely every averaged generator is itself a sum of allowed transcripts.

Fix a cylinder $C$, specified by its left and right query spaces and answers on bases. Dependent queries are redundant or inconsistent. On any orbit $O$, the averaged indicator of $C$ is $|C\cap O|\bmod2$, since the stabilizer is odd. Thus one binary coordinate per matrix orbit suffices. It is enough to test one left query space per orbit of the multipliers $M_a^{\mathsf T}$ and one right space per orbit of $M_b$. Invertible output maps only relabel the answers. For each pair of spaces, enumerate **every** answer tuple, toggle the coordinate of each matrix in its tuple's fiber, project to the promised orbit coordinates, and test whether the span contains the unit vector of the zero orbit. Enumerating increasing total dimension returns the optimum. In dimension four the numbers of orbits at ranks zero through four are respectively $1,1,34,168,96$.

As a general consequence, the only nonempty positive rank set decidable in one query is $S=\{d\}$. A single right-query term for $x\ne0$ has the form $h(Ex)$. The left multipliers sweep a nonzero response through every nonzero vector and preserve zero. The right multipliers sweep $x$ through all nonzero inputs. For $E$ of rank $r<d$, the number of nonzero inputs in the kernel is $2^{d-r}-1$, odd, and the number outside it is even. The average therefore equals $h(0)$ on every singular matrix. The left-query calculation follows by transposition. The singularity factor above gives the converse.

## Independent checks

The script repeats the full census through $d=3$ using one coordinate per matrix and all query tuples up to permutation and repetition, without group averaging. It also extracts a dual certificate for $d=4, S=\{1,4\}$ at depth two. This gives a set of 3,526 promised matrices containing zero. The script checks directly that every answer fiber for every pair of distinct probes among the 30 individual left or right probes intersects this support evenly. Summing fibers covers shallower and repeated probes. Pairing with the zero indicator gives one. These checks concern signed queries to the residual matrix. The running time of an unrestricted SAT machine is open. [Reproduce the census and the certificate with Python](sparse_rank_vector_query_audit.py)

Lean 4.19 independently constructs the support from 18 orbit representatives in the polynomial basis modulo $X^4+X+1$. Two finite facts use `native_decide`, which trusts Lean’s native evaluation. They check the support size, uniqueness, kernel sizes and parity histograms for all 1,024 ordered pairs of probes, including zero probes and repetitions. The theorem `noTwoQueryRepresentation` then proves by induction that every finite XOR of two-probe cylinders disagrees with the target somewhere on the promise. Field extension follows from the linear-system observation above. The Lean file verifies this specific lower bound. The other entries of the table come from the Python census. [Lean certificate and separation theorem](SparseRankPairCertificate.lean)
