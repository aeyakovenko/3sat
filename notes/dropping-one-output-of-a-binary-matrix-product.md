# Dropping one output of a binary matrix product

**Theorem.** For every linear map $P:\mathbb F_2^{2\times2}\to\mathbb F_2^3$ of rank three, computing $P(AB)$ from the eight bits of $A,B$ takes exactly six binary AND gates. Constants, arbitrary affine combinations and fanout are free, and each gate may use earlier gate outputs. This includes computing any three of the four entries. Computing all four entries takes seven ANDs in the same model. [Full-product theorem and exact search lemma](seven-ands-for-a-two-by-two-binary-matrix-product.md)

### Two output cases

Write each matrix in row-major order with its top left bit least significant. Let $e$ be the unique nonzero vector in $\ker P$. Knowing $P(AB)$ is equivalent, by a free output change of basis, to knowing all output functionals vanishing on $e$. The transformations $(A,B)\mapsto(LAM,M^{-1}BR)$ for invertible $L,M,R$ induce $C\mapsto LCR$ on $C=AB$. Thus rank is the only invariant of the discarded matrix $e$. There are nine nonzero matrices of rank one and six of rank two. Representatives are the bottom-right elementary matrix (mask 8) and the identity (mask 9).

In Strassen's seven-product identity, the term $(c+a)(e'+f)$ contributes only to the bottom-right entry, and $(a+d)(e'+h)$ contributes to both diagonal entries. Here $A$ has rows $(a,b),(c,d)$ and $B$ has rows $(e',f),(g,h)$. Removing the first term for mask 8, or the second term for mask 9, gives the required six-gate upper bounds. The checker verifies the quotient output at every one of the 256 inputs. [Strassen](https://doi.org/10.1007/BF02165411) · [Checker](../audits/mm2_three_output_check.py)

### Eliminating every possible first gate

Take a circuit with at most five AND gates, remove gates available from the preceding affine span, and look at its first remaining AND. It must have linearly independent homogeneous factors $u,v$. More precisely its operands may be affine, but their product differs from $h=u v$ by a free affine function. Each of $u=0$, $v=0$, and $u+v=0$ makes $h$ affine. Restricting to any of these three hyperplanes consequently leaves at most four AND gates. A circuit with zero ANDs is also excluded by the positive dimension of the outputs modulo the free inputs.

For each of the 255 possible nonzero normals $w$, restrict the three output truth tables to $w=0$. On every slice the affine inputs modulo constants have dimension seven, and adjoining the three outputs raises this dimension by three. The four-gate question thus has exactly one gate of slack over the dimension bound. Apply the exact one-extra-direction closure test from the full-product proof. In brief, every potential four-gate circuit stays in the target span or in that span with one exterior gate direction. The first exterior gate must multiply two factors already available in the target span. The test generates those factors, sieves them by restrictions, and closes each remaining enlarged span under available products. Everything takes place on ordinary Boolean truth tables. [Proof of the test](seven-ands-for-a-two-by-two-binary-matrix-product.md) · [Implementation](../audits/mm2_and_exhaustion.py)

| Discarded mask | Normals admitting four gates | Possible first-factor planes, given by their three nonzero masks |
| --- | --- | --- |
| 8 | 1, 2, 3, 16, 64, 80 | $\{1,2,3\}$ and $\{16,64,80\}$ |
| 9 | none | none |

For mask 8, take the two smallest normals $u,v$ in each surviving plane. All pairs of distinct normals from that plane have equivalent product modulo affine functions, since $u(u+v)=u+uv$ and $v(u+v)=v+uv$. On the full eight-bit domain provide $uv$ for free. The free dimension is now nine and the output dimension above it is again three. The exact closure test rejects four further gates for both planes. This exhausts the possibilities for five gates, including circuits that use high-degree intermediate functions.

The checker can recompute all 510 slice decisions directly with the command below. Its default mode computes the stabilizer of each $e$ using the input transformations above and $(A,B)\mapsto(B^\mathsf{T},A^\mathsf{T})$. It tests one normal per orbit and checks that the orbits partition the complete list of normals. The stabilizers have 15 and 11 orbits for masks 8 and 9, respectively. Transposition and changes of matrix bases give invertible linear input and quotient-output maps, so each decision is constant on its orbit. Neither mode requires a classification of two-output quadratic circuits.

~~~sh
python3 mm2_three_output_check.py --all
~~~

### At least eight wrong inputs below the optimum

**Corollary.** Every circuit with at most five ANDs disagrees with $P(AB)$ on at least eight of the 256 inputs, for every rank-three $P$. Every circuit with at most six ANDs disagrees with the four-bit product on at least eight inputs. Consequently deleting any seven points of the domain preserves the exact complexities six and seven, respectively.

A scalar Boolean function computed with $s$ ANDs has algebraic degree at most $s+1$. Induct on $s$, dropping a redundant first gate if necessary. On either fiber of one nonconstant first factor the first gate becomes affine, so both restrictions have degree at most $s$ in the remaining coordinates. Interpolating between them in the factor coordinate increases degree by at most one. We also use that a nonzero polynomial function of degree at most $d$ on $k$ bits is nonzero at least $2^{k-d}$ times for $d\le k$. For a nonconstant function, take the difference in a coordinate on which it depends. The difference on $k-1$ bits is nonzero, has degree at most $d-1$, and each point where it is nonzero contributes at least one nonzero point of the original function. Induction gives the bound, including the constant base case.

Suppose a five-AND circuit disagrees with a rank-three quotient on fewer than eight inputs. It must have some error by the exact result. If it has no genuine AND, a nonzero scalar error has degree at most two on eight inputs and therefore has weight at least 64. Otherwise let $a,b$ be its first genuine gate's independent homogeneous factors. In either half of any of the splits $a,b,a+b$, the circuit uses at most four ANDs. If that half contains an error, some scalar error there is nonzero and has degree at most five in seven variables, giving at least four erroneous inputs. Both halves of any split cannot contain errors, since that would give eight. In particular all errors are confined to a single pair of values of $(a,b)$, and each of the three splits has an exact half.

Either affine half is equivalent to its homogeneous half for the exact test. Translating the inputs by $(A_0,B_0)$ changes $P(AB)$ by the affine function $P(A_0 B+A B_0+A_0 B_0)$, recoverable for free. Hence all three normals must appear in the four-AND slice census above. Only mask 8 and its two listed planes survive.

Use the two smallest normals $u,v$ in the surviving plane as its coordinates. Translate the unique possibly erroneous quarter to $u=v=1$. On the other 192 inputs the first gate is affine, since its truth table differs from $uv$ by an affine function, and $uv=0$ there. Four gates would therefore compute the exact quotient on all those 192 inputs. For each of the two planes the checker restricts all truth tables to this three-quarter domain. The free rank is eight, adjoining the outputs raises it to eleven, and the exact one-extra-direction test rejects the four-gate budget. This proves the eight-error conclusion for all rank-three quotients.

For the full product, the last AND in a six-gate circuit contributes to the outputs with a fixed four-bit coefficient vector $e$. Project modulo $e$ to remove this gate. If the gate is unused, choose any rank-three projection. At most five gates then approximate a rank-three quotient, so at least eight inputs already give wrong projected answers. On all those inputs the original four-bit answers are wrong as well. The argument gives a lower bound on the number of errors and leaves its optimum open.
