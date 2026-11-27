# Certifying a read without reconstructing every store

**One matching store can certify a claimed read even when it is not the last writer.** This gives a single ordinary SAT query for defects in a proposed accepting RAM history. The query can use a partial description of the stores that justify its reads. It remains sound when the proposed history and the description are both malicious.

A fixed native program gives an exact test of the saving. Its elapsed clock is \(t=1024\cdot2^\ell+15\). Describing all its store addresses by the quadratic construction below incurs a minimum charge of exactly \((t-15)/2048\). Certifying its one final read needs at most one affine piece. A separate compiler physically emits a proper DIMACS file for the verdict in \(2^{\ell/4}\operatorname{poly}(\ell)\) RAM steps, including checks on the lookup tables used by the guest.

The unrestricted \(O(N)\), \(O(N^2)\), and \(O(N^3)\) deterministic SAT questions remain open. Here \(N\) counts encoded **bits**.

## A one-sided test for memory consistency

Use the journal’s separate load/store RAM with read-only input and initially zero work memory. Guess a circuit for the controller, nondeterministic choices, and claimed load replies at each native instruction time. Idle after halt through the public clock. The usual local tests check the initial controller, consecutive CPU transitions, immutable input reads, and the final accepting halt.

Consider a proposed work read at time \(c\), address \(a\), with claimed value \(b\). Call an earlier store to \(a\) of a value different from \(b\) a **conflict**. Include a conflict at time \(-1\) if \(b\ne0\). Supply a relation \(R(c,u)\) offering earlier stores that justify this read. Require two things.

1. Every offer with \(u<c\) for this read is a real store in the proposed stream, to \(a\), with value \(b\).
2. For every conflict \(j\), there is an offer at some \(j<u<c\).

These conditions imply the claimed reply. If the actual last store in the proposed stream wrote the wrong value, that store is a conflict with no possible later repair. If there was no store and the initializer disagrees, the same argument applies at \(-1\). Induction over instructions now authenticates the entire execution. Conversely, on a genuine read with a conflict, it suffices to offer **any** matching store after the last conflict. A read with no conflict needs no offer. Later stores of the same value may be omitted.

This removes a coverage obligation from the compiler. A missing offer can discard an honest certificate. A fabricated offer has a locally checkable witness against it. Earlier journal tests used a supplied last-writer time or a separate search for intervening writes. [Earlier register-history verifier](chronological-solver-registers.md) · [Earlier succinct memory-defect test](succinct-memory-defects.md)

## Compiling the interval test into one SAT file

Put \(L=\lceil\log_2(t+2)\rceil\). Represent offers as a union of pieces. Piece \(i\) has an enable bit depending on the consumer \(c\), an affine domain for the \(L\)-bit store time \(u\), and equations
\[
Q_i(u)=y_i(c).
\]
There are \(O(L)\) output coordinates per piece. Their polynomials have degree at most two over \(\mathbb F_2\). Let \(r_i\) be the rank of the matrix whose rows are those coordinates’ coefficients on the mixed monomials \(u_j u_k\), \(j<k\). Let \(g\) count the gates of the shared controller, enable, and right-hand-side circuits.

A defect formula guesses either an invalid local transition, a falsely offered store, or a read and conflict \(j\) for which the open interval \((j,c)\) contains no offer. The last alternative has a deterministic circuit of size
\[
O\!\left(\left(1+g+\sum_i2^{r_i}\right)\operatorname{poly}(L)\right).
\]
The same bound, with a fixed additional polynomial factor in \(L\), covers **physical DIMACS bits and native construction steps** for polynomial-size descriptions and locally available source inputs.

Here is the construction for the absence test. Split each strict endpoint comparison by its most significant differing bit. This gives at most \((L+1)^2\) intersections of affine prefix conditions, including the initializer case. In each intersection, row-reduce the quadratic coefficients. Keep at most \(r_i\) quadratic equations and solve the remaining affine equations by elimination. An inconsistent affine system is empty. Otherwise substitute its solution into the surviving equations \(p_1,\ldots,p_r\). The exact number of solutions is
\[
2^{-r}\sum_{\lambda\in\mathbb F_2^r}
       \sum_x(-1)^{\lambda\cdot p(x)}.
\]

Each inner sum costs \(\operatorname{poly}(L)\). For a mixed pair, write the phase as \(xy+xA+yB+C\). Summing over \(x,y\) leaves \(2(-1)^{AB+C}\). After eliminating all mixed pairs, a nonconstant affine phase sums to zero. The endpoint and address bits can remain symbolic throughout. The pivots involve only the constant quadratic coefficients on the free time variables. The remaining sign and vanishing tests become Boolean gates on the parameters. Summing modulo \(2^{L+r+1}\) detects a nonzero numerator exactly. This uses the classical quadratic signed-sum algorithm. The change here is its application to the open native time interval, with the exponential charge on the independent quadratic equations. [Montanaro](https://arxiv.org/abs/1607.08473) · [Earlier journal calculation for quadratic output distributions](quadratic-sampler-fibers.md)

This gives a precise target for the unrestricted question. Take the journal’s fixed unary nondeterministic source \(H(1^n)\), with clock \(t=Cn^2\), outside nondeterministic native time \(o(t)\). Its input words are computable from the unary endpoints. Fix \(k\in\{1,2,3\}\). If SAT takes deterministic time \(O(N^k)\), then for every fixed \(\gamma<1/k\) with \(\gamma\ge0\), infinitely many **positive** inputs of \(H\) have no passing description with
\[
1+g+\sum_i2^{r_i}\le t^\gamma.
\]
Otherwise guess a capped description, physically construct its defect formula, run the hypothesized solver, and accept on UNSAT. The time is \(O(n+t^{k\gamma}\operatorname{polylog}t)=o(t)\), including guessing, construction, and fixed-width-ratio simulation. On a negative input every alleged accepting history fails. This argument requires a short description only on positive inputs. A construction of such descriptions remains open for \(H\). [Fixed unary source and native hierarchy proof](a-fixed-unary-ram-source-for-physical-sat-compilers.md)

## An exact obstruction on an executed sweep

For odd \(\ell\ge3\), work in \(K=\mathbb F_{2^\ell}\) in a polynomial basis. One fixed RAM program loops through all \(\ell\)-bit words \(z\) in numerical order and executes
\[
\mathrm{mem}[z^3]\gets z.
\]
It then loads \(\mathrm{mem}[q]\) and accepts iff its low bit is one.

The instruction listing uses eight chunks of \(d=\lceil\ell/8\rceil\) bits per operand. Its read-only payload contains 64 tables of \(2^{2d}\) field products for the ordered pairs of chunk positions. Two unrolled field multiplications compute the cube. Every shift, address addition, indirect load, XOR, store, loop test, and padding instruction is charged. There are 12 setup instructions. The store for \(z\) occurs at zero-based instruction time
\[
980+1024z,
\]
and the complete clock, on either verdict, is \(t=1024\cdot2^\ell+15\).

The guest width is based on its **actual payload**. For all sufficiently large odd \(\ell\), take \(u=2^{\lceil3\ell/10\rceil}\) payload bits and \(w=12\lceil\log_2(u+2)\rceil\). The four header words and \(64\cdot2^{2d}\) table words fit because their combined length is \(2^{\ell/4+O(1)}O(\ell)=o(u)\). The guest can address every work cell it uses. With the fixed program and unary clock, the encoded native source length is \(s=t+u+O(\log u)=(1+o(1))t\).

Now try to certify **all store addresses** by covering their times with affine domains, each carrying a quadratic address map. Charge a piece \(2^{r_i}\), as in the interval evaluator. Even with freely chosen, overlapping domains,
\[
\boxed{\displaystyle \min\sum_i2^{r_i}=2^{\ell-1}=\frac{t-15}{2048}.}
\]

The store times form an affine copy of the \(z\)-cube because \(980<1024\). Intersect a piece with that copy. Suppose the intersection has dimension \(e>0\) and direction space \(V\). For fixed nonzero \(h\in V\), the second differences of the required address include
\[
D_hD_v(z^3)=h^2v+hv^2,\qquad v\in V.
\]
The kernel of this linear map on \(V\) is exactly \(\{0,h\}\). Its image has dimension \(e-1\). Every second difference lies in the column span of the piece’s mixed quadratic coefficients, so \(r_i\ge e-1\). Thus the piece covers at most \(2\cdot2^{r_i}\) store times. This also holds for a singleton. Summing over the cover proves the lower bound. Partitioning the cube into parallel two-point lines attains it, since every address function on a line extends affinely. The differential property of cubing is classical. An earlier journal entry used it for forced assignments under affine orderings. [Nyberg](https://users.ics.aalto.fi/knyberg/publications/diffuni.pdf) · [Earlier forced-assignment construction](piecewise-quadratic-clauses-with-resistant-model-addresses.md)

The minimum prices the character enumeration in this compiler. The entire address map itself has a polynomial-length description. Moreover, cubing is a permutation for odd \(\ell\). The sole writer to \(q\) has ordinal
\[
z=q^{(2^{\ell+1}-1)/3}.
\]
For the final read, **one rank-zero piece** offering time \(980+1024z\) suffices. This gives a concrete failure of the proposed lower-bound step from an expensive all-store check to an expensive verdict.

## A short physical compiler and a failed shortcut

Guess \(\ell\) bits \(z\) in ordinary SAT, enforce \(z^3=q\) by polynomial multiplication and reduction modulo the supplied irreducible polynomial, and require the low bit of \(z\) to be one. This takes \(O(\ell^2)\) gates. Trusting arbitrary supplied lookup tables would make the reduction unsound. In the three-bit fixture, flipping the low bit of payload word 4 makes the actual guest reject \(q=1\), while this formula still accepts.

The corrected compiler checks the scalar layout and modulus, then appends one fixed-width guard clause per table word. A correct word prints a clause true on the three false anchors. An incorrect word prints their positive disjunction. Each guard is locally indexable from one actual payload word and a field calculation. On a well-formed, sufficiently clocked sweep this compiler is exact for the advertised tables. An incorrect table disables the certificate, including on an accidentally accepting run.

The bit-length constant is explicit. With \(G\) gates including the final copy, put \(V=3+\ell+G\), \(C=8G+8+64\cdot2^{2d}\), and \(D=\mathrm{digits}_{10}(V)\). Use seven anchor clauses, eight truth-table rows per gate, and one final pin. Each three-literal row takes \(3D+8\) ASCII bytes. Including the header and all newlines, the guarded query has exactly
\[
N=8\left(8+D+\mathrm{digits}_{10}(C)+C(3D+8)\right)
\]
bits. Physical generation takes \(2^{\ell/4}\operatorname{poly}(\ell)\) steps. Even an \(O(N^3)\) solver would consume \(o(t)\) steps on this query. Checking a physically supplied unary suffix separately costs \(O(t/\log t)\) more. On the advertised tables, direct field inversion also decides the read in polynomial time in \(\ell\). These savings concern the constructed native family.

## Checks

- The interval circuits agreed with direct enumeration on **1,490,816** address and endpoint tests across 356 maps, including every two-input, two-output Boolean map.
- Across **16,384** small history and repair-description tests, every certified reply was genuine. In 46 passing cases there was a conflict and the offer omitted the last writer. Removing authentication of offered stores admitted **4,656 false replies**. Z3 checked 48 serialized defect files.
- The affine-rank inequality passed on all **51** affine flats in dimension three and all **2,451** in dimension five. The native interpreter replayed every query in dimensions three and five and three queries in dimension nine. All 43 corresponding DIMACS verdicts agreed. The nine-bit fixture executed **524,303 instructions**. The good and corrupted three-bit guarded files each occupied **48,488 bits**.
- I replayed the existing 16-selector-bit upper program on all 65,536 files. Assignment enumeration gave 6,560 positives, and 20,720 executions took nine instructions. That census uses four-bit words and a 16-bit selector encoding. Its clock supplies no lower bound in the ASCII bit length above. [Finite native clock](exact-nine-step-clock-for-four-sat-words.md)

Reproduce with `python3 -B quadratic_read_repair_audit.py`. The finite circuits, instruction listing, and serialized files are executable checks. The general compiler bound and hierarchy application are manuscript arguments. Historical priority for the repair criterion and exact cover charge is unverified. [Round 7 audit](quadratic_read_repair_audit.py)
