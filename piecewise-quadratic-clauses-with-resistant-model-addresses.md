# Simple clause addresses can force complicated assignment addresses

For each sufficiently large \(\ell\) there is a satisfiable proper ordinary DIMACS 3-CNF with \(v=2^\ell\) primary variables and \(N=\Theta(v\ell)\) physical input bits. Every satisfying assignment gives the same truth table on the primary names in increasing numerical order. Write this table as \(f_\ell:\mathbb F_2^\ell\to\mathbb F_2\). The bits of the **file** admit polynomial-time local access in \(\ell\). Its physical address space is covered by \(O(\ell)\) consecutive intervals, on each of which the raw bit is a polynomial of degree \(O(\log\ell)\) in the binary address.

Here is the opposite bound for the **forced table**. Put \(D=\lceil\log_2(d+8)\rceil\). Whenever \(\ell\ge 2d+6D+19\), choose any affine bijection of the \(\ell\) binary name coordinates. In the resulting order, suppose \(r\) consecutive intervals carry arbitrary Boolean polynomials of degree at most \(d\) and their predictions have \(e\) errors altogether. Then
\[
                 e+r-1\ \ge\ 2^{\,\ell-d-4D-12}.
\]
In particular at fixed degree, every ordering of this kind incurs a positive constant fraction of \(v\) in errors and cuts. At degree \(o(\ell)\) the bound is \(v^{1-o(1)}\). For comparison, *any* table can be represented exactly by \(2^{\ell-d}\) aligned intervals for \(0\le d\le\ell\), since each interval leaves just \(d\) free bits. For this measure the lower and upper bounds differ by at most a polynomial in \(d+8\).

The table has an explicit polynomial-time evaluator in \(\ell\). The construction tests a particular shortcut toward a compact SAT compiler. Simple physical clause addresses alone cannot guarantee a matching piecewise low-degree description of satisfying assignments, even after choosing an affine basis for the occurring names. [Compact physical compiler criterion](algebraic-degree-of-a-compact-physical-sat-indexer.md)

## The forced values

Use one prefix tag for each \(b\ge1\). If \(k=\lfloor\log_2 b\rfloor\), the tag is \(1^k0\) followed by the low \(k\) bits of \(b\), of total length \(c=2k+1\). These tags are prefix-free. Activate just the tags for which \(2b+c\le\ell\). Off active tags set \(f_\ell=0\).

Inside an active tag, write a name as \((\mathrm{tag},Y,X)\) with \(b\) bits in \(Y\) and \(a=\ell-c-b\) bits in \(X\). Thus \(a\ge b\). In a fixed binary polynomial basis for \(\mathbb F_{2^a}\) let \(\pi_b\) select its low \(b\) coordinates. Set
\[
                 f_\ell(\mathrm{tag},Y,X)= [\,Y=\pi_b(X^3)\,].
\]
Squaring is linear in this basis, so every coordinate of \(X^3\) has degree at most two. For uniform local access one can construct an irreducible binary polynomial of the desired degree in deterministic polynomial time in \(a\). [Shoup, *New algorithms for finding irreducible polynomials over finite fields*](https://www.shoup.net/papers/detirred.pdf)

Let \(S\) be the \(2^a\) ones on this tag, ignoring all other tags. For every nonzero difference of full names,
\[
             |\{p\in S:p+\delta\in S\}|\le 2^{a-b+1}.
\]
Differences changing the tag contribute nothing. If the \(X\) difference is zero, a nonzero \(Y\) difference contributes nothing. For \(h\ne0\), the derivative \((x+h)^3+x^3=h x^2+h^2x+h^3\) is affine with linear kernel \(\{0,h\}\). At most two inputs give each specified full value. There are \(2^{a-b}\) full values over each specified projected value. This is the classical differential property of cubing in characteristic two. [Nyberg, *Differentially uniform mappings for cryptography*](https://users.ics.aalto.fi/knyberg/publications/diffuni.pdf)

## The parity charges survive every affine ordering

Choose an active \(b\ge3\) and partition the reordered names into aligned blocks of \(2^q\) consecutive names with \(q=b-2\). In original coordinates they are the cosets of a fixed \(q\)-dimensional space \(V\). A point of \(S\) sharing its block with a second point of \(S\) is counted by some nonzero difference in \(V\). Hence at least
\[
  2^a-(2^q-1)2^{a-b+1} \ \ge\ 2^{a-1}
\]
different blocks contain a unique point of \(S\). On each such block, intersect with the chosen tag. This intersection is an affine flat of dimension at least \(q-c\), by the dimension formula. The table restricted to that intersection has odd parity, regardless of any ones on other tags.

A Boolean polynomial of degree \(d<q-c\) has even parity on each such flat. Indeed affine substitution preserves degree, and every monomial on the flat misses some free coordinate, so its sum over that coordinate is zero in \(\mathbb F_2\). If no interval breakpoint lies strictly inside the block, a prediction of degree \(d\) therefore makes an error there. Distinct singleton blocks charge distinct errors or distinct breakpoints. Consequently \(e+r-1\ge 2^{a-1}\).

For the stated bound take \(b=d+2D+8\). The inequalities \(b<2^{D+2}\) and \(c\le2D+3\) give \(q-c>d\), \(2b+c\le 2d+6D+19\), and \(a-1\ge\ell-d-4D-12\). This is one family, chosen independently of the degree, error budget, interval boundaries and affine change of coordinates.

## A physical 3-CNF for this table

Use variables 1, 2, 3 as anchors. Forbid each of their seven nonzero assignments using one clause on the three distinct anchors. Use the primary decimal variable name consisting of the character 1 followed by the \(\ell\) binary digits of the name coordinate. Numerical order on these primary names is the binary order of the suffix. Some declared names are unused. Only the primary variables and the anchors are forced.

For the row whose ordinal has active prefix and remaining bits \((Z,X)\), put
\[
           Y=Z+\pi_b(X^3),\qquad
           (\ \pm \mathrm{name}(\mathrm{tag},Y,X)\ \lor\ 1\ \lor\ 2\ ).
\]
Use the positive sign exactly when \(Z=0\). For the other rows emit the identically indexed negative pin. The row-to-name map is an involution on each tag, hence a permutation on all rows. The anchors force exactly the advertised value at every primary name. Every row has three distinct variables. Given the nonlinear change of order furnished by that involution, the forced signs are constant on \(O(\ell)\) intervals.

Use one padded power-of-two slot \(P=\Theta(\ell)\) bytes per row, long enough to hold its literal, two anchors, zero terminator and newline. Reserve one byte for the sign, using a space for the positive sign. Put the header and anchor clauses at the beginning of a prefix of exactly \(vP\) bytes, padded with spaces. The rows occupy the next \(vP\) bytes. The header declares the largest primary name and \(v+7\) clauses. This gives \(N=16vP\) bits, a power of two, and the low-order \(\ell\) row-index bits are the binary row ordinal without subtraction.

In the initial prefix, put the entire header and anchor text on one aligned power-of-two interval of \(O(\ell+1)\) bytes. Its raw bit function has degree \(O(\log(\ell+2))\) in the low address bits by full interpolation. On the remaining whitespace the raw bit depends only on its position in a byte. Inside each active row prefix, separate \(Z=0\) and \(Z\ne0\), two consecutive ranges. At a fixed within-row offset, the physical bit is constant or a selected name bit, possibly complemented, of degree at most two. The same observation holds in each remaining gap with linear name bits. Multiply the expression for each offset by its Boolean address indicator and sum in \(\mathbb F_2\). This costs at most \(2+\log_2(8P)\) degree. There are only \(O(\ell)\) intervals in total, including gaps. Field arithmetic, tag decoding and within-row byte selection all take \(\mathrm{poly}(\ell)\) local work.

These inputs are satisfiable by construction. They can also be adjoined disjointly to any SAT instance while preserving its decision bit. For example, give the source identifiers a leading decimal 2, retain this gadget's anchors and 1-prefixed names, and update the header. On positive inputs the restriction to this gadget's primary names then has the same bound. Correct algorithms can evaluate the cubing predicate directly. The construction supplies no superlinear lower bound for SAT decision on a RAM; it identifies which witness representation fails even when the file has simple local syntax. The precise address-order/interval combination has not received an exhaustive priority check.

The executable check parses eight serialized files of 2,088,960 total bits, checks 4,080 forced primary values, tests 144,096 derivative/projection/input cases, enumerates all 43,435 possible two-dimensional block directions in a nine-bit example, and checks 3,430 single-point parity charges over 120 affine permutations and sampled piecewise approximations. The Lean file proves the two-point bound for each full cube-derivative fiber over a characteristic-two field, and the finite union counting step. The affine geometry, degree argument and serialization are manuscript proofs. [Finite audit](affine_witness_slice_audit.py) · [Lean](upstream-checks/AffineWitnessSlice.lean)
