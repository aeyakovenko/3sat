# The exact affine capacity of an explicit binary permutation table

For $q\ge1$ write $s_2(q)$ for its number of one-bits. Encode a permutation by its array of images of $0,\ldots,q-1$ in ordinary fixed-width binary. Suppose every output bit of a table $P_z$ is an affine Boolean function of unrestricted input bits $z$, and the table is a valid permutation for every $z$. The maximum possible rank of the affine map (the dimension of its image) is exactly
$$
                           q-s_2(q).
$$
Leading zero bits in wider fields have no effect. This is a bound on independent input bits, even if each entry can use arbitrarily many XOR gates. Combined with a matching upper construction below it puts an exact asymptotic price on one attempted transfer of the list circuit lower bound to [two-permutation exact cover](two-permutations-and-the-explicit-sat-clock.md).

## Proof by partitioning parameter and value space

Take $q>1$, $k=\lceil\log_2 q\rceil$, and quotient the parameter space by the kernel of the table map. Its remaining $r$ coordinates parameterize distinct tables. In $\mathbb F_2^r\times\mathbb F_2^k$, each row graph
$$
                  \{(z,P_z(i)):z\in\mathbb F_2^r\}
$$
is an affine subspace. The $q$ graphs are pairwise disjoint and together fill parameter space times $[0,q)$. If $q<2^k$, partition the complement $[q,2^k)$ into its aligned dyadic intervals. For example, take successive intervals ending at $2^k$ according to the binary expansion of $2^k-q$. Each fixes a prefix and leaves its suffix free. Add its product with parameter space as one more affine part. The number added is $s_2(2^k-q)$ and the smallest interval has $2^{\nu_2(q)}$ elements.

Let $J$ be the intersection of all direction spaces of the parts. An element $(h,v)\in J$ satisfies $P_{z+h}(i)=P_z(i)+v$ at every row. Projection of $J$ onto the value coordinate is injective by faithfulness. For $q<2^k$, $v$ must preserve the smallest tail interval, so $\dim J\le\nu_2(q)$. For a power of two simply use $\dim J\le k$. Quotient by $J$. All parts were unions of its cosets, so they remain a partition with the same number of nonempty parts, now with trivial common direction. Filmus et al.'s tight affine partition theorem says a partition with trivial common direction in binary dimension $D$ has at least $D+1$ parts. For $q=2^k$ this gives $r\le q-1$. Otherwise,
$$
 r\le q+s_2(2^k-q)-1-k+\nu_2(q)=q-s_2(q).
$$
The simplification uses $s_2(2^k-q)=k-s_2(q-1)$ and $s_2(q-1)=s_2(q)-1+\nu_2(q)$. For $q=1$ the rank is zero. [Filmus et al., *Irreducible subcube partitions*, §4.2.1](https://arxiv.org/pdf/2212.14685)

For attainment decompose $[0,q)$ into $s_2(q)$ aligned dyadic blocks. In a block of size $2^h$, write the original row address as $u_1\cdots u_h$. Attach one independent bit to each internal node of its complete binary prefix tree. Map $u_j$ to $u_j\oplus z_{u_1\cdots u_{j-1}}$, retaining the fixed block prefix. With the original row fixed each output is affine. With the parameter fixed the input address can be recovered from the output bit by bit, so the map permutes the block. Each switch can be read off a specified row and position. The rank is the sum of the numbers of internal nodes, $q-s_2(q)$. The [capacity audit](../audits/affine_permutation_capacity_audit.py) exhausts all affine spaces through the identity up to $q=5$, which suffices for all base permutations after reordering rows. It also checks the attaining construction through $q=257$.

## The cost of encoding an arbitrary list

Let there be $m\ge2$ records of $b$ bits, $m\le2^b$, and $L=mb$. Whether the records are distinct has as its additive periods precisely the simultaneous shifts $(a,\ldots,a)$. Indeed if $h_i\ne h_j$, take two distinct records at $i,j$ of difference $h_i+h_j$ and extend them to a full distinct list. Translating by $h$ collides those records. Any affine map through which the decision factors must therefore have rank at least $(m-1)b$. [Lean verification of the common-shift lemma for arbitrary record width and index sets](../lean/DistinctnessPeriod.lean)

If the target data are two always-valid $q$-point permutations and their decision bit is allowed to be **any function whatsoever of those tables**, it follows that
$$
                   2(q-s_2(q))\ge(m-1)b.
$$
For $m=2^k$ records of $b=2k$ bits, every affine reduction needs $\Omega(L\log L)$ physical output bits. A constant number of extra $O(q)$-bit indicator arrays preserves the asymptotic obstruction, since they add only $O(q)$ rank if affine. Treating an invalid table as another verdict, allowing a general Boolean circuit for the encoder, or changing the field representation changes the hypothesis.

The output-length bound is attainable even for the specific verdict that $S,P(S),Q(S)$ partition the points. Use a fixed formula with $m$ selectors, a shared $b$-bit string and $mb$ named data bits $d_{ij}$. A constant-size update per record tracks whether at least two selectors were set. When selector $i$ is set, impose equality between each $d_{ij}$ and the corresponding shared bit, using two width-three clauses. Thus satisfying assignments exist precisely when there is a collision. Each source clause mentions at most one data bit. The converse polarity takes one output negation. The formula has $O(L)$ constant-width records and names.

For each raw position use two source names $u_i,v_i$ and include $(u_i\lor v_i)$ and $(\neg u_i\lor\neg v_i)$ inside the guard; use $u_i$ as the data bit. Apply the [guarded cubic compiler](two-permutations-and-the-explicit-sat-clock.md) and designate a separate occurrence column of each of these two names. The following six-column component has two boundary ports and one control bit. Its forward arrays on $0,\ldots,5$ at control zero are
$$
                 P=(2,0,4,5,3,1),\qquad Q=(1,5,3,0,2,4).
$$
At control one interchange the two images $P(1)$ and $P(2)$. At the rows receiving $Q(5)$ and $Q(4)$ replace the respective contributions from the internal column bits $h_5,h_4$ by arbitrary external bits $x,y$. Checking the six row sums gives exactly the following table. The set in the last column lists all the internal bits equal to one.

| Control | $(x,y)$ | Internal selection |
| --- | --- | --- |
| 0 | $(0,0)$ | $\{1,2\}$ |
| 0 | $(0,1)$ | $\{1,4\}$ |
| 1 | $(0,0)$ | $\{1,2\}$ |
| 1 | $(1,0)$ | $\{2,5\}$ |

In every accepting row $(h_5,h_4)=(x,y)$. Consequently one can cross these two $Q$ incidences permanently with the designated occurrence columns for $u_i,v_i$. The component returns their correct values to the two outside receivers and enforces $u_i=0$ at control zero or $v_i=0$ at control one. When the guard is active, the source complementary-pair clauses fix $u_i$ to exactly the given data bit. At guard zero set *both* names to zero; all other ordinary source bits may be set to zero. The known guarded cover and its completions $\{1,2\}$ in all data components are independent of the data. The separate final guard patch therefore gives the very same packing and signed witness on the entire input cube. All physical triples still have three distinct receiver rows: the two switched $P$ tables are proper internally, and each static $Q$ exchange goes across disjoint components at columns that were separately designated.

Only the two $P$ entries of each data component vary. Relabel all the switched pairs of receiver indices as disjoint aligned consecutive pairs. This one public conjugation preserves the identity matching, the constancy of $Q$, and all solutions. The different receiver words in a pair now differ at their low bit only. Thus **one raw bit flips exactly two physical bits**, one in each of two words, and all these pairs of positions are disjoint. The two changed bits are necessary even for a single nonconstant permutation table, since two distinct permutations cannot differ in just one entry. The bit projection has $q=O(L)$ points and total length $O(L\log L)$. [Exhaustive switch and physical-array audit](../audits/list_to_permutation_switch_audit.py) · [Lean check of the port table](../lean/TwoBitPermutationSwitch.lean)

Six is also the least possible positive component size under these switch conventions. The identity incidence stays internal, only two $Q$ incidences are opened, and the zero external pair has a completion returning two zeros in both settings. Closing such a component gives a perfect cover, so its size is divisible by three. At size three, simplicity forces both internal $P$ settings to be derangements, since neither can meet the fixed identity incidence. The two derangements of three points are three-cycles of the same sign; a single transposition changes sign. This rules out three. The physical audit checked all 512 choices of control, external bits and six internal bits.

The same switches work for any fixed bounded-fan-in Boolean verifier with $s$ gates, $a$ public bits and $b'$ witness bits. Encode each gate by equivalence clauses and require a true output. Use two guarded source names and a separate component per public bit as above. The number of columns is $O(s+a+b'+1)$. The control bits for the public input toggle disjoint transpositions of a single fixed permutation; the other permutation, packing and signed solution are constant. This statement concerns an encoding by tables of the displayed size. For the list construction the short existential verifier above has $O(L)$ gates.

The imported list lower bound is $\Omega(L(\log L)^\sigma)$ with $\sigma\le1$ on these parameters. At output length $N=\Theta(L\log L)$ its numeric scale is $N(\log N)^{\sigma-1}$. This rules out transferring a superlinear gate lower bound by a length-preserving affine projection of this entire list function to two always-valid permutation arrays. Ordinary DIMACS has a different projection of length $\Theta(L)$. The obstruction leaves open both a more efficient nonlinear Boolean encoder and a direct RAM lower bound. Priority for the exact permutation-rank formulation is unverified. [List theorem and DIMACS projection](checking-the-sat-circuit-bound.md) · [Circuit upper and exponent ceiling](list-and-matrix-costs-for-ram-and-tapes.md)

On the list switch restriction the native worst-case clock is $\Theta(q)$ word steps on each verdict. For the upper bound, generate the fixed array skeleton and receiver renaming by consecutive-index loops over the explicit verifier and its constant-size gadgets. This takes $O(q)$ word operations; the regularizer's explicit coloring needs no sorting. Extract each control from its designated $P$ field and verify both arrays against the resulting template. For an unknown $k$, generate sizes in increasing order up to the known constant envelope for $2^k k=O(q)$; the geometric sum is $O(q)$ and only boundedly many candidates have the input size. Packing bits can be checked if supplied. Parse a fixed-width field with at most two native word reads. Assemble the $m$ list keys from $O(L)$ extracted bits, then perform two stable counting-sort passes with radix $m$ and check consecutive keys. A mismatch invokes complete exact cover. For the lower bound take all the $m=2^k$ keys in a $k$-dimensional subcube of the $2k$-bit universe. Flipping any one of its $mk$ varying raw positions collides two keys. The corresponding physical change sets are disjoint pairs of low bits. One native word of $\Theta(\log(q+2))$ bits can see only constantly many such sites, since they occur in distinct array entries of width $\Theta(\log(q+2))$. A correct run must read a site from each pair. Flipping the last pair first encountered gives a collision input that follows the same long prefix. Both verdict bounds are in steps on this restriction. As a function of the $L$ raw **controls** the inherited Boolean circuit bound is superlinear; the full explicit input uses $\Theta(L\log L)$ bits.

## What word-addressed swaps can store

There is a direct control for the affine bound. Start from the identity array. For $i=q-1,\ldots,1$ read an independent digit $j_i$ of $\lfloor\log_2(i+1)\rfloor$ bits and swap slots $i$ and $j_i$. The digit always names a live slot. The resulting array uniquely determines the digits. To decode, replay the construction from the identity with a table of current inverse positions. At step $i$ the eventual occupant of $i$ must be brought from its current position; that position is $j_i$. Replaying the swap updates both arrays in constant time. Thus $O(q)$ word steps encode and decode $\sum_{i=1}^q\lfloor\log_2 i\rfloor=q\log_2 q-O(q)$ independent bits. Packed variable-width digits can be extracted or written across at most two words each. This near-entropy storage bound establishes no reduction from list distinctness to the exact-cover verdict. It identifies a concrete native operation that escapes the affine rank limit.

## A bound when the encoder has nonlinear gates

Suppose the preprocessing has arbitrary affine operations and $t$ nonlinear two-input Boolean gates. If its two valid permutation tables suffice to decide distinctness after arbitrary postprocessing, then
$$
          t+2(q-s_2(q))\ \ge\ \tfrac12 m\log_2 m .
$$
In particular $q=O(m)$, $b=2\log_2 m$ requires $\Omega(L)$ nonlinear gates. This bound still permits linear-size nonlinear preprocessing.

To prove it, let $U=c+V$ be any affine subspace of lists on which all $m$ records are distinct. For $i\ne j$, the possible differences between those two records form an affine space avoiding zero. Separate it from zero by a binary linear form $w_{ij}$ that equals one on the whole difference set. The vector placing $w_{ij}$ in row blocks $i,j$ and zeros elsewhere lies in $V^\perp$. Let $H$ be the span of one such vector per pair. Write $H_i$ for its projection onto block $i$ and $r_i=\dim H_i$. The sets $c_i+H_i^\perp$ in the common $b$-dimensional record space are pairwise disjoint, since $w_{ij}$ separates the corresponding two sets. Thus $\sum_i2^{-r_i}\le1$, giving $\sum_i r_i\ge m\log_2 m$ by convexity. A basis of $H$ chosen from the pair vectors touches only two row blocks per vector, so $\sum_i r_i\le2\dim H\le2\operatorname{codim} U$.

Choose an all-distinct input. Process the nonlinear gates in order, each time fixing its first input to the value taken there. This imposes at most one affine equation on the surviving affine subspace, because all previous gates have become affine there. Any binary Boolean gate with its first input fixed is affine in the second. On the resulting subspace the output permutations are affine and always valid. Fix both tables to their values at the chosen point. This costs at most another $2(q-s_2(q))$ independent equations by the capacity bound. Postprocessing is constant on the resulting subspace, so every list there is distinct. Its codimension must meet the preceding inequality.
