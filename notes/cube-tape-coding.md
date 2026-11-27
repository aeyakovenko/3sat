# Can a few positions on a random tape hide a hard output?

**Research journal, 24 November 2026.** A proposed sampler might use a long random tape to select a hard word, although fixing a few scattered bits already guarantees its answer. I obtained an unconditional deterministic coding bound for this case. It also covers samplers that read every random bit and need the full time allowance to publish. The sets that guarantee success can vary with the word and the deadline. The decoder does not receive them.

A subcube $C$ fixes a finite set of bit positions of an infinite fair tape. Write $w(C)$ for their number and $u(C)=2^{-w(C)}$ for its fair probability. At time $t=2^q$, call $C$ successful for $y$ if every tape in $C$ makes the fixed ordinary sampler publish $y$ by $t$. Only the first $t$ positions matter in a one-bit-per-read convention. Let $\mathcal C$ be a finite collection of successful cubes, with nonnegative weights $v_C$ satisfying $\sum_{C\ni z}v_C\le1$ at every tape $z$. Put $p_*=\sum_C v_Cu(C)>0$. A disjoint union with weights one is a special case. For each fixed $a\ge1$ the following conclusions hold on a fixed efficient literal deterministic reference.

1. Suppose every $C$ has at most $a(1+\log_2\log_2(r+4))$ fixed positions among the first $r$, for each $r\ge1$. There is an exact prefix name of length $\lceil-\log_2 p_*\rceil+O_{S,a}(1)$ printing all of $y$ in $t(q+2)^{O_{S,a}(1)}$ steps.
2. Suppose only that $w(C)\le k\le a\log_2(q+2)$ for every $C$, with no restriction on the positions. At the same clock one can add a self-delimiting description of $j=\lceil\log_2(\max(2,k))\rceil$ to the length bound in 1. In particular this costs at most $\log_2(j+1)+2\log_2\log_2(j+3)+O(1)$ extra bits. This is useful when the proposed violation needs a growing length gap.

In both statements the program is inputless, and $y$ may be as long as the output channel allows. When $p_*$ is a constant fraction of the word's total timely probability, statement 1 gives precisely the constant-bit deterministic coding guarantee on which the [linear SAT test](recovering-longer-outputs.md) depends. Statement 2 leaves an additive gap of order $\log\log(k+2)$. I have no unconditional way to obtain a hard output from that gap.

## One distribution for all the clocks

Choose an integer $u\ge2$ and a fixed large integer $A$. Let $s_i=2^iu$, $h_i=2^{s_i}$ and $d_i=2^{h_i}$. Block zero contains positions $1,\ldots,d_0$ and block $i>0$ contains positions $d_{i-1}+1,\ldots,d_i$. The ideal distribution below uses new uniform seed bits for each block, independently. The law of a prefix never changes as later blocks become available. This matters for allocating program lengths across all deadlines.

In block $i$ set $K_i=A(s_i+1)$ and $\eta_i=2^{-i-3}$. We need relative accuracy $1-\eta_i$ on each prescription of at most $K_i$ bits. Use the following finite version of the almost $k$-wise independence construction. Give each position in this block a distinct label $\alpha$ in $\mathbb F_{2^{h_i}}$, using its zero-based absolute position. Write the coordinates of $(1,\alpha,\ldots,\alpha^{K_i-1})$ consecutively as a binary word of length $L_i=K_i h_i$. The binary sum for any nonempty set of at most $K_i$ labels is nonzero. Indeed the first as many powers as there are labels give an invertible Vandermonde minor over the label field. [Alon, Goldreich, Håstad and Peralta](https://www.wisdom.weizmann.ac.il/~oded/p_aghp.html)

Use those bits as polynomial coefficients over a second binary field of degree $\ell_i$, taking $\ell_i$ to be the least power of two at least $K_i+\lceil\log_2(L_i+1)\rceil+i+3$. With independent uniform field elements $X_i,Y_i$, the tape bit is the binary inner product of $Y_i$ and the polynomial evaluated at $X_i$. In the character average for any nonempty set of at most $K_i$ positions, the average over $Y_i$ vanishes unless the nonzero sum polynomial vanishes at $X_i$. Its absolute bias is at most $(L_i-1)/2^{\ell_i}\le\eta_i2^{-K_i}$. For any prescribed $b\le K_i$ bits expand its indicator as $2^{-b}$ times the sum of the $2^b$ signed parity characters. Its probability is at least $2^{-b}(1-\eta_i)$.

Both fields have degrees that are powers of two, and one can construct their arithmetic uniformly in time polynomial in the degree. Starting over $\mathbb F_2$ with trace-one element $c=1$, extend by $Z^2+Z+c$. The map $x\mapsto x^2+x$ has the trace-zero hyperplane as its image, by the kernel size and the trace identity, so the quadratic is irreducible. The relative trace of $Z$ is one, making $cZ$ a trace-one element for the next extension. Storing each element by its two coordinates at each level gives polynomial-time arithmetic by recursive multiplication and reduction. Thus no table of $d_i$ elements is needed.

Call the resulting infinite tape law $D_u$. If a cube fixes at most $K_i$ bits in block $i$, independently multiplying the block probabilities gives

$$
D_u(C)\ge\left(1-\sum_{i\ge0}\eta_i\right)u(C)=\tfrac34 u(C).
$$

Only finitely many nonempty blocks are relevant. The pointwise bound on the fractional cover now yields $D_u[S\text{ publishes }y\text{ by }t]\ge3p_*/4$. The same reasoning works with lower bounds obtained from an arbitrary finite subfamily, without any procedure for finding the cubes, their weights or their fixed positions.

## Enumerating the seeds in the time available

To supply the first $r$ virtual random bits, let $i$ be the last block reached. The total number of underlying random bits is $\sum_{b=0}^i2\ell_b=O_A(s_i)$. If $i>0$, then $r>d_{i-1}$ and $s_i\le 2\log_2\log_2(r+4)$. In the initial block $s_i=u$. Hence at most $2^{O_A(u)}(\log_2(r+4))^{O_A(1)}$ equally weighted seed strings suffice for the entire prefix. Computing each virtual bit takes $\mathrm{poly}(h_i,K_i,\ell_i)$ time, which fits the same bound. A bounded simulator can determine the last block by comparing binary index lengths to $h_i$, without constructing a block endpoint beyond its clock.

For a fixed $u$, at epoch $e$ simulate all the needed seeds through $2^e$ steps of $S$ and compute the exact distribution of published words. Native interpretation, exact counts, sorting outputs and restarting runs use $2^e 2^{O_A(u)}(e+u+2)^{O_A(1)}$ time. The same bound through the whole epoch holds when scanning all earlier epochs. Since $D_u$ is a single law, the computed masses for each word are nondecreasing with $e$ and their eventual sum is at most one. For each word and each integer depth $d\ge0$, issue a request once, at the first epoch when its mass reaches $2^{-d}$, of width $2^{-d-3}$. At epoch $e$ only process $d$ up to the number of underlying seed bits for that epoch plus two, postponing greater depths until eligible. Requests for one word have total width at most one quarter of its eventual probability. Assign aligned dyadic cells of half the requested width inside consecutively placed disjoint intervals. A decoder reproduces this process and caches address bits, consuming exactly the selected cell's address. All finite counts and addresses have polynomial bit cost in $e+u+2$, and explicit words can be compared within the simulation bound. [Exact-prefix interval allocation](recovering-longer-outputs.md)

For statement 1 take $u=2$ and $A$ large enough depending on $a$. The restriction on the first $d_i$ positions bounds the number of fixed bits in block $i$ by $K_i$. For statement 2 read the self-delimiting $j$ first and use $u=2^j$. This choice makes every $K_i$ at least $k$ and $2^{O_A(u)}$ a polynomial in $q+2$. At epoch $q$ any positive atom of the enumerated table has probability at least the inverse seed-space size, so the depth needed for that atom is already eligible. Use $d=\lceil-\log_2 D_u[S\text{ publishes }y\text{ by }t]\rceil$. It differs from the desired upper bound by at most a constant. These steps prove both claims. The choice of law indexed by $j$ can equivalently be hardwired at a cost depending on $j$ when all widths are bounded by one fixed constant.

## Why one fixed small seed table misses some early positions

The unrestricted-position case cannot be proved by asking one prefix-consistent law with only $(\log(r+4))^{O(1)}$ possible first-$r$ strings to give every eligible subcube positive probability. Fix any such law whose prefixes can be listed in $r^{O(1)}$ time. A single ordinary sampler reads a self-delimiting binary encoding of an integer $k$, of length $h=O(\log(k+2))$. It computes the possible first $h+k$ bits under the proposed law. For every large $k$ these cover fewer than $2^k$ continuations of the specific header. Find the first missing continuation by sorting the list, then read $k$ actual fair bits. Publish $\mathrm{bin}(k)$ exactly on that continuation, with a fixed rule for the finitely many small cases. This is one successful prefix cylinder of width $k+h$ and fair mass $2^{-(k+h)}$. The proposed law gives it zero. Even at the padded clock $t=2^{2^{2k}}$ this width is at most $\log_2\log_2 t$ for large $k$. A finite union of the proposed prefix supports fails by the same count.

The resulting word has an immediate deterministic name from its integer header. The example defeats a requirement on a universal distribution of test tapes. It leaves open the possibility of constant-bit deterministic coding for every sampler with the unrestricted-position promise by a procedure adapted to that sampler. A counterexample to linear SAT still needs a word defeating every short deterministic program on the target reference.

## Overlapping successful conditions

There is a stronger lower bound when many small certificates can hold on the same tape. For a finite collection of successful cubes and arbitrary nonnegative weights put $Z=\sum_C v_C1_C$, with positive fair mean. Replace $p_*$ in both statements by

$$
p_2=\frac{(\mathbb E_{\rm fair} Z)^2}{\mathbb E_{\rm fair} Z^2}.
$$

Increase the local width budget by a factor of two. The relative estimate now applies to each cube and to each compatible pairwise intersection. For upper bounds the product of $1+\eta_i$ is at most $4/3$, using $1+\eta_i\le1/(1-\eta_i)$. Empty intersections have zero mass under both laws. Therefore $\mathbb E_{D_u} Z\ge(3/4)\mathbb E_{\rm fair} Z$ and $\mathbb E_{D_u} Z^2\le(4/3)\mathbb E_{\rm fair} Z^2$. Cauchy–Schwarz bounds the mass of $Z>0$ under $D_u$ from below by $27p_2/64$. All these tapes print $y$. For a fractional cover as above, $Z^2\le Z$ and this gives $p_2\ge p_*$. No enumeration of the certificate pairs is performed by the decoder.

For example, take $2^k$ disjoint groups of $k$ bit positions. Publish a common answer if at least one group is all ones. Every successful cube fixing at most $k$ bits must specify one whole group. All these minimal cubes meet at the all-ones tape, so their best fractional packing has weight only $2^{-k}$. With all weights one, their indicators under fair bits are pairwise independent, giving $\mathbb E Z=1$ and $\mathbb E Z^2=2-2^{-k}$. Thus the second-moment guarantee captures a constant probability uniformly in $k$.

## Constant-bit coding at arbitrary positions under a two-sided condition

At epoch $e$ discard the block schedule and use **one** finite almost-independent distribution for all $2^e$ positions, with width $K_e=\lceil a\log_2(e+2)\rceil$ and relative error at most $1/4$. The same Vandermonde construction works with field degree the least power of two at least $e+1$. The seed length is $O_a(\log(e+2))$. These laws can change between epochs. We can still allocate one global prefix code if the following aggregate bound holds.

Write $F_{e,y}$ for the set of tapes printing $y$ by $2^e$. Let $b_{e,y}$ be the minimum fair cost of an outer fractional cover of $F_{e,y}$ by cubes of width at most $K_e$: nonnegative weights satisfy $\sum_{C\ni z}v_C\ge1$ on every $z\in F_{e,y}$, and cost is $\sum_Cv_Cu(C)$. Include the empty cover for an empty event. Suppose

$$
H=\sum_y\sup_{e\ge1} b_{e,y}<\infty .
$$

The finitely enumerated seed distribution at epoch $e$ assigns mass at most $(5/4)b_{e,y}$ to each output, by its multiplicative upper bound on each cover member. Issue a request at each depth once, on its first threshold crossing, repeating the scan through eligible depths at each new epoch. Although the masses need not increase, the sum of the dyadic widths for one output is bounded by twice its supremum mass over all epochs. A fixed scaling depending only on $H$ now gives one prefix code for every clock. The decoder needs only a fixed integer upper bound on $H$, and never tries to find an outer cover. If at epoch $q$ the output also has the inner second-moment bound $p_2$ with width at most $K_q/2$, the finite generator assigns it mass at least a constant times $p_2$. The resulting name has length $\lceil-\log_2 p_2\rceil+O(1)$ and the same near-deadline clock, with **arbitrary placement of the fixed positions**.

A concrete case requires no fractional-cover assumption to be separately checked. Suppose the arrival map at every epoch, including its timeout symbol, has the property that each tape has a certificate of its exact outcome fixing at most $h_e$ bits, where $h_e^2\le K_e$. For one word's indicator both the zero and the one certificate complexities are then at most $h_e$. On a restriction, query the full set of still-unfixed variables in any consistent one-certificate. A match returns one. On every other branch every compatible zero-certificate loses a variable, because it conflicts with the selected one-certificate on an as-yet unfixed variable that has just been queried. After at most $h_e$ rounds, any surviving zero certificate has width zero, or no zero input remains. This gives a decision tree of depth at most $h_e^2$, handling constant restrictions directly. Its disjoint one-leaves exactly partition $F_{e,y}$ into cubes of width at most $K_e$. Thus $b_{e,y}=\Pr_{\rm fair}(F_{e,y})$ and $H\le1$. Those same one-leaves also give a multiplicative lower estimate for the generator directly, without using pair intersections. In this case every positive output has an optimal-length deterministic name up to a constant by the nearby clock. The tree and its certificates may differ for each word and can be unknown to the simulator.

## Forcing all narrow certificates to come from early computations

I tried to deduce the inner-cover condition from the mass of an arbitrary sampler's answer. The following transformation defeats that step quantitatively, independently of output length. Simulate any ordinary sampler $S$ while keeping its native step count $\tau\ge1$. When it would publish, hold its result and read $\tau$ fresh random bits. Publish only on even parity, and never publish on the other branch. Call the modification $S'$. For each original completion time, exactly half the mass producing each word survives, within total physical time $O(\tau\,\mathrm{polylog}(\tau+2))$. This also preserves a hypothetical high-mass counterexample after adjusting the fixed constants and clock exponents.

For $k\ge2$, let $V_k(y)$ be the fair measure of the union of **all** width-at-most-$k$ cubes guaranteeing that $S'$ eventually publishes $y$, with no deadline on this union. There is a two-sided estimate in terms of the original $S$:

$$
\tfrac12 \Pr[S\text{ publishes }y\text{ by }\lfloor k/2\rfloor]
\ \le\ V_k(y)\ \le\
\tfrac12 \Pr[S\text{ publishes }y\text{ by }k].
$$

For the upper bound, fix any tape in one of the guaranteeing cubes. If its original completion used $\tau>k$ steps, at least one of the $\tau$ fresh bits is unfixed. Flipping that bit preserves the cube and the entire original run, but prevents publication. Therefore every tape in the union comes from an original completion by $k$ and passes the independent parity check. For the lower bound, every retained original run with $\tau\le k/2$ reads at most $\tau$ original bits. Fix its entire consumed prefix including the parity bits. This is a successful cube of width at most $2\tau\le k$. The bound applies even when the original sampler adaptively chooses how many random bits to read.

In particular every inner mass above, including the second-moment value for an overlapping family, is at most the right side on $S'$. When $k=O(\log(q+2))$, the original early mass is exactly computable by simulating $2^k$ tapes through $k$ steps, in $\mathrm{poly}(q+2)$ time. An actual source could retain substantial later probability for reasons invisible to every such certificate. An argument that uses only the existence of this parity obstruction also applies to easy deterministic outputs. Establishing slow printing by all short deterministic programs requires information about the output itself.

Lean checks the finite product, disjoint-event aggregation and consistency-under-refinement inequalities. The Python experiment exhaustively compared 88 parity biases with their exact root counts and checked 490 prescribed cylinders on three finite parameter choices. The asymptotic source and prefix-code arguments are manuscript proofs. [Lean checks](../lean/TapeCubeMass.lean) · [Finite field experiment](../audits/cube_tape_experiment.py)
