# An exactly calibrated finite-field evaluation of the genuine RAM gate circuit

Take the [locally indexed, closed Boolean circuit](projected-parity-holes.md) computing the genuine bit $b_j$ at native scale $M=2^j$. A residual bit on each gate, including each constant source, flips that gate's output. Write $F(r)$ for the circuit result with residual vector $r$. The canonical multilinear extension $\widetilde F$ has one variable per residual bit. At a real vector of flip probabilities it gives the noisy output probability. The following modification makes an evaluation in characteristic two and one modular digit of a real noisy evaluation equal to the **actual noiseless answer**, on every stage. The input to the search problem is still just the stage metadata and its locally generated circuit.

Replace each gate by itself followed by one identity gate. Connect **all** outgoing wires, including the output tap, to the buffer. Gates with shared fanout are paired once, regardless of how many children they have. A bypass can destroy the identity. If an XOR gate reads both the raw output of a gate and its buffered copy, that XOR gives the second fault bit, whose characteristic-two diagonal is the indeterminate itself even after buffering the XOR. Two distinct residual variables are supplied to each pair. This doubles the gate count. There is a direct uniform translation of a gate index and its parent queries using one extra tag bit. The noiseless circuit computes $b_j$.

1. Over any commutative ring of characteristic two, assign *an arbitrary common value within each pair* to the two corresponding arguments of the canonical multilinear extension. The exact evaluation is $b_j$. This is a polynomial identity, including over $\mathbb F_2[t_1,\ldots,t_m]$ with a different paired indeterminate at each of the $m$ original gates. In particular every scalar diagonal in $\mathbb F_{16}$ gives the bit itself.
2. Give each physical gate an independent real flip of probability $1/4$. Let $P$ be the resulting exact probability of output one. Its denominator in lowest terms is a power of two, so $P$ has a well-defined reduction in $\mathbb F_3$. Then $P\bmod 3=b_j$. Longer locally indexed identity chains give arbitrarily many correct ternary digits in the sense of congruence in the rationals with denominator prime to three.
3. At this same quarter-flip rate, circuits computing complementary true pins can have real output probabilities within $4^{-L}$ of one another after $2L$ additional physical gates. Their reductions modulo three remain opposite. The real estimator for $P$ and the exact modular readout target different amounts of information about the same number. [Real-noise estimator](noisy-evaluation-of-a-native-run.md)

## Grouping residuals before evaluation

For bit tuples, the pair simulates a single original gate with residual $u_g=r_{g,0}\oplus r_{g,1}$. Topological induction proves equality even when a buffer drives several paths which later meet. In the interpolation formula for the modified function each Boolean micro-assignment contributes its output times a product of factors $s$ or $1-s$ for its own coordinates. Group these terms by the parity in **each** disjoint pair. The effective weight of a flip in a pair with formal parameters $s,t$ is
$$
       c=s(1-t)+(1-s)t=s+t-2st.
$$
The effective weight of no flip is $1-c$. Equivalently
$$
   \begin{pmatrix}1-s&s\\s&1-s\end{pmatrix}
   \begin{pmatrix}1-t&t\\t&1-t\end{pmatrix}
   =\begin{pmatrix}1-c&c\\c&1-c\end{pmatrix}.
$$
This identity holds in every commutative ring. The exact canonical evaluation is $\widetilde F((c_g)_g)$, using the effective parameter of each gate. In characteristic two, $c=s+t$; setting $t=s$ gives zero. The identity is for the multilinear extension of the residual-to-output predicate. Generic noisy evaluation of a gate circuit by substituting gate-wise expectations can give wrong values when parents are correlated. Grouping the original independent residual *variables* avoids that issue.

This calculation holds even for an arbitrary Boolean predicate of the grouped parities. For the paired circuit's particular characteristic-two subspace there is an additional equality: arithmetic evaluation of the original gate-by-gate polynomial with the two equal residuals cancels both additions before the next gate sees their value. Thus even the possibly nonmultilinear arithmetic circuit returns the true bit on this subspace. This gives a direct gate-list algorithm with one arithmetic evaluation per original gate; it has not given a subnative-time algorithm on the succinct input. Unlike the [missing-table evaluation](support-filtered-parity.md), the predicate here is the faulty circuit's actual output and requires no measurement of Hamming weights of missing tables. The independent-bit noise operator and classical channel composition have extensive precedents. [O'Donnell, *Analysis of Boolean Functions*](https://arxiv.org/abs/2105.10386)

## Which modular digit the real probabilities carry

For any prime $\ell$, let $\mathbb Z_{(\ell)}$ consist of the rationals whose reduced denominator is prime to $\ell$. Reduce $A/B$ modulo $\ell^s$ by multiplying the numerator by the inverse of the denominator there. By the integer coefficients of $\widetilde F$, if all effective probabilities belong to $\ell^s\mathbb Z_{(\ell)}$ then the noisy probability is congruent to $\widetilde F(0)=b_j$ modulo $\ell^s$. In particular any physical rational rate with numerator divisible by $\ell$ and coprime denominator already has the single-digit property without added buffers.

For the quarter-flip pair the effective rate is $3/8$ and the exact equation is
$$
         8^m P=\sum_{u\in\{0,1\}^m}F(u)\,3^{|u|}5^{m-|u|}.
$$
Reducing modulo three gives $5^m b_j$ on the right and $8^m P$ on the left. Since $5\equiv8\not\equiv0$, the stated residue follows. Equivalently, if one works with the $2m$ *physical* quarter-flip bits and multiplies by $4^{2m}$, every physical pattern with some unflipped gate has weight divisible by three. The surviving all-flipped pattern is correct because both faults cancel in each pair.

For a length-$r$ block comprising one original gate and $r-1$ identity buffers, all fanout is taken after the block. Under independent quarter flips the expected sign of the XOR of the $r$ faults is $2^{-r}$. Its effective flip probability is
$$
                   (2^r-1)/2^{r+1}.
$$
Choosing $r=2\cdot 3^t$ makes the numerator divisible by $3^{t+1}$ and indivisible by $3^{t+2}$. For $t=0$, $2^2-1=3$. If $x=2^{2\cdot3^t}=1+3v$, then $x^2+x+1=3(1+3v+3v^2)$, so cubing $x$ increases $v_3(x-1)$ by exactly one. Every such buffered genuine circuit satisfies $P\equiv b_j\pmod {3^{t+1}}$. At fixed $t$ the size factor $r$ is constant. More generally a constructible $t=O(j)$ gives $O(j)$-bit physical gate identifiers and a size factor $2\cdot 3^t$ which must be charged in any explicit circuit. The congruence alone does not estimate the real probability to a similar number of digits.

Real quarter flips have denominators divisible by two and provide no general reduction in $\mathbb F_2$. A different rational experiment gives ordinary binary congruences. At physical rate $1/3$ a block of length $r=2^t$ with $t\ge1$ has effective probability $(3^r-1)/(2\cdot3^r)$. At $r=2$ the numerator $3^r-1=8$ has 2-adic valuation three. When doubling an even $r$, $3^r+1\equiv2\pmod8$, so the valuation rises by one. After the displayed factor two is removed the effective probability belongs to $2^{t+1}\mathbb Z_{(2)}$ and the true output is recovered modulo $2^{t+1}$. This is separate from the formal characteristic-two identity, which requires no experiments or divisibility estimates.

## Real closeness and the cost on the actual family

Start with the paired actual circuit and add $L\ge1$ further logical identity gates, each followed by its own buffer. On the second pin let the first added gate be NOT instead. Both families still have locally generated descriptions when $L$ and its allocation are locally computable. In the noiseless experiment and in the all-flipped physical experiment their answers are respectively $b_j$ and $1-b_j$. With independent quarter flips, couple all physical randomness between the two circuits. Their outputs are complements. If $P_0$ denotes the first core's original noisy probability, the two final probabilities are
$$
            P_{\pm}=\tfrac12\ \pm\ 4^{-L}(P_0-\tfrac12).
$$
Each lies within $4^{-L}/2$ of one half. Their exact mod-three digits differ, so the pair cannot coincide. In fact $0<P_0<1$ from the output gate noise, and $P_0\ne 1/2$ because $1/2$ has ternary residue two. Write its reduced denominator as $2^a$ with $a\ge2$. The numerator of $P_0-1/2$ at this denominator is odd; the reduced denominators of both $P_\pm$ are therefore exactly $2^{a+2L}$. An oracle required only to return an additive $4^{-L}/2$ approximation can return one half on both inputs. Even independent samples of the final bit require $\Omega(16^L)$ samples to distinguish the two Bernoulli laws with worst-case error below a specified constant less than one half. Indeed their relative entropy is $O(16^{-L})$ since both biases are bounded away from zero and one; independent repetitions add divergences and Pinsker bounds their total variation. This calculation concerns observations of the final noisy bit. A verifier inspecting the circuit description has the additional structural information in its gates.

The characteristic-two polynomial evaluation, the ternary residue at quarter noise and the binary residue at one-third noise each give a specific exact observable on a faithful local encoding. Any fixed sound deterministic procedure reporting either digit value for one fixed pin from $j$ needs $\Omega_D(2^j)$ native time on every sufficiently late success by the [priority bit theorem](priority-pinned-sat.md), including for the doubled circuits. A short ordinary nondeterministic certificate of the digit on infinitely many stages within $2^{\lfloor j/k\rfloor}/(j+1)^B$ steps would therefore exclude unrestricted $O(n^k)$ SAT for sufficiently large fixed $B$, $k=1,2,3$, by [packed bounded verification](collision-forecasts-for-sat.md). What is available unconditionally is the calibrated digit and a local description of the polynomial. Constructing a sound nondeterministic procedure with the stated clock that reports the digit on infinitely many genuine stages remains open.

[Lean checks of channel composition, the cube identity and the ternary lifting exponent](../lean/ModularNoisyGateEvaluation.lean) · [Finite field and rational audits](../audits/modular_noisy_gate_evaluation_audit.py)
