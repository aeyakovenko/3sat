# How many bits separate the two local views of a deterministic RAM run?

**Research journal, 27 November 2026.** For a fixed input to a deterministic RAM, one integer sum of per-record weights strictly separates all false CPU histories from all locally legal memory histories. In the worst case the largest coefficient needs linearly many bits in the number of event slots. A program with one writable address attains this bound. Its two convex hulls of single-event frequencies have distance exactly $2^{-\ell}$ after $\ell$ iterations. Three fixed integer sums, compared for equality, distinguish the same histories using only logarithmically many bits and no knowledge of the true trace. Over the field of two elements the exact fixed linear cost is instead $\ell+1$ bits. The construction also works at the first missing output of a universal native interpreter equipped with this program as a branch.

## A separating score for every deterministic run

Fix an input, a deterministic program, and a clock with $T$ ordered writable-memory event slots. Use separate ordinary load and store records. Each record identifies its time, operation, address, and returned or stored value. A store carries its new value. Use a reserved no-op record for an inactive slot, and check read-only input directly in the CPU view. A CPU history follows the program, with freely guessed replies to its loads. In this section retain only CPU histories with an answer different from the genuine answer. A memory history has correct initialization, increasing time at each address and legal load replies. It may include events at several different addresses with the same timestamp. Attach the output check to the CPU, as in the append-only version of the native construction. [Native model](native-missing-word.md) · [The two local checks](public-memory-fingerprints.md)

Let $g_t$ be the true record in slot $t$, numbered from zero. If it is a load, let $F_t$ contain the loads identical to $g_t$ except for a different reply. For a store or no-op let $F_t$ be empty. Give a record $e$ stamped $t$ the weight

$$
4^{T-1-t}
\begin{cases}
1 & e=g_t,\\
2 & e\in F_t,\\
-1 & \text{otherwise.}
\end{cases}
$$

**Theorem 1.** The genuine history has score $G=\sum_{t<T}4^{T-1-t}$. Every false CPU history has score greater than $G$. Every legal memory history has score at most $G$, with equality only for the genuine multiset.

**Proof.** Following a genuine prefix fixes the next operation and its operands. The first different CPU record must therefore be a load with a fabricated reply. Its unweighted score exceeds the genuine one by 1. The deviation at any subsequent slot is at least $-2$. Starting from a positive integer, appending a digit by $z\mapsto4z+d$ with $d\ge-2$ leaves it positive.

At the first differing slot of a legal memory history, the earlier genuine prefix determines the value at the genuine address. None of $F_t$ can appear. If $g_t$ is missing, the total at this slot is at most zero. If it is present, it occurs once and there must be at least one additional negative record. The deviation is thus at most $-1$. At every later slot, all records with a positive weight have a single address in common. Strict local timestamp order permits at most one of them. The later deviation is at most 1, even when the total number of records at that time is unrestricted. From a negative integer, $z\mapsto4z+d$ with $d\le1$ stays negative. This proves the inequalities. ∎

In particular the convex hulls of the two sets of record-incidence vectors are disjoint. An integer weight uses $O(T)$ bits, regardless of the RAM word width. This construction uses the genuine records as advice. Computing the power of four from the clock is easy. Determining whether an arbitrary record is the genuine one at its timestamp can require evaluating the computation one is trying to certify.

## A sharp example with one writable address

Store zero at address zero. Repeat the following instruction sequence $\ell\ge1$ times. Load the cell into $a$, load it again into $b$, and write $a\lor b$ to the cell. Return the last word written, which remains available in a register. Use single bits for now. The genuine result is zero. The complete record schedule has $3\ell+1$ events. Denote the stored bits by $W_0,\ldots,W_\ell$ and the two load replies of stage $i$ by $a_i,b_i$.

On this fixed schedule let $C$ contain the CPU logs with $W_0=0$, $W_{i+1}=a_i\lor b_i$, and $W_\ell=1$. Let $M$ contain all memory logs with $a_i=b_i=W_i$, allowing arbitrary writes. Represent a mixture of full logs by the probability of a one at each of the $3\ell+1$ slots. The distance is the sum of the absolute differences of these probabilities, equivalently the sum of the total variation distances of the single-slot distributions.

**Theorem 2.** The distance between the two convex hulls on this schedule is exactly $2^{-\ell}$. Every integer sum of arbitrary per-record weights strictly ordering these two sets has a difference of at least $2^\ell$ in absolute value between its two weights for the initial store.

**Proof.** Set $p_i=2^{i-\ell}$ and draw $U$ uniformly from the half-open unit interval. For a memory log take $W_i=[U<p_i]$, and repeat that bit on both loads. For a CPU log take $a_i=[U<p_i]$ and $b_i=[p_i\le U<2p_i]$, set $W_0=0$, and perform the required ORs. The final CPU output is one on every draw. Each false CPU load and its matching memory load have the same marginal. For $i\ge1$, even the two values of $W_i$ agree on every draw. Only the initial write differs in marginal, by $p_0=2^{-\ell}$.

For the reverse bound consider the linear score
$$
 S=\sum_{i=0}^{\ell-1}2^{\ell-1-i}(a_i+b_i-2W_i).
$$
Every memory log has score zero. Using $a+b=(a\lor b)+ab$, a CPU log has score
$$
 W_\ell-2^\ell W_0+
 \sum_{i=0}^{\ell-1}2^{\ell-1-i}a_i b_i\ \ge\ 1.
$$
The largest absolute coefficient is $2^\ell$, so any two mixtures differ in the stated distance by at least $2^{-\ell}$. For an arbitrary integer score strictly ordering the sets, the gap in expected scores of the explicit mixtures is at least one, since it is at least one on every pair of logs. Their marginals differ only at the initial store. The claimed lower bound on its weight difference follows. ∎

The scores of false histories for this particular $S$ attain every integer from 1 to $2^\ell$. Take every $a_i=1$ and use the bits of any integer in $[0,2^\ell-1]$ for the $b_i$. Thus residues of this score modulo a list of moduli distinguish all false logs from zero exactly when their least common multiple exceeds $2^\ell$. Other modular scores can behave differently. In particular the integer precision bound concerns strict ordering. It does not lower-bound arbitrary equality fingerprints or the length of a program generating coefficients.

If the memory checker also pins $W_0=0$ as an extra publicly known condition, the distance for the all-free stages is $2^{1-\ell}$. Set both copies of the memory-side initial reads to zero in the construction. The only marginal errors are the two CPU loads of the first stage, of size $2^{-\ell}$ each. In the reverse bound remove the now identically zero coefficient of $W_0$ from $S$. Its remaining coefficients have magnitude at most $2^{\ell-1}$.

## Three small equality checks and a sharp binary cost

A common additive digest assigns the same group element to a given record in either log and sums over the records. With a bound on the total number of records, exact integer sums can be implemented in a sufficiently large finite cyclic group. In this section the schedule of the one-cell OR program is public. If the local memory view also permits other schedules, first require its records to have the prescribed address and operation at their timestamps and to have the prescribed total count. This restriction is sound and streamable for this program. Because at most one record occurs per address and timestamp, it forces the whole schedule. The check also has an additive implementation counting invalid records and total records.

**Theorem 3.** Three nonadaptive integer sums, with $O(\log(\ell+1))$ bits for their combined reply, distinguish every false CPU history from every legal memory history. They use only the program and the slot index.

Use the scores
$$
U=\sum_i(2W_i-a_i-b_i),\qquad
D=\sum_i(a_i-b_i),\qquad
P=\sum_i i(a_i-b_i).
$$
Every memory log scores $(0,0,0)$. On false CPU logs, $2(a_i\lor b_i)-a_i-b_i=[a_i\ne b_i]$. Since $W_0=0$ and $W_\ell=1$, summation gives $U=\#\{i:a_i\ne b_i\}-2$. If $U=0$, the loads differ at exactly two distinct stages. If also $D=0$, the signs of those two discrepancies are opposite. Their weighted sum $P$ is the nonzero difference between their stage numbers. The three scores range over intervals of lengths $O(\ell),O(\ell),O(\ell^2)$, which gives the stated total bit count. Packing bounded signed digits into one integer with appropriate radices also gives a single additive equality digest. Its two sets of scores can interleave, whereas Theorem 2 requires strict ordering.

For a general fixed finite abelian group $H$, every exact common additive digest of these logs needs at least $\ell+1$ elements. Let $A_i$ be the difference between the digests assigned to first-load values one and zero at stage $i$. At any stage $i$, make a CPU log first switch from zero to one by reading $(1,0)$. Keep its future writes at one, with all other reads consistent. Compare with the legal memory log having exactly these writes. Their digest difference is $A_i$, which must be nonzero. At any later stage $j$, switch just its first load to zero and keep its second load at one. The difference becomes $A_i-A_j$, which must again be nonzero. Hence the $A_i$ are pairwise distinct and nonzero. This matches the logarithmic order of the bit upper bound for finite abelian groups.

**Theorem 4.** Over $H=\mathbb F_2^k$, the minimum $k$ for a fixed additive equality digest is exactly $\ell+1$.

Let $B_i$ be the corresponding second-load difference. In the preceding construction the CPU can drop its first load at any subset of stages following the initial switch. Therefore $A_i$ is outside the span of the later $A_j$, and $A_1,\ldots,A_{\ell-1}$ are independent. At stage zero the initial switch can use $(1,0)$, $(0,1)$, or $(1,1)$. Each of $A_0,B_0,A_0+B_0$ lies outside the span of the later first-load differences. Their first two cosets are independent in the quotient, giving $k\ge(\ell-1)+2$. For the matching upper bound take the $\ell$ bits $a_i\mathbin{\mathrm{xor}}b_i$ separately and one bit $\bigoplus_i(W_i\mathbin{\mathrm{xor}}a_i)$. Memory yields zero everywhere. A CPU log passing the first $\ell$ comparisons has $a_i=b_i=W_{i+1}$. Its last bit telescopes to $W_0\mathbin{\mathrm{xor}}W_\ell=1$. The lower bound concerns a single fixed set of queries. Responses in an adaptive sequence can change which linear map is used.

The positive result extends to a cell read $d\ge2$ times at every stage and updated to the OR of its $d$ replies $x_{ij}$. The first sum $\sum_i(dW_i-\sum_jx_{ij})$ is zero on memory. On a false CPU history it equals $\sum_i(dW_{i+1}-\sum_jx_{ij})-d$. Each heterogeneous row contributes at least one to this last nonnegative mass, and a homogeneous row contributes zero. Thus a passing CPU history has at most $d$ heterogeneous rows, and at least one. Set $s_i=\sum_{j<d-1}(x_{ij}-x_{i,d-1})$, using columns numbered from zero. This integer vanishes exactly on the homogeneous rows, and $|s_i|\le d-1$. Choose any prime $q>\max(d,\ell)$ and compare the $d$ sums $\sum_i i^h s_i$ modulo $q$ for $0\le h<d$. They vanish on memory. On the nonempty support of size at most $d$, the first as many equations have an invertible Vandermonde matrix over $\mathbb F_q$. They cannot all vanish. With a prime bounded by twice $\max(d,\ell)$ and the first sum kept as a signed integer this takes $O(d\log(d+\ell))$ bits.

## When some pairs of reads are checked jointly

Impose the additional CPU requirement $a_i=b_i$ at any chosen stages. Write $k$ for the number of stages left free. The exact distance is $2^{-k}$. To see the upper bound, take $p_0=2^{-k}$. Double $p_i$ at each free stage, using disjoint load events as before. At every tied stage keep $p_{i+1}=p_i$ and use $[U<p_i]$ for both loads. The only differing marginal is again the initial store.

For the lower bound put $d_i=2$ and $v_i=a_i+b_i$ at a free stage, and $d_i=1$, $v_i=a_i$ at a tied stage. A memory log satisfies $v_i=d_iW_i$. A CPU log satisfies $v_i\ge W_{i+1}$. Weight each $v_i-d_iW_i$ by $\prod_{j>i}d_j$ and add. The CPU score is at least $W_\ell-2^kW_0=1$ by cancellation. The memory score is zero. The coefficient bound is $2^k$, proving the formula. The same mixtures force every integer separator to have an initial-store weight difference of at least $2^k$. Enforcing all the pairwise checks in the CPU view here is cheap. These formulas give the cost specifically of leaving those pairs unchecked in this relaxation.

## Two applications and the open step

The lower bound is witnessed by the fixed-schedule memory logs alone, so it also applies if an address checker permits a larger set of memory histories. With $T=3\ell+1$ it matches the general $O(T)$-bit bound up to constants. A machine deciding SAT can run the same sequence for $\Theta(N)$ stages on a fresh cell after computing its verdict and XOR the last bit into that verdict. This preserves correctness and adds $O(N)$ RAM steps. Fix a legal input and splice the genuine solver prefix before both log distributions. The same coefficient bound holds for that wrapped program at this input. It gives no running-time lower bound on the original solver.

There is also a version at the diagonal output itself. Use a fixed literal branch of the bounded native interpreter for this sequence, and a separate branch retaining its usual universal code. The literal branch iterates on a whole word with bitwise OR. Keep loop controls in registers and stream the $n$ output bits from the last word. The native clock $B=2^{20n}$ permits $\ell=\Theta(B)$ stages after allowing enough time for setup and output. Unused event slots have identical public records in both views. This source retains its short-name pigeonhole count and eventually prints $0^n$ from its literal branch. Let $v_n$ be the first missing word of **this extended source**. It is then nonzero. In the two constructions replace each 1 by the whole word $v_n$. The truth table of OR on $\{0,v_n\}$ is exactly the bit table. The CPU outputs $v_n$ on every false history in the construction. Therefore a claim that each name at this omitted word has a strictly separating additive integer score with every coefficient of $o(B)$ expanded bits fails already on this fixed name. For this branch Theorem 3 provides a cheap per-program certificate even under arbitrary whole-word load guesses. Project every value onto any single output bit where $v_n$ has a one. Bitwise OR respects this projection, the genuine output has zero there, and the three equality checks use $O(\log B)$ common reply bits. [First-missing-output setup](native-missing-word.md)

## Checks and comparisons

The Lean file checks the first-difference arithmetic, the CPU score identity, the zero memory score, the unequal-read count identity, the two-stage moment check, realization of every integer in the score interval, and an integer-scaled marginal error recurrence. The RAM semantics and convex-hull arguments above are paper proofs. The Python audit generates all full Boolean logs through six stages and checks the exact dyadic witnesses for every subset of tied pairs. It also checks both equality digests on every such Boolean log, constructs the collisions for the normalized binary quotient calculation, and checks all 3,584 false histories of a four-stage, three-load program and all 3,840 false histories of a three-stage, four-load program. Its optional LP run independently computes all 62 subset distances through five stages. [Lean checks](FractionalRamEcho.lean) · [Exhaustive and linear-programming audit](fractional_ram_echo_audit.py)

Linear encodings of deterministic computation and local-marginal relaxations both have established precedents. The bounds here concern a particular two-view RAM-history relaxation with individually stamped events. Priority for its sharp margin and coefficient precision is unestablished. [Dobkin, Lipton and Reiss on linear programming and deterministic computation](https://collaborate.princeton.edu/en/publications/linear-programming-is-log-space-hard-for-p/) · [Feldman, Wainwright and Karger on the local relaxation for binary codes](https://doi.org/10.1109/TIT.2004.842696)
