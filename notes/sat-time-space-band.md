# A logarithmic time–space band for explicit SAT

**Research journal, 24 November 2026.** Write $L(n)=\max(2,\lceil\log_2(n+2)\rceil)$. On the packed word RAM and explicit binary CNF encoding specified below, for each fixed nonnegative integer $a$, no deterministic SAT algorithm has both worst-case bounds
$$
 O(n L(n)^a)\quad\text{time},\qquad O(n/L(n)^{2a+8})\quad\text{auxiliary bits}.
$$
This first derivation excludes **linear time and $O(n/\log^8 n)$ bits simultaneously**. A second reduction improves 8 to **7** and $2a+8$ to **$2a+7$** on the same model. [Final input-cost improvement](materialized-input-census.md) The same conclusion holds with 9 in place of 8. For a fixed conventional model or encoding admitting the standard polylogarithmic transfers without the specific costs below, the proved statement has $2a+C$ in place of $2a+8$, for some fixed $C$. These are unconditional restrictions on algorithms. The proof uses complementary-time diagonalization and classical checkpoint simulations. Priority for the numerical accounting is unverified. [Fortnow, Lipton, van Melkebeek and Viglas, §§2–5](https://lance.fortnow.com/papers/files/tst.pdf) · [Williams on inductive time–space bounds](https://people.csail.mit.edu/rrw/sat-journal-final.pdf)

### The machine and the two transfers

Time counts word instructions, $n$ counts **formula bits**, and workspace charges the word width for each distinct auxiliary word touched. The original input is read-only. Workspace also includes registers. A word has $\Theta(\log(n+2))$ bits with a fixed machine constant. The concrete basis has ordinary register operations, indirect loads/stores, comparisons, Boolean operations, shifts, addition and subtraction, and permits multiplication and integer quotient/remainder. Division by zero has fixed semantics. Use a binary 3-CNF list with a header, three fixed-width binary variable indices per clause, and three signs. Repeated literals allow padding shorter clauses. A general explicit SAT solver on an encoding admitting these records must solve this subfamily. For an encoding requiring a separate conversion one must account for that conversion. The numerical argument also works when the physical input interface reads individual bits instead of packed words, by generating the requested bit.

In the proof we use nondeterministic word machines allowed to guess a whole word. A public input to an auxiliary bounded computation has $m$ **words**, and its time allowance is $h$ word steps. Write $H=\max(h,m,2)$ and $L=L(H)$. Auxiliary word widths are $\Theta(\log H)$ with fixed constants. A time-bounded nondeterministic computation has a virtual, explicit 3-CNF with $O(H L^3)$ **bits**. After a polylogarithmic setup, the value of any single packed word of this formula is available in $O(1)$ word operations and polylogarithmic scratch space. The next note gives the record fields, certificate routing network, local addressing and diagonal model. Local access matters because writing down the formula in workspace would erase the band. [Packed trace reduction and diagonalization](packed-band-transfer.md)

Assume both solver bounds, but temporarily write $b$ for the space exponent. Running the solver on the virtual formula gives the following simulation of **every** bounded nondeterministic computation:
$$
 T=O(HL^A)\ \text{word steps},\qquad
 S=O(H/L^B)\ \text{words per configuration},\qquad
 A=a+3,\quad B=b-2.
$$
The formula length contributes three logarithms. Dividing the SAT workspace in bits by its word width returns one logarithm. A sparse snapshot of an occupied memory word consists of its address and its value, each a word up to a fixed width factor. Control, word-width metadata, temporary input generation, and the ordinary padding of halted configurations add at most polynomially many bits in $L$, absorbed in $S$. Here and below the $S$ formula is used with fixed positive $B$. Constants in bounds can be built into the simulators.

There is a separate route that does not require the concrete packed compiler. In the random-access bit-machine model of FLMV, their Theorem 3.1 has a fixed exponent $r$ for the local SAT reduction. A conventional fixed word instruction set with uniformly bit-polynomial operations can be simulated there with $L^u$ time overhead. For sparse high addresses use a compact balanced dictionary of address/value pairs: operations take polylogarithmic time, and each entry and its pointers take a constant number of guest words. If another model transfer uses an $L^v$ factor for space, include it explicitly. Padding to the source clock is virtual, with length, zero ranges and original input positions locally accessible; absorb any extra fixed address-generation logarithms into $u$ or $r$. Thus one can take $A=a+u+2r$, $B=b-v-r$ after enlarging those fixed constants as necessary. FLMV Theorem 2.1 supplies the complementary-time separation on their model. In that route all subsequent checkpoint costs measure bits. Neither theorem in that citation specifies $r$ numerically. [FLMV, Theorems 2.1, 3.1 and 3.4](https://lance.fortnow.com/papers/files/tst.pdf)

### Improving the simulation time

Let $H(e)$ assert that any bounded nondeterministic computation has a conondeterministic simulation in
$$
 O(HL^e + mL^A)
$$
on $m$ public input units. The unit is a word for the packed proof or a bit for the FLMV proof. Complementing a language interchanges the two signs of simulation. The assumed deterministic simulation gives $H(A)$. We invoke an improvement only with $0\le e\le A$. All machines, nesting depths and powers below are fixed independently of the input length.

Build the deterministic simulation with bounds $T,S$ above. Give a universal stage $P=\lceil L^x\rceil$ checkpoint intervals, with endpoints fixed or checked for validity; use accepting and rejecting halts that stutter. Acceptance is equivalent to the assertion that **every** candidate list ending in rejection has an erroneous segment. An authentic rejecting run supplies the converse. Malformed lists also pass the error test. The inner nondeterministic machine guesses the segment index, checks its two endpoints and replays the segment. Its time is $R=O(T/P+S+\operatorname{poly}(L))$. Its public input size is $m'=O(m+PS+\operatorname{poly}(L))$. A selected pair can be addressed directly. A malformed endpoint or local format is a defect, so a global initial scan is unnecessary. The outer guess itself costs $O(PS)$. [Checkpoint equivalence and exponent proof in Lean](../lean/BandTimeSpace.lean)

Use $H(e)$ to replace the inner nondeterminism by conondeterminism, merging it with the leading universal stage. Since $e\le A$, applying the bound at $\max(R,m',2)$ costs $O(R L^e+m'L^A)$, even when the public input is longer than the replay time. The logs are comparable: the budgets are within fixed log powers of $H$, and the replay clock is at least $H/L^{O(1)}$ by construction. This gives the improved exponent
$$
 e'=\max\{A-x+e,\ x-B+A\}.
$$
The extra term indexed by $S L^e$ is smaller for the choices used below. The original public input still costs $mL^A$. Taking $x=(B+e)/2$ gives $e'=(2A+e-B)/2$. For $B>2A$, the fixed point $2A-B$ is negative. A fixed finite number of iterations, starting at $e=A$, makes $e'<0$. Small fixed rational slacks suffice for all strict inequalities; ceilings in the checkpoint counts cost constant factors. In particular this already covers $b=2a+9$ for the concrete model.

### Reaching the endpoint $B=2A$

At this endpoint two applications give $H(A/2)$ then $H(A/4)$. Use the latter at **two nested levels** in one final simulation. Write $e=A/4$, $P_1=\lceil L^{11A/12}\rceil$ and $P_2=\lceil L^{2A/3}\rceil$. The overall time is at most a constant times
$$
 (T/(P_1P_2))L^{2e}
 +P_1 S L^A + P_2 S L^{A+e}
 +(m+S)L^{A+e}.
$$
To see where the second list is charged, first construct the appropriate one-level segment verifier on $m+O(S)$ public data and deterministic time $O(T/P_1)$. It can have either initial sign, by determinism of the segment relation and complementation. Guessing the outer defective index and running the existential version of this verifier is one nondeterministic computation on $m+O(P_1S)$ public units. Apply $H(e)$ once more, now with that longer input. This multiplies the inner replay work by $L^e$ and charges the entire outer input at $L^A$. Copying only the selected pair into the inner verification prevents the outer list from being charged as its input a second time. Copying the original input if necessary is covered by the displayed $m$ term. [FLMV's nested input accounting, proof of Lemma 5.3](https://lance.fortnow.com/papers/files/tst.pdf)

The first three terms each have exponent $-A/12$ relative to $H$. The residual $SL^{A+e}$ has exponent $-3A/4$. Choose the initial hierarchy clock $h=n_0^2$ on inputs of length $n_0$ bits, so $m=O(n_0)$ and $mL^{A+e}=o(h)$. We would simulate the diagonal nondeterministic computation in conondeterministic time $o(h)$. That contradicts complementary-time diagonalization. This proves the claimed endpoint. The input term would have spoiled this argument at $h=n_0$.

The simulations can use a binary public clock: each reduction treats the clock and widths as parameters, fixes all array lengths before guessing data, and checks the claimed endpoints at those lengths. Every recursive invocation is on a fixed verifier of bounded runs with a supplied upper clock. The lengths of the bounded computations are polynomially related at this fixed depth. Computing ceilings for the rational powers of $L$ takes polynomial time in $L$ (integer powers and roots suffice). The elementary lower-order overheads fit even the final shaved clock. The final improvement below uses a different public-input cost only in the stage that can materialize its SAT instance. [Last-stage reduction](materialized-input-census.md)

### What the bound says about actual runs

Fix **any** correct deterministic solver in the concrete model. The statement applies also to the strengthened exponent $2a+7$ after the last-stage improvement. On satisfiable formulas, for any pair of constants multiplying the two claimed bounds, there are arbitrarily long inputs exceeding at least one bound. This holds separately on unsatisfiable formulas. Otherwise, simulate the solver with both caps and return the opposite verdict on overflow. This is correct if every input of the chosen sign respects the caps. The time counter is constant per step. For the distinct-words space convention keep a seen bit in a parallel sparse bank for each guest word touched and stop on the first excess. This costs a constant factor in time and auxiliary bits; a larger fixed word-width constant or a second bank supplies the tag. Finite exceptional lengths can be hardwired. This would produce the prohibited simultaneous solver. In particular, if a linear-time solver exists, **on each sign** its workspace divided by $n/L(n)^7$ is unbounded using the last-stage improvement.

A linear-time word RAM can touch $O(n)$ words, using $O(n\log n)$ bits. This accounts for the proposed $b=-1$ endpoint at $a=0$. The band proof does not reach that endpoint. Its resource improvement occurs when an actual checkpoint fits the specified word count. A configuration of order the whole time budget supplies none of the required saving.

The Lean checks cover the finite cost inequalities, iteration, and the indicated semantic checkpoint and abstract hierarchy steps as documented in the source. The circuit layout, model transfer and universal-machine simulation are given as mathematical proofs. A full formalization of the RAM and reduction is still outstanding.
