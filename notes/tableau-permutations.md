# Certifying a tableau by local permutations with defects

**Research journal, 24 November 2026.** A description need not return the cell of a particular accepting computation on request. It can provide a set of possible states at each cell and permutations that move states one step right or down. There is a sound test for this representation even when exponentially many pairs of coordinates and states violate a local rule. Under linear-time SAT the test costs nearly the time required to examine one local neighborhood. I do not know whether the required descriptions exist for the hierarchy verifier.

Use the fixed unary $H\in\mathsf{NTIME}(n^{12})\setminus\mathsf{NTIME}(n^{23/2})$ and its ordinary computation tableau of side $D=O(n^{12})$. A fixed list of local tests together enforces all transitions, tape operations, initialization and acceptance. Anchor each stencil at its northwest bounding-box corner, so every cell read is a constant number of right or down steps from the anchor. Allow the boundary tests appropriate to the domain. [Tableau and machine conventions](mixed-tableau-patches.md) · [Nondeterministic time hierarchy, Theorem 2.1](https://www.cs.cmu.edu/~ryanw/improved-algs-lbs2.pdf)

## An exact gluing condition and its error tolerance

At every site $v$ use states $z\in\{0,1\}^g$. A supplied description gives the symbol $O_v(z)$ and the right and down edge maps $R_v,B_v$. Require each existing edge map to be a permutation. At a square with northwest corner $v$, one possible failure at $z$ is

$$
B_{v+\mathrm{right}}(R_v(z))\ne R_{v+\mathrm{down}}(B_v(z)).
$$

At a tableau-test anchor and state $z$, obtain its finitely many symbols by a prescribed monotone path to each stencil position and test the constraint. A failure of this test is another event. Different local test types have distinct identifiers. Let $K=2^g$. If the total number of failing pairs $(e,z)$ over all tests and squares is less than $K$, the original tableau has an accepting filling.

To prove this, choose a uniform state at the top left. Define the state at each site by traveling down the left column and then right along its row. Each resulting state is uniform since the edge maps are permutations. The expected number of failures seen at these canonical states is the total pair count divided by $K$. Some root sees no failures. The right edges and leftmost down edges agree with the canonical states by construction. Induct across each row. If its down edge agrees at column $j$, the commuting equation at its canonical state there forces agreement at column $j+1$. Thus all edges agree on this one assignment. Every stencil now sees exactly the symbols it checked, proving acceptance.

The strict threshold can be attained by an inconsistent local computation. A bit must remain unchanged for $K$ transitions, starting at zero and ending at one. Use identity transports and at time $t$ output one precisely if the state, read as an integer in $[0,K)$, is below $t$. Each transition has one failing state, and both endpoint tests hold for every state. In the other direction, when the total count is below $\varepsilon K$, a fraction at least $1-\varepsilon$ of roots give entire valid fillings. For a unique tableau this implies that a uniform individual state at every site gives its correct symbol with probability at least $1-\varepsilon$.

<details>
<summary>Lean 4.19 verification of the row induction</summary>

The following statement checks the gluing step on every finite rectangular grid. Its commuting hypothesis is required only at the states actually reached. The probability and running-time arguments are manuscript proofs.

```lean
import Std

namespace TableauTransport

theorem allVertical {State : Type} (x : Nat → Nat → State)
    (right down : Nat → Nat → State → State)
    (width height : Nat)
    (first : ∀ r, r < height → x (r+1) 0 = down r 0 (x r 0))
    (across : ∀ r c, r ≤ height → c < width → x r (c+1) = right r c (x r c))
    (flat : ∀ r c, r < height → c < width →
      down r (c+1) (right r c (x r c)) = right (r+1) c (down r c (x r c))) :
    ∀ r c, r < height → c ≤ width → x (r+1) c = down r c (x r c) := by
  intro r c hr hc
  induction c with
  | zero => exact first r hr
  | succ c prev =>
    have c_lt : c < width := by omega
    have r_upper : r ≤ height := by omega
    have succ_upper : r + 1 ≤ height := by omega
    rw [across (r+1) c succ_upper c_lt, prev (by omega), across r c r_upper c_lt]
    exact (flat r c hr c_lt).symm

end TableauTransport
```

</details>

## Dependencies on independent registers

The root state can instead be a sequence of independent uniform binary registers. Require each edge permutation to act separately on the registers, with its fixed coordinate map known from its site. In particular the value of register $i$ at any canonical site is a permutation of the **same** root register $i$, independent of all other root registers. Split a square failure into one failure per unequal register. For each possible defect event $e$ supply a set $I_e$ of registers such that whether the event fails at a local state depends only on those registers. Empty events may be discarded. Define

$$
p=\max_e\Pr_z[\text{event }e\text{ fails}],\qquad
d=\max_e\left|\{e\}\cup\{f:\ f\text{ is nonempty and }I_e\cap I_f\ne\varnothing\}\right|
$$

over nonempty events. A defect-free description passes directly. Otherwise $4pd\le1$ suffices for a globally accepting tableau. Each event pulled back to the random root depends only on the root registers in $I_e$ and has its original probability. All events outside its listed neighborhood, taken jointly, depend on disjoint registers from it. The symmetric Lovász local lemma gives a root with no failures, and the row induction gives a genuine accepting history. The total expected number of defects can exceed one by an unbounded factor. For example, arbitrarily many unary tests on disjoint uniform registers, each failing only on its all-zero value, have $d=1$. With twelve bits per register their expected number of failures grows as the number of tests divided by 4,096. [Lovász local lemma in the independent-variable model](https://arxiv.org/abs/0903.0544)

The local description may be much easier to evaluate than a long composition of its edge maps. For instance a machine can first guess one bit and then toggle it at times $t$ satisfying a circuit $F(t)$. Model its evolving bit by a register with time transport $z\mapsto z\oplus F(t)$ and trivial horizontal transport. Reading the final bit for the trajectory with initial guess zero computes the parity of the truth table of $F$. The local descriptions only evaluate $F$ once per time step examined. This example imposes acceptance on both final values and supplies no accepting-tableau description for $H$.

## Checking the hypotheses without following long paths

Suppose a fixed representation has total description length, state length and local evaluation cost bounded by $S$. Include the time to evaluate the full state after each of the constantly many moves used in a stencil, the time to report a symbol, and the construction of the input and indices. Register lengths can, for example, be uniform with a shorter last register. Their total is $g\le S$. An event has a canonical identifier of $O(\log(D+g+2))$ bits. The representation gives a membership test for $i\in I_e$ within the local clock. Choose a common constructible cap for all these bounds and reject on malformed descriptions or timeouts.

Assume an unrestricted deterministic linear-time SAT solver on encoded bits. Injectivity of every supplied map can be checked by searching for a collision at one chosen edge. Register independence can be checked by searching for two states equal on a selected input register and unequal on that output register. For a proposed event support, search for two states giving different failure bits but agreeing on every register in $I_e$. A universal register index checks this last agreement while charging for one support test per branch. These are fixed-block predicates of local branch time. [Uniform elimination using explicit SAT](linear-quantifiers.md)

For any primary-string count $C>0$ of a fixed bounded-quantifier relation the journal's projected approximate count returns an exponent $j$ with $2^j/4\le C\le8\cdot2^j$. Zero is detected exactly. Set $U(C)=8\cdot2^j$ for a positive count and $U(0)=0$. Then $C\le U(C)\le32C$. A count and its power-of-two upper estimate can be compared by their exponents. Under linear SAT this takes quasilinear time in the primary-string length plus the fixed-quantifier branch clock. [Counting algorithm and assumptions](near-native-counting.md)

For the total-error test, count the pairs $(e,z)$ directly and accept the description when the upper estimate is below $K$. A count of at most $K/64$ always passes. For the dependency test let $C_e$ count the local states failing event $e$. Let $D_f$ count the distinct nonempty event identifiers in the displayed neighborhood of $f$, including $f$ itself when nonempty. For another event, nonemptiness and support overlap have existential witnesses. Count its identifier once independently of the number of witnesses. Universally check all pairs of nonempty event identifiers $e,f$ and require

$$
4U(C_e)U(D_f)\le 2^g .
$$

Every passing description satisfies $4pd\le1$. Every description satisfying $4096pd\le1$ passes. The two separate identifiers allow the maxima of probability and degree to occur at different events. The numbers of quantifier blocks and approximate-counting levels are fixed. Thus these tests take $(S+n+\log D)\,\mathrm{polylog}(S+n+D)$ deterministic RAM time for a given description. They require neither a list of all active events nor a sampler computing the canonical state at a remote site. The local lemma is used only to prove that accepting the description is sound.

Consequently linear SAT would be impossible if, for every sufficiently large accepted $1^n$, one of these two representations had $S\le n^{23/2-\eta}$ for a fixed $\eta>0$, with either the $K/64$ total bound or the $4096pd\le1$ dependency bound. Nondeterministically guess the representation, choose the appropriate test, and verify it. The polylogarithmic simulation of that RAM recognizer on multitape machines preserves a fixed exponent gap, contradicting the defining lower bound for $H$. Finitely many small exceptions may be hardwired. The missing assertion concerns the actual machine's accepting computations. Small local state alphabets by themselves do not supply the permutations and support certificates.
