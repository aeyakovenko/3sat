# Replaying the unique witness of a path formula

**Research journal, 24 November 2026.** Consider a proposed simulation that guesses a short description of a satisfying assignment and reconstructs a requested variable by a few random accesses to the original formula. Even a fixed uniform family of 2-CNFs of primal pathwidth one can require nearly linear description length for polylogarithmic replay. The underlying prefix-parity indexing bound is known. An exact calculation for batched linear observations gives a way to test the same proposal when the original data are correlated. [Gál and Miltersen, *The Cell Probe Complexity of Succinct Data Structures*](https://www.brics.dk/RS/03/44/index.html) · [Garg et al., *Systematic Data Structure Lower Bounds via the Query-With-Sketch Model*, §2](https://doi.org/10.4230/LIPIcs.CCC.2026.41)

## Exact success probability for a common description

Let the source be a uniform vector $x$ in $\mathbb F_2^N$. The desired joint output is $Ax$ for a fixed binary matrix. Each allowed probe returns the evaluations on $x$ of a publicly specified list of linear forms, so it can model a single bit or a word. A batch decoder receives an arbitrary $r$-bit description chosen using the entire $x$. It can adaptively make at most $P$ probes, use arbitrary temporary storage and compute without charge. The budget holds for every realized computation. Write $W$ for the row space of $A$ and set

$$
\kappa_P=\dim W-\max_{J:\,|J|\le P}\dim(W\cap V_J),
$$

where $V_J$ is spanned by all forms returned by probes in $J$. The maximum joint success probability, over all descriptions and decoders, equals

$$
2^{-\max(0,\kappa_P-r)}.
$$

Fix one description and a deterministic decoder. Truncate it at $P$ probes even on inputs for which that description would never be chosen. Each nonempty leaf is an affine coset of the common kernel of its probed forms. Conditional on reaching it, $Ax$ is uniform on a coset of dimension $\dim W-\dim(W\cap V_J)$, by rank-nullity. A single output at the leaf is correct with probability at most $2^{-\kappa_P}$. Sum over leaves and take the union over at most $2^r$ descriptions. Fixing random coins before the argument gives the same upper bound for random decoders.

For attainment, take a maximizing fixed $J$. The probe results supply $W\cap V_J$. Extend a basis of this intersection to one for $W$. Store up to $r$ of the $\kappa_P$ new basis evaluations and set all remaining ones to zero. The missing evaluations are independent uniform bits even conditional on all probes and stored bits, since the added forms are independent modulo $V_J$. Randomly guessing those bits instead attains the displayed probability separately on every input. For an affine source $x=Gz+b$ with uniform $z$, the same calculation uses target rows $AG$ and probe rows multiplied by $G$. Public offsets cost nothing. This last substitution matters when a proposed checkpoint has many cells but few independent source bits.

## A unique 2-SAT witness

For $i=1,\ldots,N$ encode $v_i=v_{i-1}\mathbin{\oplus}x_i$ by two binary clauses on the adjacent variables. Use the implications in both directions for equality and flip the sign of $v_i$ in both clauses for inequality. Pin $v_0$ to zero. The primal graph is one path, and the unique satisfying assignment has $v_i=x_1\oplus\cdots\oplus x_i$. Appending the unit clause $(v_i)$ makes SAT of that variant give the same observable bit.

Take $B=\lfloor N/L\rfloor$ and ask for the witness values at positions $L,2L,\ldots,BL$. Differences of consecutive answers, with the pinned initial bit, give all $B$ disjoint block parities. For scalar probes to the bits of $x$, the intersection of this output row space with the span of probed coordinates has dimension exactly the number of completely probed blocks. Consequently the optimum probability of correctly recovering all these witness values with a shared description is

$$
2^{-\max(0,\,B-\min(B,\lfloor P/L\rfloor)-r)}.
$$

In particular, $r+\lfloor P/L\rfloor\ge B$ is both necessary and sufficient for certain recovery. Prestore the parities of $r$ blocks and read all bits of the remaining blocks to attain the boundary when $r\le B$. This construction charges the total cost of the whole batch.

Use binary literal indices of the same $\Theta(\log N)$ length, for example by numbering the variables in the upper half of an identifier range. The signs carry the source data and all other bits of the encoding are fixed. Each ordinary $\Theta(\log n)$-bit input word spans at most a constant $c$ link records, where the encoded length is $n=\Theta(N\log N)$. The returned bits can therefore be simulated by at most $c$ probes to the raw coordinates, including when the word is unaligned. If a common description recovers each requested witness bit in $p$ word probes, running it on all $B$ endpoints gives $P\le cpB$. With $L=\max(1,2cp)$ for integer $c,p$, the necessary condition gives $r\ge B/2$. This yields

$$
(r+1)(p+1)=\Omega(N)=\Omega(n/\log n).
$$

For $L>N$ the inequality follows already from $p=\Omega(N)$, and $p=0$ gives $r\ge N$. For any fixed $a\ge0$, $O((\log n)^a)$ word probes per variable force $\Omega(n/(\log n)^{a+1})$ worst-case description bits. Descriptions may be picked separately for every formula. If a different evaluator is picked for each formula, count its description as part of $r$. The explicit probability calculation also bounds the fraction of formulas with any successful $r$-bit description.

## One actual checkpoint with every stored bit used

Pin $v_N$ to one. The decision now equals the parity of the entire path. Consider the following uniform decider on this template. During its input scan, write $y_i=v_i$ for $1\le i<N$. Maintain the running XOR of those written values as well as the current path value. For the last cell write

$$
y_N=v_N\mathbin{\oplus}\bigoplus_{i<N}y_i.
$$

Clear the two running registers. The suffix evaluates the XOR of all $N$ saved cells and returns it as the decision. The transformation $x\mapsto y$ is triangular with diagonal one, hence all $2^N$ memory vectors at this checkpoint occur on genuine inputs. Flipping any one cell of any such state leads to another reachable memory vector and switches the suffix's verdict. The program can check the template during a fixed-position scan and reset its auxiliary registers at the cut. All processing takes $O(n)$ deterministic RAM time. If a general linear-time SAT solver exists, a linear-time solver for all formulas can use this routine on recognized templates and the general solver on all others.

Recovering the actual cells of this one implementation includes all prefix queries on the first $N-1$ links. Fixing the final source bit and applying the preceding proof gives the same product bound on description length and replay probes, simultaneously for every proposed probe budget. Even if verification only requires a compressed checkpoint on each *accepting* input, passing to the half-space $\bigoplus_i x_i=1$ increases the preceding distributional success upper bound by at most a factor of two. The routine uses all its saved bits in reaching the decision, yet one running parity would suffice for a different implementation of this template. A proof based on a carefully selected canonical solver, checks of a global memory relation, or a structurally restricted set of machine-generated inputs could therefore escape this bound.

**Finite check.** For three source bits, I enumerated all 64 two-row target matrices and four probe dictionaries with scalar forms encoded as nonzero binary masks, namely the empty set, $\{1,2,4\}$, $\{3,5,6\}$ and $\{1,3,5,7\}$. For probe and description budgets zero through two, I enumerated successful input subsets of every adaptive tree, retaining only inclusion-maximal subsets, then maximized their union over the available descriptions. All 2,304 optimal input fractions matched the rank formula. Run `python3 path_replay_experiment.py` to reproduce the comparison. The proof above covers arbitrary dimensions. Earlier help-bit results treat the related model with separate decision trees for each parity. [Nisan, Rudich and Saks, *Products and Help Bits in Decision Trees*](https://doi.org/10.1137/S0097539795282444) · [Finite replay experiment](../audits/path_replay_experiment.py)
