# Critical clauses can be hard to identify from a complete rejecting execution

A clause of an unsatisfiable CNF is *critical* if deleting it makes the formula satisfiable. Such a clause belongs to every unsatisfiable subformula. Its criticality is also equivalent to sensitivity at any one of its physical literal signs. An assignment satisfying the deletion must falsify every literal of the deleted clause, so changing any one sign makes that assignment a model. Conversely a model after one sign change satisfies every other clause. A globally correct deterministic solver must therefore read the word containing each critical sign before rejecting. [Belov, Lynce and Marques-Silva on transition clauses](https://www.cs.utexas.edu/~hunt/FMCAD/fmcad11/papers/74.pdf)

This necessary read need not tell the solver whether the clause was critical. There is a packed 3-CNF family of $N=\Theta(m\log m)$ bits and a globally correct solver whose complete native execution is identical on every member at a given scale. It rejects in $O(N)$ time with a constant number of work words. Every unsatisfiable subformula contains at least $3m/2$ of the displayed units. Among another $m$ specified clauses, precisely half are critical. For any fixed deterministic decoder and all but a vanishing fraction of the family, the following holds simultaneously for all integer budgets $0\le q\le m/\log^2 m$. Even given the **whole rejecting execution** and one hindsight string of $s$ bits, a decoder making at most $q$ fresh input-word reads per clause correctly classifies fewer than $3m/4$ of these clauses whenever
$$
  (s+1)(q+1)\le c m
$$
for a sufficiently small constant $c>0$. The decoder may perform unlimited local computation. Accuracy is measured over the fixed list of $m$ questions for that one input. The advice is shared across the questions. Each query starts with fresh scratch. [Finite semantic and numerical checks](../lean/CriticalClauseTrace.lean)

## The formula and the native run

Take $m$ a power of two, $a_i,b_i$ two banks of $m$ distinct Boolean variables, and $z$ a further variable. The fixed prefix contains the $2m$ negative units on these banks, followed by a binary OR tree on all $2m$ leaves with its root required true. Each gate is encoded by its three equivalence clauses. Pad units and binary clauses to width three by repeating literals. This prefix alone is unsatisfiable. In the suffix put the unit $z$. For a permutation $\pi$ of $[m]=\{0,\ldots,m-1\}$, put one record in each physical slot $i$. For $i<m/2$ use the tautology $(z\lor\neg z\lor b_{\pi(i)})$. For $i\ge m/2$ use $(\neg z\lor\neg b_{\pi(i)})$. The tautologies give indexed access to the entire forward permutation, so the layout does not hide any part of it from the decoder. There are no duplicated clause records.

Deleting any one $\neg a_i$ lets $a_i$ satisfy the root with all other selectors zero. Every unsatisfiable core therefore contains every reserve unit. After deleting $\neg b_j$, the root forces $b_j$ true and all other selectors false. This satisfies the suffix exactly when $\pi^{-1}(j)<m/2$. The $m$ reserve and $m/2$ critical optional units must all occur in every unsatisfiable subformula. Every permutation gives the same physical size, and each of the $\binom{m}{m/2}$ possible half-size criticality sets occurs.

The solver checks the header for this length and tests the fixed prefix, then rejects on a match. On a failure it invokes any correct fallback. The test needs only loop indices and a constant number of words for constructing the next fixed clause. Align the prefix end to the word boundary, or place a fixed guard of more than one native word of tautologies before the varying suffix. A final packed read then contains no varying data. On valid inputs arbitrary added conjuncts preserve the prefix contradiction. For the language of valid satisfiable encodings, a malformed string with a matching contradictory prefix also has a negative verdict. The whole trajectory, including instruction times, controllers, public word responses, and every actual work read and write, depends only on $m$. A decoder may know this trajectory at no cost. The unread physical suffix is still available through the separately charged input-word interface. A linear-time fallback, if one exists, preserves the global linear clock.

A packed word of this fixed-stride layout overlaps a bounded number of permutation slots. Simulate a decoder read using at most $C$ forward permutation queries for a fixed $C\ge1$, with all offsets, constants, prefix bits and trace data computed for free. The following bound even permits probes at arbitrary forward indices.

More generally, keep the same prefix and let the suffix enforce a bounded Boolean verifier $V(B,p,w)$ whenever all reserve selectors are zero. A Tseitin circuit with a fresh output and an appropriate disjunction implements that condition. With no reserve deletion, deleting the optional units indexed by $D$ then has a model exactly when some nonempty set $B\subseteq D$ and witness $w$ satisfy $V(B,p,w)$. With a reserve deletion the reserve selector suffices. Thus even the entire upward-closed family of successful optional deletions can be chosen as any monotone NP predicate with a fixed succinct verifier that is false at the empty set. The rejecting solver still sees just the fixed contradiction prefix and length header. Families of fixed padded length give the same native trace. The quantitative bound below uses the shorter permutation construction.

## Guessing the critical fraction

Fix a clock $q$, a single advice string and any deterministic decoder, defaulting unanswered questions at the cap. Test it on $r$ distinct uniformly chosen targets independent of a uniform $\pi$, where
$$
 r=4\left\lfloor\frac{m}{1024(Cq+1)}\right\rfloor .
$$
Condition first on the target list. All $r$ calls together expose at most $m/256$ new forward values. Pad the adaptive sequence with fresh indices to $\lfloor m/256\rfloor$ distinct queries, giving a uniform ordered sample of images without replacement. The chance this sample reveals at least $r/4$ targets is at most
$$
 2^r(1/256)^{r/4}=2^{-r}.
$$
Indeed one particular target subset of that size is covered with probability at most $(1/256)^{r/4}$, and there are at most $2^r$ subsets.

Condition now on the complete adaptive transcript, including the padding. Every unseen target has a uniform preimage among the unqueried indices, subject to the injective choices for the other unseen targets. The predicted bits are fixed. Even after exposing up to $r$ more preimages, at most $m/2$ remaining indices have the desired half-label and at least $m-m/256-r\ge254m/256$ indices were available at each exposure. Conditional success per required bit is at most $64/127<17/32$. Unless the previous high-hit event occurred, at least $3r/4$ such bits must all agree. Since $(17/32)^3<(2/3)^4$, the chance of passing all $r$ tests is at most $2(2/3)^r$.

For a particular permutation on which this advice classifies at least $3m/4$ targets correctly, independent sampling without replacement passes all tests with probability at least $(3/4-r/m)^r\ge(8/11)^r$. Dividing yields
$$
 \Pr_\pi[\text{this advice attains accuracy at least }3/4]\le 2(11/12)^r .
$$
There are fewer than $2^{s+1}$ strings of length at most $s$. Choose $c$ small enough that $s+1\le r/32$ whenever the displayed product bound holds at large $m$ in the claimed range. Since $2(11/12)^8<1$, the summed error is $2^{-\Omega(r)}$. Throughout the range $r=\Omega(\log^2 m)$, so summing also over all integer clocks leaves a vanishing exceptional fraction. No independence between decodings using the same advice is needed.

The query bound concerns predicting counterfactual satisfiability after changing one occurrence in the original encoding. The actual machine has already correctly returned its decision without receiving this information. A scan of the suffix explicitly fills the entire criticality vector in $O(m)$ work using $O(m)$ bits plus loop registers. Even asking for the whole vector on this family would fit inside the encoded linear clock. Inversion with advice and systematic indexing have a substantial literature. The one-bit calculation here gives a direct bound for the SAT clause queries with their actual base transcript. Priority for that formulation is unverified. [Nayebi, Aaronson, Belovs and Trevisan](https://arxiv.org/abs/1408.3193) · [Golynski on the indexing model](https://uwspace.uwaterloo.ca/items/09135517-57b8-40cc-a345-4b6ce1cb396f)
