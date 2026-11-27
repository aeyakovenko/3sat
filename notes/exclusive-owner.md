# When global coverage identifies one producer

**Research journal, 24 November 2026.** Write $M=2^n$ and $B=M^{20}$. The native first missing output $v$ has no genuine producer. A model in which nearly every label has exactly one predicted producer can nevertheless predict $v$. If the model samples different groups of names independently, this prediction has to come from one identifiable group. Under linear SAT, the conclusion survives near-$B$ private randomness *per group*, rare local conditioning, and an unknown shared advice value. Pairwise independence alone gives a different answer. [Native source](native-missing-word.md) · [Near-native projected counting](near-native-counting.md)

## A concentration inequality for one output

Fix a label and let $X_i$ be its multiplicity in group $i$. There are finitely many groups, with arbitrary internal dependencies and independence across groups. Write $q=\Pr[\sum_i X_i\ne1]$ and

$$
\Gamma=1-\max_i\Pr[X_i=1\text{ and all other counts are zero}].
$$

Always $q\le\Gamma\le2q$. If $q<1/2$, then $\Gamma\le q+q^2$. In this regime a single group $i$ has both $\Pr[X_i=1]\ge1-q$ and $\Pr[\sum_{j\ne i} X_j=0]\ge1-q$.

Indeed, the indicators $[X_i>0]$ are independent Bernoulli trials. If every success probability is at most $1/2$, the probability of exactly one success is at most $1/2$. To see this, let $z,o$ be the current zero- and one-success probabilities. Adding a trial of probability $p\le1/2$ gives $(1-2p)o+p(o+z)\le1/2$ whenever $o\le1/2$. Start with no trials. Since exactly one total occurrence entails exactly one positive group, the case $s=1-q>1/2$ has some group $i$ with $\Pr[X_i>0]>1/2$.

Set $a=\Pr[X_i=1]$, $b=\Pr[X_i=0]<1/2$, and let $z,y$ be the zero- and one-count probabilities for all other groups combined. Then $s=az+by\le\max(a,b)$, hence $a\ge s$. If $z\le1/2$ then $s\le az+(1-a)(1-z)\le1/2$, so $z>1/2$ and $s\le(a+b)z\le z$. The probability of a singleton supplied by someone else is $by\le(1-a)(1-z)\le q^2$. For $q\ge1/2$, $\Gamma\le1$ suffices. Lean verifies the one-success bound using integer masses, including deterministic trials. An exhaustive check verified the inequalities for all 3,875 unordered collections of one to four laws on $\{0,1,2\}$ with probabilities in quarters. [Lean](../lean/ExclusiveOwner.lean) · [Experiment](../audits/exclusive_owner_experiment.py) · [Hoeffding on independent unequal Bernoulli trials](https://repository.lib.ncsu.edu/bitstream/1840.4/2268/1/ISMS_1955_128.pdf)

## Obtaining the individual score from separate short checks

First fix the common advice. For a group and label $x$, put $a_i=\Pr[X_i=1]$ and $t_i=\Pr[X_i>0]$. Use the score

$$
g_x=\min_i\min\!\left(1,\ (1-a_i)+\sum_{j\ne i} t_j\right).
$$

Then $\Gamma_x\le g_x\le3\Gamma_x$. For a chosen $i$ the union bound gives the first inequality before minimizing. For the other direction let $\lambda=\sum_{j\ne i}t_j$. The chance of some competing group is $1-\prod_{j\ne i}(1-t_j)\ge(1-e^{-1})\min(1,\lambda)$. The chance that this group fails to be the exclusive owner is at least that probability and at least $1-a_i$. Their bounds give the factor $1+1/(1-e^{-1})<3$. In particular $\sum_x g_x\le6D$ where $D=\sum_x q_x$ is the expected total number of labels whose multiplicity differs from one.

Each group may sample a different primary string of at most $H$ bits, uniformly conditioned on its own nonempty live set. Assume the live-set, zero-count, and one-count tests have a fixed number of quantifier blocks and uniform branch time $T$, including effective string lengths. Include no more than $M$ groups. Compute dyadic constant-factor estimates of $1-a_i$ and $t_i$ by counting the actual complementary or positive events, with zero tested exactly. Guess the array of short exponents and verify a universally chosen entry against the counting procedure. Sums can be computed within a fixed relative error using $O(n)$ mantissa bits: align to the largest summand and discard terms more than $n+2$ exponents below it, whose total is at most one quarter of that largest term. Zeros remain exact. Each candidate $i$ can sum its competitors directly. Minimizing and truncating to one preserve constant-factor accuracy. The resulting estimate for $g_x$ can be rounded to zero or $2^{-k}$ with $0\le k\le H+O(1)$, since any positive input probability is at least $2^{-H}$. This uses $(H+T+M^2)\operatorname{poly}(n)$ time under linear SAT. It never needs one combined string of $MH$ random bits. [Projected-counting routine](near-native-counting.md) · [Batched table check](linear-sat-batches.md)

## Common advice and the actual missing word

Now condition the groups on common advice $A$. Draw $A$ uniformly from a nonempty live subset of a bounded tape, followed by independent local group tapes with the advice-dependent live sets above. Let $D=\sum_x\mathbb E_A q_x(A)$ and $G_x=\mathbb E_A g_x(A)$. To tabulate $G_x$ up to a constant multiplicative factor, introduce an independent auxiliary tape of $H+O(1)$ bits. When the conditional estimate is $2^{-k}$ accept if its first $k$ bits are zero, and always reject for a zero estimate. Conditional acceptance probability is exactly the estimated dyadic value. Apply projected counting again with liveness determined only by the common advice. This preserves the specified advice weights even when the primary group denominators vary arbitrarily with advice or group.

Under linear SAT take $H,T$ and the common tape length at most $B/n^c$ for a sufficiently large fixed $c$, with the overhead exponents independent of that choice or the final clock checked directly. The fixed number of nested computations, the output table, rank decoding and native interpretation still fit $B$. Since $\sum_xG_x\le6D$, ranking by the dyadic estimates of $G_x$ gives

$$
\mathbb E_A g_v(A)\le O(D/M).
$$

Indeed the rank of a positive score is at most a constant times its total mass divided by that score. A rank smaller than $M$ by an arbitrarily growing factor would print the omitted $v$ within the cutoff. For advice $a$ of mass $\rho$, this implies $g_v(a)\le O(D/(M\rho))$. When the bound is below one, **one particular group at that advice produces exactly one copy of $v$ with failure probability at most that bound, and the sum of all competing groups' hit probabilities is equally small**. In singleton groups this identifies one name. No such name really produces $v$. With $h$ bits of uniform advice the loss is $2^h$. The loss from averaging is unavoidable in general: let each advice value deterministically omit a different label, so a label's failure score can be one on its own advice and zero elsewhere.

A direct sufficient condition for ruling out linear SAT follows. On a set of live advice of mass $\rho$, suppose every group fails to supply exactly one $v$ with probability at least $\eta$. Then necessarily $\rho\eta\le O(D/M)$. Proving the opposite asymptotic inequality on infinitely many lengths would exclude linear SAT. Equivalently, a calibration proof can require that a group reporting a label above a specified confidence threshold has a genuine producer. Given such a semantic calibration, a group index and the near-native confidence test identify a certified individual label. With an explicit gap, the deterministic counting verdict under linear SAT has a quasilinear checked transcript compilable into an ordinary SAT instance. These results establish the forced individual prediction; a calibration theorem for real interpreter outputs is still needed. They make no cubic-SAT clock claim.

A concrete model supplies the calibration on the actual source. Give each name $p$ a nonempty list $C_p$ containing its true bounded outcome, counting timeout or wrong length as one nonlabel, or containing its true value in the injective semantic completion. Independently sample **uniformly among distinct listed outcomes**. No actual name emits $v$. If $v\in C_p$, another element of the same list is the true outcome, hence the predicted probability of $v$ is at most $1/2$. Therefore $D=\Omega(M)$ for every such family under linear SAT, assuming the stated uniform near-native recognition clocks. Uniformity is over primary outcomes, so the number of alternative proofs of membership cannot bias a list entry. Constructing lists satisfying actual containment with $D=o(M)$ would refute linear SAT directly. More generally a group with at most $L$ uniformly sampled distinct possible tuples, one being the true tuple, fails to supply exactly one $v$ with probability at least $1/L$. For live advice of mass $\rho$ satisfying this guarantee in every group, the necessary bound is $D=\Omega(M\rho/L)$. [Completion preserving the true first omission](semantic-completion.md) · [Earlier independent-list obstruction](matching-holes.md)

For lists on an injective completion with no nonlabels, this implies a numerical overlap bound, $\sum_{p<j}|C_p\cap C_j|/(|C_p||C_j|)=\Omega(M)$. The sum is the expected number of unordered equal-output pairs. In each sampled table the number of anomalies is at most one plus twice its number of such pairs, by counting the surplus occurrences in occupied columns. For cheaply tabulated uniform lists this conclusion can alternatively be recovered from the earlier set of possible matching holes: each possible hole has no singleton list pointing to it, and hence has anomaly probability at least one half. The concentration and conditional-advice estimates also apply to unequally weighted predictions.

## How much independence matters

For pairwise independent singleton row hits, write $p_i=\Pr[X_i=1]$, $\lambda=\sum_i p_i$, $m=\sum_i X_i$, and $K_x=\mathbb E[m(m-1)]$. Then $K_x=\lambda^2-\sum_i p_i^2$. Since $\lambda\ge1-q_x$ and $\max_i p_i\ge\sum_i p_i^2/\lambda$ when $\lambda>0$,

$$
1-\max_i p_i\le 2q_x+2K_x.
$$

For $q_x<1/2$ substitute $\lambda\ge1-q_x$ into $1-\lambda+K_x/\lambda$; otherwise the claim follows from the bound one. Thus under the same clocks one can rank the minimum individual miss probability even for pairwise independence, now charging $D+\sum_x K_x$ instead of $D$. The expected miss probability for the best name at $v$ is at most $O((D+\sum_xK_x)/M)$, taking conditional minima before averaging if there is shared advice. If multiplicity is always capped at $L$, then $K_x\le L(L-1)q_x$. The quadratic dependence on $L$ is necessary in a per-label estimate: for $L\ge3$ let $p=1/(L-1)$, give the all-ones pattern probability $p^2$ and each of the $L$ singleton patterns probability $p-p^2$. This is a probability law with pairwise independent indicators, maximal hit probability $p$ and anomaly probability $p^2$.

For a joint table counterexample use the nonzero elements $u$ of $\mathbb F_M$ as names, $M\ge4$. Choose uniform $(a,b)\in\mathbb F_M^2$ and output $au+b$. Every pair of rows is independent uniform. For $a\ne0$ the unique missing label is $b$. For $a=0$ every label is anomalous. Thus $D=2-1/M$, every candidate $v$ is omitted on a compatible seed, and every named row hits $v$ with probability only $1/M$. The expected number of ordered colliding pairs here is $(M-1)(M-2)/M$, precisely the term the pairwise estimate charges. If one conditions on $a\ne0$, then $D=1$ and each two-row distribution has total variation exactly $1/M$ from a pair of independent uniforms. Neither exact pairwise independence nor approximate pairwise independence with universal injectivity substitutes for independence across the groups in the first conclusion.
