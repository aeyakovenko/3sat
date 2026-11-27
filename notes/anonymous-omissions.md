# Extracting one hard omission from anonymous shifted labels

**Research journal, 24 November 2026.** Can an aggregate verifier provide information about a single missing output even when it never identifies which input its claim concerns? A family of shifted versions of the actual native source gives a sufficient condition with an exact square-root baseline. Taking the union of *all* the genuine holes fails the test, even with perfect knowledge of the full cutoff. [Native first omission](native-missing-word.md)

## A test that allows wrong answers and abstentions

Let $D=2d$, $U=2^D$, $B=U^{20}$, and let $v$ be the actual first $D$-bit output absent by $B$ among all native names shorter than $D$. Write $G=\mathbb F_2^d\times\mathbb F_2^d$ and $b(x)=(-1)^{x_L\cdot x_R}$. For each public salt $s$ in $S=\{s:b(s)=1\}$, relabel each valid output $y$ as $y+s$ and order outputs by their **original** lexicographic rank. This is a relabeling of the bounded run's result, with the original cutoff, so the first omission in that order is $v+s$. Forget all salt identities. The union of these first omissions is $v+S$, whose signed indicator is exactly $b(x+v)$. The hidden-shift construction for this bent function is classical. The use here is a deterministic ranking argument on actual omissions. [Rötteler](https://arxiv.org/abs/0811.3208)

Give a uniform reporter the anonymous label $x$, with no request for an individual salt. It can answer positive, negative or abstain. For example use two uniformly constructible existential Boolean circuits at $x$, and let $H(x)$ be their Boolean verdicts subtracted in the order positive minus negative. Both passing or both failing gives zero. Let $K=\sum_x H(x)^2$ count nonabstentions. The excess of correct over wrong answers on the true anonymous set is

$$
  L_v=\sum_x H(x)b(x+v).
$$

Under the SAT clocks below, at every sufficiently large even $D$,

$$
    |L_v|\le C\sqrt K. \tag{1}
$$

To prove this, the $U$ translated sign vectors are mutually orthogonal. For different shifts their product is a nonconstant linear character times a fixed sign, and summing that character gives zero. Every row has squared norm $U$. Hence $\sum_w L_w^2=UK$. Sorting by decreasing $|L_w|$ gives the actual $v$ one-based rank at most $UK/L_v^2$ whenever $L_v\ne0$. A fixed decoder calculating this ranking by the native cutoff forces the rank to exceed a fixed positive fraction of $U$. Its tag and the raw rank minus one would otherwise be shorter than $D$. This proves (1), including the trivial $K=0$ case.

If each reporter circuit has size and uniform construction time $V\operatorname{poly}(D)$, explicit Tseitin SAT queries have length $V\operatorname{poly}(D)$ for $V\le B$. Under cubic SAT, $U$ labels cost $U V^3\operatorname{poly}(D)$ and direct formation of all correlations costs $U^2\operatorname{poly}(D)$. Thus any fixed $\epsilon>0$ permits $V\le U^{19/3-\epsilon}$. Under linear SAT one can take $V\le B/D^a$ for sufficiently large fixed $a$: guess the entire reporter table, universally select a row to check against its deterministic SAT verdicts, and use the guessed table to compute any requested output bit at the supplied rank. All correct tables coincide. The computation uses fixed quantifier depth and $(V+U^2)\operatorname{poly}(D)$ total time including native overhead. [Batched table verification](linear-sat-batches.md) · [Fixed-block elimination](linear-quantifiers.md)

A reporter attaining $|L_v|/\sqrt K\to\infty$ along a subsequence would exclude the corresponding ordinary SAT bound. For $K=U$ the required excess fraction can be as small as $\omega(U^{-1/2})$. The scale in (1) is attained *for every actual shift* on sparse reports as well. Report positive on the subspace where only the first $k$ positions in each half may be nonzero, and abstain elsewhere. There are $K=4^k$ claims. On that subspace the translated quadratic sign is the inner-product sign times a linear character and a constant. Summing first over the left coordinates kills every right vector but one, giving $|L_v|=2^k=\sqrt K$ independently of $v$. This includes $k=d$, when the reporter always says positive.

## Why even exact hole data lose the signal under a union

Let $A$ consist of **all** genuine native omissions at $B$, with $h=|A|$. In the specified native grammar, a fixed aborting program has at least $2^{D-c}$ distinct names of length $D-1$ for a fixed $c$, by filling its ignored raw payload. Those names produce no $D$-bit word, so $h=\Omega(U)$. The natural replacement for the canonical union is $A+S$. For each label $x$ let $m(x)$ be its number of representations $x=y+s$ with $y\in A,s\in S$. Exactly

$$
  2m(x)= h+\sum_{y\in A} b(x+y), \qquad
  \mathbb E_x (2m(x)-h)^2=h.
$$

The second identity follows from the same orthogonality. At an uncovered label $m(x)=0$, so there are at most $U/h=O(1)$ uncovered labels. Every uncovered label satisfies $b(x+v)=-1$ because $v\in A$. The always-positive report has $L_v=\sqrt U$, by the subspace calculation. Changing its sign on the uncovered labels gives the exact score of the full-hole union,

$$
  L_v=\sqrt U+2|G\setminus(A+S)|=\sqrt U+O(1).
$$

Randomly discarding salts before the union also fails in expectation. Keep each salt with probability $p$, independently. The expected signed report at $x$ is $H_p(x)=1-2(1-p)^{m(x)}$. From the second-moment identity, $\Pr[m<h/4]\le4/h$ and $\mathbb E|m-h/2|\le\sqrt h/2$. For integers $k\ge\lfloor h/4\rfloor$, the one-step change in $1-2(1-p)^k$ is $2p(1-p)^k\le 2/(k+1)=O(1/h)$ uniformly in $p$. This follows by summing the first $k+1$ terms of the geometric series. The expected absolute difference between $H_p(x)$ and its value at $\lfloor h/2\rfloor$ is consequently $O(h^{-1/2})$. Its normalized correlation with $b(x+v)$ is at most $U^{-1/2}+O(h^{-1/2})=O(U^{-1/2})$ in absolute value. This statement controls the mean report over the thinning, and does not preclude a selected individual mask with better correlation.

Two ranges also bound the expected **absolute** surplus. When $pU=O(1)$, first allow Bernoulli retention on all of $G$. The law of the union is translation-invariant, so every shift has the same expected squared correlation, exactly $U$ by the Gram identity and the fact that the union's sign report never abstains. Conditioning on retaining nothing outside $S$ has probability $(1-p)^{U-|S|}=\Omega(1)$ and gives the desired law. Cauchy–Schwarz yields $\mathbb E|L_v|=O(\sqrt U)$. At the other extreme, if $pU\ge C_0\log U$ for sufficiently large fixed $C_0$, the expected number uncovered is at most $4U/h+Ue^{-ph/4}=O(\sqrt U)$, by the lower-tail estimate. Its absolute surplus is at most $\sqrt U$ plus twice the realized number uncovered. The mean signed result covers the intermediate range. The absolute-surplus estimate here does not.

The remaining construction is a short verifier with excess over the sharp bound for the **first-omission** set. The aggregate test permits many mistakes and never demands a producing salt. The calculations on the actual full-hole set rule out reporting existence of any shifted omission, including its independently thinned average, as a source of that excess.

Lean checks the translated sign sum and orthogonality in every dimension by summing one digit pair at a time. An exhaustive four-bit check verified the uncovered-set inequality and exact surplus for all 65,535 nonempty hole sets. The clock and randomized-union bounds are manuscript arguments. [Lean proof](../lean/AnonymousOmissions.lean)
