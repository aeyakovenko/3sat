# Quadratic and cubic SAT clocks in the full-cube argument

**Research journal, 24 November 2026.** Let $A_q$ be the $q$-bit words missed by every plain program of length at most $q-2$ by the original deadline $T(q)=2^q(q+2)^{\lceil\log_2(q+2)\rceil}$. Suppose ordinary explicit SAT on $n$ encoded bits has a deterministic unrestricted-space logarithmic-word RAM algorithm of time $O(n^c)$ for $c=2$ or $3$. There are constants $\epsilon,\kappa>0$ such that, on every sufficiently large length $q$, each bounded-fan-in Boolean circuit of at most
$$
\kappa\,2^{q/(1+2c^2)}/q
$$
gates disagrees with $1_{A_q}$ on at least $\epsilon 2^q$ words. The denominators in the exponent are $9$ for quadratic SAT and $19$ for cubic SAT. The deadline defining $A_q$ stays fixed. This weakens the circuit size in the linear-SAT conclusion while retaining constant-fraction error. [The fixed language and plain-name convention](full-cube-advice.md)

## Reuse one suffix table in every prefix block

Let $b=\lfloor q/(1+2c^2)\rfloor$ and $M=2^b$. A table lists $K=2^{b-a}$ members of the $b$-cube, for a fixed positive integer $a$ chosen for the compiler header below. For a small positive constant $\eta$, consider all descriptions of length at most $\eta M$ of Boolean circuits on $b$ inputs over a fixed basis. Fix a rational density threshold $\theta>0$. Call a $K$-set qualifying if every such circuit of suffix acceptance density at least $\theta$ accepts more than $\theta K/2$ of its entries. A uniform $K$-subset misses this quota on any one dense set with probability at most $\exp(-c_0\theta K)$, for an absolute $c_0>0$. Choose $\eta$ sufficiently small relative to $a$ and $\theta$. A union bound over at most $2^{\eta M+1}$ descriptions proves the existence of a single qualifying table. The sampling bound and the common-table counting step have already been checked for finite sets. [Product moment](../lean/BatchHitPotential.lean) · [Selection](../lean/FullCubeSelection.lean)

For every prefix $p$ of length $q-b$, concatenate $p$ with every member of the **same** qualifying suffix table. A $q$-input circuit of at most $\kappa M/q$ gates restricts at each prefix to a circuit on the $b$ suffix bits whose encoding fits $\eta M$ bits, after choosing $\kappa$ sufficiently small. Hardwire the fixed prefix pins and renumber the remaining inputs; each gate and its ports use $O(q)$ encoded bits. If the original circuit accepts a fraction at least $\delta$ of the $q$-cube and $\theta=\delta/2$, at least a $\delta/2$ fraction of prefixes have suffix acceptance density at least $\theta$. Otherwise the global density is below $\delta$. The circuit thus accepts at least $(\delta^2/8)2^{q-a}$ words of the concatenated set. The transfer from the global density to the number of high-density prefix blocks, and the summation of their hits, have been formalized with integer counts. [Lean verification](../lean/SuffixBlockExponents.lean)

## Two SAT simulations and an explicit call count

For a supplied $M$-bit table $H$ and one circuit description $z$, the following check takes $W=M^2\mathrm{poly}(q)$ time. Verify the syntax, then evaluate the circuit on all $M$ suffixes, scanning the original and restricted acceptance counts and comparing against the quotas. Reject malformed purported counterexamples. The existence of a valid circuit violating the quota of a given $H$ is an existential computation of time $W$. A quasilinear RAM-to-SAT reduction and the hypothesized SAT algorithm decide it or its complement in $W^c\mathrm{poly}(q)$ time. This deterministic check also verifies the cardinality of $H$. The inner scan runs $M$ circuit evaluations explicitly and incurs no alternation for choosing a suffix address.

Given a partial binary prefix of a proposed table, guess its $M$-bit completion and invoke that deterministic qualification check. Compiling this existential computation and applying SAT once more gives deterministic completion decision time $W^{c^2}\mathrm{poly}(q)$. Starting with an empty prefix, extend by zero if some qualifying completion starts with that extension, and otherwise by one. A qualifying completion always remains. After exactly $M$ such tests one has the entire lexicographically least qualifying table. In particular every decoder recomputes the same set. This uses an extra factor $M$ in time and avoids a third elimination for the minimum. [Standard RAM transcript size and uniformity](linear-quantifiers.md)

The running time is
$$
M\,W^{c^2}\mathrm{poly}(q)
\ \le\ 2^{(1+2c^2)b}\mathrm{poly}(q)
\ \le\ 2^q\mathrm{poly}(q).
$$
The fixed SAT program and fixed table construction give a fixed polynomial exponent, independent of $q$. The interpreter's polylogarithmic slowdown at this clock is another polynomial in $q$. All these costs fit $T(q)$ for sufficiently large $q$.

Use a fixed native algorithm whose raw payload has length $q-a$. It reconstructs $q$ from the length, keeps the first $q-b$ bits as the prefix, and uses the remaining $b-a$ bits as the ordinal of a suffix among the table's $K$ ones. It prints the concatenation and halts. The compiler constants need not determine the previously required choice of $\eta$. For example put $a$ in a self-delimiting header, and let the routine derive $\eta=2^{-a-h}$ with another fixed constant $h$ large enough for the quota and union bound. The header then costs a fixed constant plus $O(\log(a+2))$, and choosing $a$ large enough pays for the header and two bits of compression. All concatenated words are outside $A_q$.

Finally, $|A_q|>2^{q-1}$ by plain-name counting. A circuit accepting less than a quarter of the cube makes errors on more than a quarter of the cube. For a denser circuit the preceding argument with $\delta=1/4$ counts a fixed positive fraction of false positives. Taking $\epsilon$ below those two constants proves the assertion.

## The remaining contradiction

A circuit family of size $o(2^{q/19}/q)$ approximating $A_q$ to within $o(2^q)$ errors on infinitely many lengths would now contradict even cubic SAT. Unconditionally simulating every short program through the defining deadline costs $2^{2q+O((\log q)^2)}$ steps; putting those executions into circuits does not approach the approximation size above. A generic circuit synthesized from the full truth table can use order $2^q/q$ gates. Neither construction supplies the needed approximation.

At fixed $a$ the sample size on a block is a constant fraction of $M$. Replacing the independent sample with one generated from a short public seed does not alone make it fool every suffix circuit. For example, if the generated subset has a membership circuit within the allowed description length, its complement is itself an eligible dense circuit and has zero hits. The original full-dimensional least-table query with three or more eliminations would repeatedly raise a size-$2^q$ input to the power $c$, already exceeding the fixed deadline. These observations leave room for other methods of describing a common sample. I have not established optimality of the exponents or priority for this block tradeoff.

## A failed attempt to select the table by a short isolating score

If a public integer score of polynomial range had one unique minimizing qualifying table, binary search for its minimum and an existential bit test at that minimum would use only $\mathrm{poly}(q)$ completion tests per printed word. This would remove the factor $M$. I tested whether the overwhelming fraction of qualifying tables alone guarantees that one of polynomially many predetermined scores isolates such a minimum.

There is a finite obstruction. Let $X$ be all $K$-sets and give any $J$ public scores, each taking at most $V$ values. Start with the whole family. Whenever a score has a fiber consisting of exactly one remaining table, delete that table. Charge the deletion to that score-value pair. Its fiber becomes empty permanently, so at most $JV$ tables are removed. At termination every nonempty fiber of every score has at least two tables. If $|X|>JV$, the family still has density at least $1-JV/|X|$ and **no** score has a unique minimum on it. With constant $K/M$ and polynomial $J,V$, the excluded density is exponentially small in $M$. Giving each prefix of an output program its own score from this list does not change the argument. Additional facts about how the bad tables arise from small circuits would be needed for this approach. The obstruction concerns deductions from density alone.
