# Can packing the pins make the epoch counts superlinear?

The present family uses $p=2m$ independent data bits and $N=\Theta(p\log p)$ encoded bits. Removing the spacing between private sign sites could save native input reads. It cannot improve the asymptotic bit length for **any** fixed-layout ordinary width-three encoding of this verdict in which the input changes only literal signs, one selected data bit per variable sign occurrence. Several signs in the same clause may depend on different data bits and a given data bit may occur many times. The argument below imposes no read order and does not require private signs to occupy separate native words.

More generally, let $f$ on $p$ bits have positive density $\mu>0$. Assume every subcube on which $f=1$ fixes at least $c$ input bits. Suppose
$$
        f(x)=1\quad\Longleftrightarrow\quad\exists z\in\{0,1\}^v:\quad
        \bigwedge_{j=1}^M T_j(x,z)=1,
$$
where, for each fixed $z$, each test $T_j$ depends on at most $k\ge1$ bits of $x$. Then
$$
 v\ \ge\ \log_2\mu+
       \lceil c/k\rceil\log_2\big(1/(1-2^{-k})\big).
$$
No bound on the number of tests or on their dependence on $z$ is needed. This is a bound on witness length under fixed input locality of each conjunct, including nonuniform templates.

Fix a witness $z$. Under a current partial assignment, stop successfully if every test is identically one on the residual subcube. Otherwise choose one test still capable of failing and reveal its remaining input bits, at most $k$. A constant false test immediately rejects. Conditional on the exact previously revealed bits, the probability of passing the chosen test is at most $1-2^{-k}$, since at least one setting fails. Whenever a path stops successfully, its revealed bits certify $f=1$. Therefore it passed at least $\lceil c/k\rceil$ tests. By induction on rounds the measure of paths passing that many tests is at most $(1-2^{-k})^{\lceil c/k\rceil}$. This bounds the acceptance probability with this $z$. Summing over all $2^v$ witnesses proves the inequality.

For ordinary width-three clauses, fixing the assignment to all named SAT variables makes each clause a test on at most three data bits. The explicit complement quadratic has $\mu=1/2+o(1)$ and $c\ge p-9$. Consequently the number of distinct *occurring* SAT variables must be $\Omega(p)$, regardless of how many sign bits a native word reveals. Writing even one distinct binary name for each of $v$ occurring variables costs $\Omega(v\log v)$ bits, since only $O(2^l)$ distinct binary names can have length at most $l$. Hence $N=\Omega(p\log p)$ in the explicit indexed encoding. The existing construction matches this order. [Verdict density and certificate property](expander-cut-signs.md)

At each dyadic scale of a partition of $p$ pin discoveries, a count that credits at most the number of discoveries in each interval totals at most $p$. Even if every credited operation could be shown distinct **across** scales, these credits would sum to at most $O(p\log p)=O(N)$ for this entire class of encodings. Thus a time exclusion needs additional charged operations, different scales with an appropriate disjointness proof, or a different encoding or verdict property. This is a specific obstruction to an attempted lower-bound proof. It gives no upper time bound for arbitrary SAT. [Distinct sources at a single scale](birth-epoch-reuse.md) · [Sparse source changes](sparse-epoch-changes.md) · [Lean survival count](../lean/LocalTestCertificateMass.lean) · [Finite coverage check](../audits/certificate_width_encoding_audit.py)
