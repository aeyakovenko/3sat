# A product lower bound for polynomial replacement of public randomness

**Research journal, 24 November 2026.** The [public-tape argument](random-tape-decision-witnesses.md) spends roughly the advice length times the query time to replace a genuinely random tape by a polynomial evaluation table. Can a simpler choice of degree reduce this to their sum? There is a family of efficient tests on which this polynomial sampler needs at least a constant times the product in **seed bits**, even for advice chosen after seeing the tape and perfect acceptance on almost all uniform tapes.

Use the field $F=\mathbb F_{2^s}$. Take a binary additive subspace $U$ of size $q$, and $t$ distinct cosets $a_j+U$, where $4\mid t$ and $qt\le2^s$. For an oracle $R:F\to F$, test $j$ can sum the $q$ words on its coset. Independent uniform tape words give $t$ independent uniform sums. The same statement need not hold for a polynomial tape of large degree.

Put $L(X)=\prod_{u\in U}(X-u)$. Translation by elements of $U$ preserves $L$; the values $L(a_j)$ are distinct because the degree-$q$ polynomial $L(X)-L(a_j)$ already has all elements of $a_j+U$ as roots. Every polynomial $P$ of degree less than $h$ has a unique expression
$$
 P(X)=\sum_{i=0}^{q-1} X^i f_i(L(X)).
$$
Indeed the polynomials $X^i L(X)^j$ are monic of distinct degrees $i+qj$ covering all nonnegative integers. The sum of the $i$th powers of the points on each coset vanishes for $0\le i<q-1$ and is the same nonzero constant for $i=q-1$. To see this, $L'$ is translation-invariant of degree less than $q$, so $L'$ is constant by evaluation on $U$. At zero its value is $c=\prod_{0\ne u\in U}(-u)\ne0$. The logarithmic derivative of $L(X)-L(a_j)$ is both $c/(L(X)-L(a_j))$ and $\sum_{y\in a_j+U}1/(X-y)$. Compare powers of $X^{-1}$ at infinity. The first nonzero coefficient occurs at $X^{-q}$ and equals $c$. Thus the coset sums of $P$ are exactly $c f_{q-1}(L(a_j))$. Conversely, $X^{q-1}f(L(X))/c$ realizes each permitted low-degree $f$. The image of the coset-sum map is precisely a Reed–Solomon evaluation code of dimension
$$
 \min\big(t,\lfloor h/q\rfloor\big).
$$
The finite experiment computes these spans independently for every binary subspace of $\mathbb F_{16}$. [Coset-sum audit](../audits/polynomial_tape_sums.py)

Now take the code $C$ of evaluations at the $t$ points of polynomials of degree less than $t/4$. The advice is a vector $z\in F^t$, of $b=st$ bits. The test first requires Hamming distance from $z$ to $C$ greater than $t/4$. It then chooses a uniform $j$ and checks that the tape's $j$th coset sum equals $z_j$. For a uniform tape choose its true sum vector as advice. The fraction of such tapes whose advice fails the distance test is at most
$$
 |F|^{t/4}\,2^t |F|^{t/4}/|F|^t =2^t |F|^{-t/2}.
$$
Every other uniform tape admits advice making **all** checks pass. For every polynomial replacement with $h\le qt/4$, its sum vector lies in $C$. Each legitimate advice differs on more than $t/4$ coordinates, so no advice makes even $3/4$ of the checks pass. A degree-less-than-$h$ sampler written as $h$ field coefficients therefore needs more than $bq/4$ seed bits to reach this threshold. Other families of replacement oracles may behave differently.

The distance test has polynomial cost in $t,s$. Put $e=k=t/4$. Solve for a monic polynomial $E$ of degree $e$ and a polynomial $B$ of degree at most $e+k-1$ satisfying $B(L(a_j))=E(L(a_j))z_j$ at every point. If there is a nearby codeword $f$, an error-locator polynomial padded to degree $e$ supplies a solution. Conversely, in this case every solution satisfies $B=Ef$, since the difference vanishes at at least $t-e$ distinct points and has degree at most $e+k-1<t-e$. Divide and verify all distances, treating absence of any solution as absence of a nearby codeword. The points can for example be obtained from a binary basis for a subspace using the recurrence $L_{U+\langle u\rangle}(X)=L_U(X)(L_U(X)-L_U(u))$, starting at $L_{\{0\}}(X)=X$. Inductively these polynomials are additive, so their values can be computed with polynomially many bit operations in $s$. With $q$ a sufficiently large fixed power of $t$ and $s=O(\log t)$, the ordinary checking work fits $q\operatorname{poly}(s)$, including the $q$ tape probes. This is an obstruction to a particular randomness replacement in a single sampled test. It does not give a time lower bound for explicit SAT or for different proof verifiers.
