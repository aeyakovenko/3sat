# How many actual gate clauses can certify a random checksum?

Use the [balanced checksum SAT distribution](sat-on-random-checksums.md). Write \(h\in\{0,1\}^v\) for the unique full solution of its native gate-table 3-CNF \(C_j\), \(d=\lceil\log_2 v\rceil\), \(K=\mathbb F_q\) of characteristic two, and \(P_x(p)=\sum_{i<v} x_i L_i(p)\) for the multilinear interpolation of a zero-padded table. The \(L_i\) are the Boolean Lagrange basis functions. Sample \(p\in K^d,\lambda\in K\) uniformly; the mask is \(c_i=\langle\lambda,L_i(p)\rangle\) in the chosen binary basis. The terminal parity pin is independent and fair. The intended scale is \(\epsilon=(j+1)^{-A}\) and \(q\) the least power of two at least \(2^{18}(d+1)/\epsilon^2\).

* On each unsatisfiable draw, every unsatisfiable subformula contains at least \(\mathrm{wt}(c)\) original native clauses. This number exceeds \(v/4\) except with probability at most \(4/v+4d/q\).
* With probability at least
  \[
   1-\frac{2d}{q}-\frac{4(q-1)}v\left(1+\frac1{q-2}\right)^d
  \]
  over the field point, every collection of fewer than \(v/12\) original native clauses allows **all \(q\) values** of \(P_x(p)\). The clauses may be chosen after seeing the point, mask and even the true table.
* A list algorithm that takes only \(p\), returns at most \(L\) candidate symbols, and contains the true symbol on an \(\alpha\) fraction of points can be converted to an advised predictor correct on every checksum when \(\epsilon\lceil\sqrt L\rceil\le\alpha\). The conversion has polynomial-in-\(j\) overhead for inverse-polynomial \(\alpha\). Producing such lists for the genuine computation within the small time and advice budget is still open.

## Private one-bit repairs of wrong pins

On a wrong pin, start from \(h\). For every \(i\) with \(c_i=1\), change just \(h_i\) and recompute the entire checksum gadget on that modified table. This satisfies every checksum clause including the final pin. It also extends all optional header and clause-padding bits with their prescribed values. Consequently any unsatisfiable subformula must include an original native clause falsified by this modification. A clause satisfied by \(h\) can be falsified by single-coordinate flips at at most one distinct index. Indeed every true literal in it must use that coordinate. Therefore at least \(\mathrm{wt}(c)\) distinct native clauses are required. If the physical encoding pads native clauses with shared false literals, consider each retaining its original fixed padding. This only strengthens the lower bound. The private-clause observation is the classical critical-clause property in the satisfiability coding lemma. [Paturi, Pudlák and Zane](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/PaturiPudlakZane_1997_focs.pdf)

Let \(\delta=1-(1-1/q)^d\le d/q\). Distinct tables have \(\Pr_p[P_x=P_y]\le\delta\). To see this, a nonzero multiaffine polynomial is nonzero on at least \((q-1)^d\) points: induct on a variable that occurs and count at least \(q-1\) nonroots wherever its leading coefficient is nonzero. Variables absent from the polynomial multiply the count by \(q\). For \(Z=v^{-1}\sum_i(-1)^{c_i}\), averaging its square over all masks and points gives at most \(1/v+(1-1/v)\delta\). Indeed the cross term for \(i\ne l\) averages to the probability that \(L_i=L_l\). Since \(\mathrm{wt}(c)\le v/4\) entails \(Z\ge1/2\), Markov's inequality proves the first probability bound. Conditioning on the wrong pin leaves the distribution of \(p,\lambda\) unchanged. Thus a predictor always answering SAT except upon finding an unsatisfiable core with at most \(v/4\) native clauses gains at most \(2/v+2d/q\) over one half. This conclusion concerns proof via the specified clauses. A solver can use the public construction of the formula.

## Every nonzero mask on the same field point

Condition on every \(p_l\notin\{0,1\}\) and choose \(\lambda\) uniformly nonzero. Set \(r_l=p_l/(1-p_l)\). These ratios are independent and uniform on \(K^\times\setminus\{1\}\), since \(p=r/(1+r)\) in characteristic two. Then \(L_i(p)=\prod_l(1-p_l)\prod_{l:i_l=1}r_l\). For words at Hamming distance \(s\), equality of their weights is equivalent to a product of \(s\) independent draws from \(K^\times\setminus\{1\}\) being one, with some factors inverted. Inversion preserves that uniform law. Its probability \(a_s\) satisfies \(a_0=1\) and \(a_{s+1}=(1-a_s)/(q-2)\), since a previous product different from one is canceled by one allowed factor. Thus
\[
  a_s=\frac1{q-1}+\frac{q-2}{q-1}\left(-\frac1{q-2}\right)^s .
\]
For \(X_i=(-1)^{c_i}\), averaging over nonzero \(\lambda\) gives \(\mathbb E X_i=-1/(q-1)\), since all weights are nonzero. The pair product has conditional expectation one on equal weights and \(-1/(q-1)\) otherwise. Substitution gives the signed covariance
\[
   \operatorname{Cov}(X_i,X_l)
   =\frac{q(q-2)}{(q-1)^2}\left(-\frac1{q-2}\right)^{\mathrm{dist}(i,l)} .
\]
For any fixed center \(a\in\{0,1\}^v\), write \(Z_a=v^{-1}\sum_i(-1)^{a_i} X_i\). Taking absolute values and summing all cube positions gives
\[
 |\mathbb E Z_a|\le\frac1{q-1},\qquad
 \operatorname{Var}(Z_a)\le V:=\frac1v(1+1/(q-2))^d .
\]
The row sum bound works for any set of \(v\) distinct Boolean index words, including the actual truncated index interval. If \(q\ge5\), closeness \(\mathrm{dist}(c,a)\le v/4\) implies \(Z_a\ge1/2\), at least \(1/4\) above its mean. Its probability under interior \(p\) and nonzero \(\lambda\) is at most \(16V\), uniformly over centers chosen before the query. At the zero center the mean is negative, so the probability is at most \(4V\).

By the union bound over the \(q-1\) nonzero masks, outside a fraction \(4(q-1)V\) of interior points, every nonzero binary linear functional sees more than \(v/4\) nonzero bits on the table of field weights. At each such point let an arbitrary set of \(t<v/12\) base clauses be chosen. Its variables form a set of size at most \(3t<v/4\). The \(L_i(p)\) outside this set span \(K\) as a binary vector space: a proper span has a nonzero annihilating functional, supported as a mask entirely inside the mentioned positions. That contradicts the simultaneous weight bound. Flipping an arbitrary subset of these untouched bits preserves every chosen clause at \(h\). Their field increments span \(K\), giving every proposed value of \(P_x(p)\). Unconditioning costs at most \(2d/q\), by a union bound over the coordinates. The same argument applies to a collection of derived consequences if they are all implied by a *common* subcollection of fewer than \(v/12\) base clauses. Separate consequences may collectively use every original clause.

## Candidate tables and candidate symbols

Predicting the checksum of any complete candidate table \(y\) chosen independently of \(p,\lambda\) succeeds with probability exactly \((1+\Pr_p[P_y=P_h])/2\), after applying the public pin. If \(y\ne h\), the advantage is at most \(\delta/2\), with equality for a table differing in just one bit, since a single \(L_i\) vanishes exactly when one of its \(d\) factors vanishes. A random mixture over these table predictors therefore needs probability strictly above \((2\epsilon-\delta)/(1-\delta)\) of drawing the *whole true table* to exceed advantage \(\epsilon\). The same distance controls a candidate drawn from any fixed nonlinear relaxation with \(K_0\) distinct possible tables: for a common decision predictor and a uniform table in this set the average advantage is at most
\[
 \frac12\sqrt{K_0^{-1}+(1-K_0^{-1})\delta}.
\]
Indeed pairwise inner products of the signed table codewords equal their symbol collision probabilities. The squared norm of their normalized sum is bounded by the expression under the radical, and the predictor has norm at most one. One may include the public pin in that inner product. The bound concerns what can be guaranteed across the admissible tables; the actual table can have additional structure.

There is a positive conversion for **point-dependent** symbol lists. Let \(S(p)\) have at most \(L\ge1\) elements, and let \(\Pr_p[P_h(p)\in S(p)]\ge\alpha\). Use the real score \(g_p(z)=[z\in S(p)]/\lceil\sqrt L\rceil\). Its squared row norm is at most one and its average true score is at least \(\alpha/\lceil\sqrt L\rceil\). Put \(\kappa=\alpha/(2\lceil\sqrt L\rceil)\). The [quadratic-curve soft decoder](recovering-tables-from-field-values.md#beating-a-random-field-symbol-guess-on-fixed-scalar-queries) needs \(q\ge2^{16}(d+1)/\kappa^2\), which the specified field size supplies under \(\epsilon\lceil\sqrt L\rceil\le\alpha\). Its proof uses the row norm, bounded score, and mean true score (here at least \(2\kappa\)). It works at every target \(x\in K^d\). With \(O(d\log q)\) independent advised anchor tuples, the per-target majority error is below \(q^{-d}\), so one fixed advice list works simultaneously at all \(q^d\) targets. This recovers the true field symbol at every point and hence the terminal decision on every query. Advice and work cost only \(\operatorname{poly}_A(j)\) times the time and advice budget of the list algorithm plus one, for fixed inverse-polynomial \(\alpha\). Each trial initially samples its positions without reference to the table and takes the true anchor labels as advice. Selecting one fixed successful collection of trials may depend on the table. The lists may depend on the full queried point, and the list procedure may have stage advice of its own. This conversion uses no SAT solver. The original conditional checksum theorem then applies to the resulting exact predictor if its budget is small enough.

[Lean check of disjoint critical clauses and the product recurrence](../lean/LocalChecksumClauses.lean) · [Finite field, clause and list audit](../audits/local_checksum_clauses_audit.py)
