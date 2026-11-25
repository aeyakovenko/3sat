# Exact worst-case ambiguity on unique 3-SAT with distinct clauses

Consider a uniquely satisfiable proper 3-CNF $F$ with $m$ clauses. Each clause has three distinct variable names, and no two clauses are equal as **unordered signed triples**. Enable every literal occurrence. Among all positive, separate-row certificate systems correct on every setting of the enable bits, the minimum number of witnesses on this all-enabled input is $P(F)=\prod_C\tau_C$, where $\tau_C$ is the number of true literals of clause $C$ under the unique model. With the additional requirement that counts agree modulo $p$ with the zero-one decision bit on every mask, the minimum is $1+p(H(F)-1)/2$, where $H(F)=\prod_C(2^{\tau_C}-1)$. Hidden variables may be shared across all clauses. [Occurrence masks and the optimal counts](shared-witnesses-for-masked-literal-occurrences.md)

The following formulas maximize these minima over $F$, for every $m\ge16$. Let $v_0$ be the smallest integer satisfying $\binom{v_0}{3}+v_0\ge m$ and put
$$
 \ell=m-\left(\binom{v_0-1}{3}+v_0-1\right).
$$

| Condition | Number $v$ of variables in an extremizer | Number $b$ of two-true clauses |
|---|---:|---:|
| $\ell=1$ or $\ell=2$ | $v_0-1$ | $\ell$ |
| $\ell\ge3$ | $v_0$ | $0$ |

Then the exact maximum ordinary minimum is $2^b3^{m-v-b}$. The exact maximum modulo-two minimum is $H_{\max}=3^b7^{m-v-b}$. For any prime $p$ the maximum with the normalized modulo-$p$ requirement is $1+p(H_{\max}-1)/2$. The **same** formula attains all these maxima. In particular
$$
 \log_3 P_{\max}=m-(6m)^{1/3}+O(1),\qquad
 \log_7 H_{\max}=m-(6m)^{1/3}+O(1).
$$
Priority for this extremal calculation has not been established.

## Two elementary constraints force the maximum

Rename and negate variables so that the unique model is all ones. Let $n_i$ count the clauses containing exactly $i$ true literals. Each occurring variable must be the sole true literal in some clause. Otherwise flipping only that variable would keep the entire formula satisfied. The designated clauses for different variables differ, giving $n_1\ge v$. In an all-true clause, the three literals are determined by the unordered triple of names, so $n_3\le\binom v3$.

Both objectives have the form $B^{n_3}D^{n_2}$, with $(B,D)=(3,2)$ or $(7,3)$. For fixed $v$, at most $m-v$ clauses have more than one true literal. Filling as many of those as possible with three-true clauses gives the upper bound
$$
 G(v)=B^{m-v}(D/B)^{\max(0,m-v-\binom v3)} .
$$
When $3\le v<v_0$, $G(v)=B^{\binom v3}D^{m-v-\binom v3}$. Between consecutive integers both in this range its ratio is $(B/D)^{\binom v2}/D>1$. On $v\ge v_0$ the bound decreases by a factor of $B$ per extra variable. The only candidates are therefore $v_0-1$ and $v_0$. Their ratio is $G(v_0-1)/G(v_0)=B(D/B)^\ell$. For either objective this exceeds one for $\ell=1,2$ and is less than one for $\ell\ge3$. Finally $v_0=(6m)^{1/3}+O(1)$.

## A five-variable forcing construction

On the first five variables include all ten positive triples and the five clauses
$$
      (x_i\lor\neg x_{i+1}\lor\neg x_{i+2})
        \qquad (i\in\mathbb Z/5\mathbb Z).
$$
Three or more zeros violate a positive triple. One zero violates its own displayed clause. Two zeros could satisfy both of their displayed clauses only if each is among the next two cyclic positions of the other. In a five-cycle these two conditions cannot both hold. Thus the anchors are all true. For each additional variable use $(x_i\lor\neg x_1\lor\neg x_2)$, forcing it true as well. Exactly $v$ clauses have one true literal.

In the $v_0$ case choose $m-v$ positive triples including the ten anchor triples. The definition of $v_0$ provides enough available triples. For $m\ge16$ there is room for the ten anchors: $v_0\ge6$ and $m-v_0\ge\binom{v_0-1}{3}$. In the $v_0-1$ case use all positive triples and add $\ell$ distinct clauses with two positive literals, chosen from $(x_1,x_2,\neg x_3)$ and $(x_1,\neg x_2,x_3)$. Here $v\ge5$. Every added clause holds on the forced all-true assignment. All clauses remain pairwise distinct and proper. The resulting counts are $n_1=v$, $n_2=b$, $n_3=m-v-b$.

## Negative enable tests needed for isolation

If some enables may be tested in either polarity, let $h_1(F)$ and $h_2(F)$ be the fewest distinct such enables sufficient for at most one or two accepting witnesses, respectively, on **every** mask. On a fixed unique formula,
$$
 h_1(F)=\sum_C(\tau_C-1)=2m-2n_1-n_2,\qquad
 h_2(F)=\max(0,h_1(F)-1).
$$
Indeed, in clause $C$, leave at most one live enable unsigned to ensure isolation. For ambiguity two, one clause may retain two unsigned choices. The product formula for the residual ambiguity gives the converse: the product of positive integers $r_C$ is at least $1+\sum_C(r_C-1)$. [Signed-enable tradeoff for a fixed source](shared-witnesses-for-masked-literal-occurrences.md)

For $m\ge16$ the maximum $h_1(F)$ is $2m-2v-b$ with the $v,b$ from the table, and the maximum $h_2(F)$ is one less. At fixed variable count $v$ the upper bound for $h_1$ is $2(m-v)-\max(0,m-v-\binom v3)$. It increases through the saturated regime and decreases thereafter. Its value at $v_0-1$ minus its value at $v_0$ is $2-\ell$. Thus the smaller variable count wins when $\ell=1$, and the two upper bounds tie when $\ell=2$. The table's chosen construction realizes the maximum in every case.

In fact the same extremizer works for **every budget $h$ of signed positions**. Write $c=m-v-b$. With $h\le b$ the maximum over source formulas of the best attainable worst-mask ambiguity is $2^{b-h}3^c$. For $h=b+2j<b+2c$ it is $3^{c-j}$, and for $h=b+2j+1<b+2c$ it is $2\cdot3^{c-j-1}$. At $h\ge b+2c$ it is one. For a single profile, spend first on two-choice clauses and then in pairs on three-choice clauses. This order is optimal: reducing a two to one divides the product by two at once, while taking a three to one costs two positions. Two untouched threes are better reduced to one and three than to two and two.

To compare profiles across all $h$, one may replace a sublist by another whose optimal ambiguity is at least as large at every budget. Adding the remaining clauses preserves this relation, since the combined optimum minimizes the product over budget splits. At fixed $v$, upgrading coordinates to use all available three-choice slots and using two-choice slots up to $m-v$ dominates every feasible profile. Along the saturated regime, increasing $v$ trades $\Delta+1$ twos for $\Delta$ threes and a one, where $\Delta=\binom v2$. For $\Delta=2$ the old optimal products at budgets zero through four are $8,4,2,1,1$; the new ones are $9,6,3,2,1$. For larger $\Delta$ additionally upgrade each extra two to a three. Along the unsaturated regime an extra variable only downgrades a three to a one. At the boundary, increasing the variable count trades $\ell$ twos for $\ell-1$ threes and a one. For $\ell\ge3$ the same dominance applies. For $\ell=1$ a two beats a one; for $\ell=2$ two twos have profile $4,2,1$ compared with $3,2,1$ for a three and a one. This proves simultaneous extremality for all budgets.

The constructions use $\Theta(m\log m)$ ASCII DIMACS bits with dense numbering. Indeed, in *any* file of $m$ distinct proper clauses only $O(m^{3/4})$ can use exclusively identifiers of numerical value at most $m^{1/4}$. Each remaining clause pays $\Omega(\log m)$ digits for at least one identifier. If repeated clauses are allowed, even one fixed uniquely satisfiable three-variable block plus repeated copies of its all-true clause gives forced counts exponential in the physical source length. The separate enable variables still require distinct identifiers when printed as an ordinary target CNF.

The audit checks all assignments to constructed formulas for $15\le m\le100$, including the five-variable core, and directly compares both upper envelopes over all possible variable counts for $16\le m\le500$. It also checks the signed-budget envelope for every $h$ through $2m$ at $16\le m\le100$. The proof above applies to all $m\ge16$. [Reproduce the finite checks](extremal_ambiguity_unique_3sat_audit.py)
