# Testing degree-two Boolean representatives of the permanent on prescribed matching entries

**Research journal, 24 November 2026.** Let $P$ have individual degree at most two, agree on the Boolean cube with the permanent of an $M$-by-$M$ matrix, and have a division-free arithmetic circuit of size at most $M^D$ for fixed $D$. Work over a fixed field $F$ of characteristic different from two. For an entry $v$ write the formal polynomial as $A_v+B_vX_v+C_vX_v^2$, with coefficients in the other variables. There exists a set of $\exp(O_{D,F}((\log M)^{3/4}))$ rows and columns such that **outside them the two coefficient polynomials $B_v,C_v$ are linearly independent over $F$ at every entry**. In particular all but $M^{1+o(1)}$ entries must have this property. This is a necessary condition on a hypothetical small circuit. A single small polynomial vanishing on the cube can generate the same coefficient independence, as shown below.

The numerical exponents throughout use the formal permanent lower bound $k^{c(\log k)^{1/3}}$ from the November 2026 preprint. The matrix restriction and the circuit extractions below are explicit deductions from that bound. [VP–VNP preprint, Theorem 1.1](https://hexagonmath.org/2611.00954v1)

## Put the free entries on any prescribed matching

Given $M\ge2k^2+k$, prescribe any $k^2$ entries sharing neither a row nor a column, and label them by $e=(i,j)\in[k]^2$. Write the prescribed row and column as $r_e,c_e$. Take new row vertices $L_i,u_e$ and new column vertices $R_j,v_e$. Include a length-five path
$$
 L_i\;-\;v_e\;-\;r_e\;-\;c_e\;-\;u_e\;-\;R_j .
$$
Give its middle edge the free weight $X_e$, and its other edges weight one. Fix an arbitrary perfect matching between leftover rows and columns, of weight one, and set all other entries to zero.

In any perfect matching, if $L_i v_e$ is chosen, the next edges alternate, forcing $r_ec_e$ and $u_eR_j$. Otherwise $v_e r_e$ and $c_eu_e$ are forced and neither endpoint edge is used. Each $L_i$ and $R_j$ therefore selects one common used path, and every permutation on $[k]$ gives precisely one full matching with the associated weight. The restricted formal permanent equals $\operatorname{perm}_k$. The corresponding restriction $R$ of $P$ agrees with it on the cube and costs at most the original circuit size up to constant gates. Row and column names and the edge labels on the prescribed matching can be arbitrary. [Lean verification of the local path modes, matching constraints and unique completion](../lean/MatchingCoordinatePermanent.lean)

## A test in a basis chosen separately at every entry

Choose any normalized quadratic $p_v(X)=a_vX+b_vX^2$ with $a_v+b_v=1$ for each free entry, and let $g(X)=X^2-X$. The three polynomials $1,p_v,g$ form a basis of the space of degree-at-most-two univariate polynomials. Expand $R$ in the corresponding product basis. If $r$ is the largest number of $g$ factors in any term with nonzero coefficient, then
$$
 c(\log k)^{4/3} \ \le\ D\log M + O((r+1)\log(k+2)) .                 \tag{1}
$$
In particular on **every** gadget with $k\ge M^\delta$ for fixed $\delta>0$ and sufficiently large $M$, **every** choice of the $p_v$ leaves a term with $\Omega((\log k)^{1/3})$ such factors. For prescribed powers $e_v\in\{1,2\}$ take $p_v=X^{e_v}$. A monomial with at most $u$ present entries using a different exponent expands with at most $u$ factors $g$, since the other power is $p_v+g$ or $p_v-g$. Thus each prescribed power pattern has an ordinary surviving monomial differing at that many matching entries. This concerns the polynomial after the Boolean specialization of its other entries.

To see (1), define the interpolation operator $J_v R=(1-p_v)R|_{X_v=0}+p_vR|_{X_v=1}$. It fixes $1,p_v$ and kills $g$ in that coordinate. The commuting operators $J_v-I$ therefore give
$$
 \prod_v J_v R=\sum_{|S|\le r}\left(\prod_{v\in S}(J_v-I)\right)R
              =\operatorname{perm}_k((p_v(X_v))_v).
$$
The first equality follows term by term in the product basis. The second follows by Boolean interpolation of the cube values, or uniqueness of the multilinear representative in the new symbols. Expanding the three choices in each operator constructs the right-hand polynomial with $(M^D+1)k^{O(r+1)}$ gates for $k\ge2$.

For each $v$ choose $b=0$ if $a_v\ne0$, and $b=1$ otherwise. Then $p'_v(b)\ne0$ even in odd positive characteristic. In $F[X][t]/(t^{k+1})$ solve $p_v(b+u)=p_v(b)+tX_v$ with $u(0)=0$. The coefficient of $t^\ell$ obeys
$$
 p'_v(b)u_\ell=\mathbf1_{\ell=1}X_v-b_v\sum_{i=1}^{\ell-1}u_i u_{\ell-i}.
$$
Substitute these series simultaneously. The coefficient of $t^k$ in $\operatorname{perm}_k((p_v(b)+tX_v)_v)$ is the formal permanent. Truncation at every gate by ordinary convolution costs polynomial overhead in $k$ and divides only by the displayed nonzero field constants. Applying the formal lower bound proves (1). [Per-entry power extraction](degree-two-permanent.md)

## Concentration of the proportional entries in few rows and columns

Call an original entry proportional if $\dim_F\operatorname{span}\{B_v,C_v\}\le1$. Since the cube permanent depends on every entry, $B_v+C_v$ is nonzero: fix the other entries to a permutation with the $v$ edge removed. At a proportional entry there are constants $a_v,b_v$ with $a_v+b_v=1$ and $(B_v,C_v)=(a_v,b_v)(B_v+C_v)$. Thus $J_vP=P$ with precisely the normalized quadratic above. The identity persists under any Boolean restriction of the other entries.

If a matching of $k^2$ proportional entries existed with $M\ge2k^2+k$, the gadget would leave $r=0$ for these choices. Take $k=\lceil\exp(C(\log M)^{3/4})\rceil$. For sufficiently large fixed $C$ depending on $D$ and the formal lower bound, inequality (1) fails and the room condition holds for all sufficiently large $M$. Hence the maximum matching in the bipartite graph of proportional entries has fewer than $k^2$ edges. All endpoints of a maximal matching cover that graph, using fewer than $2k^2$ rows and columns. This gives the claimed concentration.

## One cheap vanishing term passes all these tests

Set $Z_M=\prod_v(1+X_v^2-X_v)-1$, with $O(M^2)$ gates. On every Boolean point $Z_M=0$. Every restriction above leaves $Z_{k}$ on the $k^2$ free entries. In the product basis for *any* normalized choices $p_v$, its coefficient on $\prod_v g(X_v)$ is one. Adding $\operatorname{perm}_k$ cannot cancel it for $k\ge2$, because each permanent monomial involves only $k$ distinct variables. In the ordinary power basis the all-present monomial with exponent opposite to each prescribed $e_v$ likewise has coefficient $+1$ or $-1$. One ambient perturbation simultaneously realizes the maximum defect $k^2$ on all matching gadgets.

For $P^\star=\operatorname{perm}_M+Z_M$, at every entry $C_v=\prod_{w\ne v}(1+g(X_w))$ has constant coefficient one, while $B_v+C_v$ is the permanent minor, nonzero with constant coefficient zero for $M\ge2$. Thus coefficient independence holds everywhere as well. Only the added term is known to be cheap. The examples demonstrate why these output properties alone do not yield a circuit-size lower bound for all degree-two representatives or a SAT time lower bound.

Forbes, Kumar and Saptharishi study functional lower bounds under arithmetic depth and degree restrictions and their Boolean consequences. Hrubeš studies hardness of canonical multilinearization and uses homogeneous extraction. These supply relevant precedents for the setting and method. Priority of the prescribed-matching deductions has not been established. [Forbes, Kumar and Saptharishi](https://arxiv.org/abs/1605.04207) · [Hrubeš, Theorem 1 and Lemma 4](https://users.math.cas.cz/~hrubes/PDFs/Mult.pdf) · [Finite matching and inverse checks](../audits/matching_coordinates_permanent_audit.py)
