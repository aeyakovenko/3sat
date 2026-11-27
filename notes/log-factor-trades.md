# A finite checkpoint trade at linear SAT time

**Research journal, 24 November 2026.** On the specified packed logarithmic-word RAM, a correct explicit SAT solver cannot simultaneously take $O(N)$ time and use $O(N/\log^{25/4} N)$ auxiliary **bits**. Here $N$ counts encoded formula bits. The calculation below uses the same local formula generator and final materialized reduction as the earlier bound with space exponent $7$. Historical priority for the refined exponent is unverified. [Packed model and both reductions](materialized-input-census.md)

Suppose the SAT time and space exponents are $a$ and $b$, giving bounds $O(N\log^a N)$ and $O(N/\log^b N)$ bits. Set $A=a+3$, $p=a+2$, $B=b-2$, and $C=B-p$. For a source computation with $m$ public words and clock $R$, put $H=\max(R,m,2)$ and $L=\log_2(H+2)$. The virtual reduction gives deterministic time $O(HL^A)$ and snapshots of $O(H/L^B)$ **words**. The materialized reduction gives a complementary simulation costing $O(RL^A+mL^p)$ even when $R<m$. This first direct use matters because $A>p$. [Reduction and unbalanced public-input cost](materialized-input-census.md)

## Charging the intermediate inputs

A profile $(e,f)$ gives complementary time $O(HL^e+mL^f)$. When $0\le e\le f$, raising a subproblem's clock to its input length still gives time $O(RL^e+mL^f)$. Use $k$ nested checkpoint levels with branching factors $\lceil L^{u_i}\rceil$, numbered outermost first. At level $i$ the verifier sees the entire list of checkpoints for that level. After picking a segment, it passes its two endpoints and the original public input to the next level. Determinism permits the required polarity at each level. The work exponents relative to $H$ are

$$
u_i-B+f+(i-1)e\quad (1\le i\le k),\qquad
A-\sum_i u_i+ke.
$$

The original public input costs $mL^{f'}$, with $f'=f+(k-1)e$. Allow also $HL^{f'-B}$ to copy the endpoints. Loading the innermost endpoints contributes at most $HL^{ke-B}$, which fits this allowance when $e\le f$. These bounds use a fixed number of levels and the fixed polynomial-times-logarithmic clocks of the packed simulation. They charge only the selected endpoint pair at the next level, while charging each full list when eliminating its own quantifier. [Checkpoint construction and input lengths, FLMV, Lemma 5.3](https://lance.fortnow.com/papers/files/tst.pdf)

Choose
$$
E=\frac{A+k(f-B)+k(k+1)e/2}{k+1},\qquad
e'=\max(E,f'-B),\qquad
u_i=e'+B-f-(i-1)e .
$$
All widths are nonnegative. Each list costs $HL^{e'}$ and the replay costs at most that much because $e'\ge E$. This gives the new profile $(e',f')$. For the first depth-one step, use the direct $(A,p)$ resource bound above. Its additional endpoint exponent is $A-B$, which fits the balanced work exponent $A-C/2$ for the positive $C$ below. Later uses have $e\le f$. A final $e'<0$ makes the complementary time $o(H)$ on the bounded diagonal inputs with quadratic $H$ and linear $m$. This contradicts the complementary-time hierarchy. [Packed complementary diagonal](packed-band-transfer.md)

## One final choice of depth

When $0<C<A$, repeated depth-one steps keep $f=p$ and send $e$ to $(A-C+e)/2$. Starting at $A$, the work exponent after $j$ steps is $e_j=A-C+C/2^j$. After the first step it is at most $p$ whenever $C\ge2(A-p)$. That condition holds in the parameter range $C/A>7/9$ for $a\ge0$.

Use one final depth $k$ with that same profile at every level. Its limiting work exponent is
$$
\max\left\{
\frac{A-kC+k(k+1)(A-C)/2}{k+1},\ (k-1)(A-C)-C
\right\}.
$$
For the first term to be negative requires $C/A>[k(k+1)+2]/[k(k+3)]$. This fraction exceeds $7/9$ by $2(k-3)^2/[9k(k+3)]$. At $k=3$ the second term is already negative for $C/A>2/3$. Thus **$C/A>7/9$** is the exact strict threshold for this family of depth choices. Negativity at the limit holds after finitely many depth-one steps by continuity. A larger $C$ can always be weakened to a value below $A$ in this range. In SAT units the sufficient inequality is $b>16a/9+19/3$.

## An exact certificate for $a=0$, $b=25/4$

Here $(A,p,B,C)=(3,2,17/4,9/4)$, so $C/A=3/4$. Six depth-one steps give $(201/256,2)$. Rounding the work exponent up to $51/64$ makes the following independent calculation shorter.

| Next depth | Work exponent | Public-input exponent |
| ---: | ---: | ---: |
| 2 | $19/64$ | $179/64$ |
| 4 | $1/32$ | $59/16$ |
| 11 | $-3/32$ | $4$ |

The resulting time is $O(H/L^{3/32}+mL^4)$, which is $o(H)$ on the hierarchy inputs. Keeping $201/256$ exactly gives $-1/640$ after just the next depths $2,4$. The script checks every width, the input guard and the endpoint charge. It recomputes the resulting cost from the innermost segment outward with exact fractions. [Reproduce the finite checks](../audits/log_factor_trades.py)
