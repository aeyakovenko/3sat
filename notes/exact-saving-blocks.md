# A quantitative bound for constant intervals of description savings

**Research journal, 24 November 2026.** For the native source, let $E_{a,d}$ be the sum of the two-clock improvements in shortest-description weight over words whose timely shortest program saves exactly $d$ bits. Under linear deterministic SAT, the sum of the derivatives of these reals over a constant number of consecutive savings pays a constant multiple of the universal a priori weight of the initial saving. The constants may depend on the native machine. A family of literally universal native machines shows why some such dependence on the machine is necessary. [Definition of the exact-saving series](clocked-complexity-increments.md)

Write $T(m)=2^{3m}$, $t(m)=\max(1,\lfloor T(m)/m^a\rfloor)$ and $\Delta(y)=2^{-K_T(y)}-2^{-K_t(y)}$. All complexities with a clock are on the specified native source. Fix an ordinary optimal prefix machine with halting probability $\Omega$, and use its unbounded complexity $K(D)$ for encoding integers. Write $\partial\alpha$ for the Barmpalias–Lewis-Pye tail derivative of a left-c.e. real with denominator $\Omega$. It is nonnegative, additive, and strictly positive exactly for random left-c.e. reals. The following bounds concern the actual two-clock series. [Tail-ratio theorem](https://arxiv.org/abs/1604.00216) · [Derivative and randomness](https://people.math.wisc.edu/~jsmiller8/Papers/derivation.pdf)

More explicitly, fix a computable nondecreasing rational approximation $\Omega_s\to\Omega$. For *any* computable nondecreasing rational approximation $\alpha_s\to\alpha$, the ratios $(\alpha-\alpha_s)/(\Omega-\Omega_s)$ converge to the same finite value $\partial\alpha$. For a nonrandom left-c.e. $\alpha$, this follows also by applying the two-random-real version to $\alpha+\Omega$ and $\Omega$ and using the randomness characterization for the zero value. For rational $\alpha$ one can use the constant approximation, giving derivative zero, including for rational finite corrections and zero terms. If two chosen approximations satisfy $\alpha-\alpha_s\ge c(\gamma-\gamma_s)$ for all sufficiently large $s$, divide both sides by the same positive $\Omega-\Omega_s$ and pass to the limit. This is the synchronized comparison used below.

Assume linear deterministic time for explicit SAT on the unrestricted logarithmic-word RAM. There are $a_0,H\in\mathbb N$ and $c>0$ such that, for every $D\ge1$ and $a\ge a_0$,

$$
\sum_{d=D+1}^{D+H}\partial E_{a,d}\ \ge\ c2^{-K(D)}.
$$

In particular one of these exact savings has derivative at least $c2^{-K(D)}/H$ and a random series for every $a\ge a_0$. For the broad clock pair $2^{3m},2^{5m}$, the same assertion holds unconditionally.

## Charging the costs jointly to the saving and the phase

Begin with $a=a_0$. In the feedback experiment for threshold $D$, let $A(D,r)$ be $2^D$ times the target-word mass in failed windows of phase $r$ whose first producer of length less than $m-D$ finishes in $(t(m),T(m)]$. The word mass of a word of length $m$ is $2^{-m}$. For $h\ge1$, let $B_h(D,r)$ restrict the same scaled amount to $K_T(y)\le m-D-h$. These quantities are computable after finite simulations. For fixed $D$, each word occurs at most once over $r$. Summing a word's possible contributions $2^{D-m}$ over $D\le m-K_T(y)-h$ costs at most $2^{1-h-K_T(y)}$. Kraft's inequality gives $\sum_{D,r} B_h(D,r)\le 2^{1-h}$. [Window construction](varying-description-savings.md)

Consequently the marginal

$$
L(D)=\sum_{h,r} \frac{2^h}{(h+1)^2}B_h(D,r)
$$

is lower semicomputable with finite, absolutely bounded total. Universal semimeasure domination and the coding theorem give $L(D)\le C_0 2^{-K(D)}$ with one fixed integer $C_0$. Retaining $D$ in this marginal will pay for its header.

Use a conditional optimal prefix machine $U(p\mid z)$ with ordinary bit-by-bit output, where $z=(D,k)$ is auxiliary information. Its compiler simulates the fixed ordinary machine of probability $\Omega$ on one fixed header while ignoring $z$. Pair each halting input $p$ and its conditional runtime $u$ into the previously used injective phase index $r(p,u)\ge 6+3(u+|p|+1)$. Put $w^z_r=2^{-|p|}$ at that index and zero at empty indices. Given $z,r$ this is computable by inversion and bounded simulation. Its sum $\Omega^z$ is random and $\partial\Omega^z\ge c_1>0$ uniformly in $z$, by the fixed ordinary compiler prefix and its left-c.e. complement.

One native grant decoder first reads a halting self-delimiting program $q$ for $D$, measures $k=|q|$, then runs $U(p\mid D,k)$ and obtains $r$. Take the cell depth at output length $m$ to be $m-D-k-|p|-e$ where the decoder reads a self-delimiting integer $e$ and we fix $e$ larger than its encoding length plus the fixed native header cost. The whole name has length less than $m-D$. For each fixed $D$, take $q$ shortest. Its fixed simulation time and $D,k$ are absorbed at sufficiently late phases. The mask computations and exact prefix unranking are those for the common grant. Its runtime exponent is uniform in $D,k$, which are supplied to the same fixed algorithms. For all sufficiently late phases of this $D$,

$$
A(D,r)\ \ge\ c_2 2^{-k} w^z_r .
$$

Indeed the raw grant is $2^{-D-k-e}w^z_r$. The final successful window costs at most $2^{1-r}$ in raw units, which is negligible compared to this grant since $|p|\le r/3$ and $D,k$ are now fixed. Empty rows contribute zero to the right. The narrow time interval uses linear SAT and a common sufficiently large $a_0$. In the broad interval the earlier names can be exhaustively simulated within the upper clock, giving the same estimate without a SAT solver. [Clock and grant calculation](varying-description-savings.md)

Uniform control of the exceptional *tails* strengthens this row estimate to a derivative bound. On auxiliary data $D,k$, construct one effective Kraft request machine for all $h,r$. For the pair $h,r$, request program mass

$$
\frac{2^k}{C_0}\,\frac{2^h}{(h+1)^2}B_h(D,r).
$$

Enumerate finite dyadic pieces approaching each requested rational from below, dovetail them, and discard pieces that would take total mass above one. When $k=K(D)$, the marginal estimate assures that no piece is discarded. On each granted name the machine prints $r+1$ bits. The fixed conditional compiler then gives genuine $U$-programs of a fixed fraction of the requested mass, finishing no earlier than step $r$. Their actual phase indices exceed $r$. Thus for every $R$ and $h$ and all true $D,k$,

$$
\sum_{r>R} B_h(D,r)\ \le\ C_3 2^{-k}(h+1)^2 2^{-h}\sum_{r>R}w^z_r .
$$

The constant includes a single compiler header and $C_0$. Choose $h\ge2$ fixed so that $C_3(h+1)^22^{-h}<c_2/2$. The tail of the computable nonnegative sequence $A(D,r)-B_h(D,r)$ now dominates $(c_2/2)2^{-k}\sum_{r>R}w^z_r$ for all sufficiently large $R$. Its sum has derivative at least $(c_1c_2/2)2^{-k}$ by synchronized tail comparison.

Each contributing word satisfies $D+1\le m-K_T(y)<D+h$, $K_t(y)\ge m-D$ and $\Delta(y)\ge 2^{D-m}$. Subtracting its credited amount from its contribution to the exact-saving band leaves a nonnegative computable amount. For fixed $D$, membership of a word is decidable by computing the successive windows until their length range passes the word's length. Every phase terminates. The band's full sum minus the credited subseries is therefore left-c.e. Positivity and additivity of the derivative prove the assertion with $H=h-1$. Increasing $a$ adds a nonnegative computable amount to each qualifying word, so the statement including the choice of a single exact $d$ persists for every $a\ge a_0$.

## What telescoping in the early clock forces

Set $E_{0,d}=0$. Under linear SAT there are fixed integers $b,H$ and $c>0$ such that for every $j\ge0,D\ge1$,

$$
\sum_{d=D+1}^{D+H}\partial\bigl(E_{b(j+1),d}-E_{bj,d}\bigr)
       \ \ge\ c2^{-K(D,j)} .
$$

Here $K(D,j)$ encodes the pair on the same ordinary prefix machine. Both exact-saving indices in the difference use the *original* upper clock $T$. For $t_j(m)=\max(1,\lfloor 2^{3m}/m^{bj}\rfloor)$, a word in its fixed column contributes exactly $2^{-K_{t_j}(y)}-2^{-K_{t_{j+1}}(y)}$ to the difference.

To prove the estimate, restrict the phase experiment to first eligible productions in the slab $(t_{j+1},t_j]$, still testing bad words against the *outer* $K_T(y)\le m-D-h$. For fixed $y,D$, the first eligible production can fall in at most one slab. Thus $\sum_{D,j,r}B_h(D,j,r)\le 2^{1-h}$, even with all slabs counted. Use the marginal above with $(D,j)$ in place of $D$. Supply a shortest header for this pair, and give the conditional grant machine the pair and that header's length. For fixed $j$, both deadlines eventually exceed $2^{2m}$; computing the powers and processing bounded transcripts have a common polynomial-in-$m$ overhead, since $j$ is fixed and supplied as data. The table of possible words has at most $2^m$ entries. The ratio of slab deadlines is asymptotic to $m^b$, so one sufficiently large $b$ pays the overhead for all fixed $j$ at late lengths. The good words satisfy $K_{t_{j+1}}\ge m-D$ and $K_{t_j}<m-D$, paying at least $2^{D-m}$ to the displayed difference. All tail comparisons carry over. Although summation in $j$ telescopes, every such slab therefore retains a constant-width band with positive derivative.

In each such band there is one fixed $d$ for which, for **every** computable unbounded nondecreasing integer weight $f(j)$,

$$
\sum_j f(j)\partial\bigl(E_{b(j+1),d}-E_{bj,d}\bigr)=\infty.
$$

If every column in the band had a weight giving a finite sum, take the pointwise minimum of its finite list of weights. This computable order still tends to infinity. The pair lower bound would make $\sum_j f(j)2^{-K(D,j)}$ finite, which is impossible by selecting computable $j_i$ with $f(j_i)\ge2^i$ and using $K(D,j_i)\le K(i)+O_D(1)$. For this one $d$, infinitely many disjoint clock increments are random. Furthermore the same weighted sums of the increments *themselves* diverge. Otherwise their left-c.e. sum would have a finite derivative dominating every finite partial sum in the display. In particular the convergence of $E_{a,d}$ as $a\to\infty$ has no computable modulus: a computable sequence of cutoffs with successive tails at most $2^{-i}$ would give a computable unbounded step weight with finite weighted sum.

## An unbounded weight on the saving

For every computable unbounded nondecreasing $f:\mathbb N\to\mathbb N$ and every computable $G(m)\to\infty$, linear SAT requires

$$
\sum_{y:\ 1\le d=|y|-K_T(y)\le G(|y|)} f(d)\Delta(y)=\infty.
$$

For each fixed $d$, the bandwidth excludes only finitely many words in its column. Its derivative is unchanged by this finite rational modification. If the displayed sum were finite it would be left-c.e., and its finite derivative would dominate every finite partial sum of $f(d)\partial E_{a,d}$. Each $d$ belongs to at most $H$ intervals above, so this would bound $\sum_D f(D)2^{-K(D)}$. This last series diverges. Select distinct increasing $D_j$ computably with $f(D_j)\ge2^j$; then $K(D_j)\le K(j)+O(1)=O(\log(j+2))$. A proof of finiteness for one such weighted band and arbitrarily large fixed $a$ would exclude linear SAT. The argument also allows any decidable filter that retains all but finitely many words of each fixed column.

## A derivative that remains in every tail, unconditionally

Let $E_{\infty,d}$ use the same $T$ and the early clock of one step. The $E_{a,d}$ increase to this real as $a$ tends to infinity by monotone convergence. There are constants $H',c'>0$ such that on the actual native source, without assuming linear SAT,

$$
\sum_{d=D+1}^{D+H'}\partial(E_{\infty,d}-E_{a,d})\ge c'2^{-K(D)}
\qquad(D\ge1,\ a\ge0).
$$

For this claim dispense with the feedback windows. At the single length $m=2^r$ let $A(D,r)$ be $2^D$ times the mass of all words with $K_{m^3}(y)<m-D$. Define $B_h(D,r)$ by additionally requiring $K_T(y)\le m-D-h$. The same geometric upper bound and marginal estimate hold because each word belongs to at most one of these lengths for each $D$. The conditional Kraft machine and its lower bound on the tails of $w^z$ therefore apply verbatim to this new computable $B_h$.

To obtain the grant, one fixed program reads $q,p$ exactly as above and computes $r$ and $m=2^r$. It reads $\ell=m-D-k-|p|-e$ free bits and outputs $m-\ell$ zeroes followed by those bits, skipping ineligible lengths. At a given nonempty phase for fixed $D,k$, this supplies $2^\ell$ different words, each with a name shorter than $m-D$. For fixed $q$ and all sufficiently late $r$, simulation of $p$ takes polynomial time in $r$, and reading the payload and printing the output takes $m\,\mathrm{poly}(\log m)$ native time. Thus all these names finish by $m^3$ and the scaled mass is at least $2^{-k-e} w^z_r$. Subtract the exceptional tail as before with a fixed $h$. The sum of the resulting nonnegative computable row masses has derivative at least $c'2^{-k}$.

For any fixed $a$, every sufficiently late selected length satisfies $t(m)\ge m^3$, and one step cannot publish an $m$-bit word. Each qualifying word then contributes $2^{-K_t(y)}\ge2^{D-m}$ to one of the displayed residuals. The credited set of words is decidable by checking the length and the two bounded complexities. Finitely many early lengths change the credited sum by a rational. This proves the unconditional bound with $H'=h-1$.

For fixed $D$, each of the finitely many residual derivatives decreases as $a$ increases. At least one fixed $d$ in the band has

$$
\partial E_{\infty,d}-\lim_{a\to\infty}\partial E_{a,d}
   \ \ge\ c'2^{-K(D)}/H'>0 .
$$

In particular $E_{a,d}\to E_{\infty,d}$ has no computable modulus for this $d$ even without a SAT assumption. A computable choice of exponents $a_i$ with residuals at most $2^{-i}$ would yield a finite left-c.e. sum of residuals whose derivative dominates arbitrarily many terms of uniformly positive derivative. The positive difference in the display records the failure of the derivative to commute with an infinite telescoping sum. It can persist regardless of the derivatives of its individual finite clock slabs. The conditional two-dimensional lower estimate instead bounds the derivatives of those individual slabs.

## Missing residue classes on a literal native interpreter

Fix an integer $M\ge2$ and an ordinary native stream interpreter $V$. Give a new native interpreter $M$ disjoint headers of lengths $1,\ldots,M$, namely $0,10,\ldots,1^{M-1}0$. Each ensuing raw payload $p$ simulates $V(p)$, counts the consumed payload bits and the output length $m$, and publishes only if the full name length is congruent to $m\pmod M$. On the separate longer header $1^{M+1}$, simulate the same raw $p$ and publish its output whatever its residue. This is a literal compiler for $V$ with a fixed prefix. Use a common simulated-step schedule and pad this last branch sufficiently that its output becomes visible no earlier than the corresponding successful residue branch on $p$. For example, scan each header first, postpone simulation to a common start tick, count both lengths on every branch, and allocate the same final tests and publication clock on each. These fixed-$M$ operations preserve polylogarithmic simulation overhead and require no end-of-input signal.

For every successful fallback name there is a strictly shorter name on precisely one of the residue headers that publishes the same word no later. Thus on this interpreter $K_S(y)\equiv |y|\pmod M$ whenever the clocked complexity is finite, for *every* clock $S$. All exact-saving series outside $M\mathbb Z$ are identically zero. This prevents a machine-independent cofinite conclusion and permits arbitrarily long constant gaps as the interpreter varies. Whether further consecutive savings can be forced on the particular fixed native source requires information about that source's implementation. No upper bound for the weighted band above has been found. Lean 4.19 checks existence of a matching header and its consequence for a shortest timely name under the stated branch rules. [Lean proof](../lean/ResidueHeaders.lean)
