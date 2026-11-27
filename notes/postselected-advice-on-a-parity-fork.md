# Relative scores for advice at a single SAT-controlled fork

In the [single-fork controller](the-first-choice-in-a-winner-transcript.md), the optional first pair has priority over the unconditional fallback. All later guarded pairs follow the first award. On a clean run of $m\ge1$ blocks, the better expert is one if the optional row accepts and zero otherwise. The difference between their mistake counts is $m$ in either case. How many input bits must a local test inspect to give the better expert a larger score? With existential replies and two scores conditioned on survival, **one probe suffices for strict preference on every input of a parity family**. Its optimal worst-input advantage is exactly $1/[2(2^D-1)]$ on $D$ independent bits. Thus a large gap in mistakes cannot by itself supply a usable gap in the scores.

## An explicit optional row

Give the optional row the ordinary 3-CNF $F_x$ for $x\in\{0,1\}^D$, $D\ge1$. It contains one unit fixing $X_j=x_j$ for each $j$. Take $Z_1=X_1$ and introduce $Z_j=Z_{j-1}\mathbin{\oplus}X_j$ for $2\le j\le D$, then require $Z_D=1$. Repeat a literal three times for each unit. The four clauses for $c=a\oplus b$ are

$$
(a\lor b\lor\neg c),\quad(a\lor\neg b\lor c),\quad
(\neg a\lor b\lor c),\quad(\neg a\lor\neg b\lor\neg c).
$$

The pins and gates determine every variable. The number of full satisfying assignments is precisely the parity bit $P(x)=\bigoplus_jx_j$, so the better expert in this explicit fork is $P(x)$. Flipping one source bit changes only its unit. There are $5D-3$ clauses, counting the terminal unit, and $O(D\log(D+2))$ encoded bits with fixed-width literal fields. An encoded RAM word of logarithmic length intersects only $O(1)$ distinct source pins. The two score tests below have access to these independent pins and the common template. At a genuine native checkpoint the optional row instead checks the endogenous bounded computation of its descriptor. No description of that unmodified row by independent external pins follows from this construction.

## The exact optimization over projected replies

A tagged primary string $z$ has color $b_z\in\{0,1\}$, nonnegative input-independent weight $w_z$, and survives on $x$ if **some** reply makes its bounded verifier accept. Count its weight once in that color whenever it survives. A public tape with replies for both colors can be represented by two tagged copies. The prediction on each input draws a surviving string in proportion to its weight. Require positive total weight on every input. There is no quantitative lower bound on this weight. The counts, or their relative sizes, can take much longer to compute than checking one reply.

Suppose each successful verification reads at most $q$ distinct source bits, adaptively. For each fixed tag its survival set $A_z$ is the union of the accepting transcripts' subcubes, each described by at most $q$ literals. Conversely a width-$q$ DNF gives such a verifier by asking the reply to name a term and then checking its literals. For this converse the representation of the DNF and the work outside the source probes are unrestricted. For $0\le q\le D$, define

$$
\eta_q(D)=\max_{\substack{\varnothing\ne A\subseteq\{0,1\}^D\\
                  A\ {\rm expressible\ by\ a\ width}\text{-}q\ {\rm DNF}}}
   \frac{\left|\sum_{x\in A}(-1)^{P(x)}\right|}{|A|}.
$$

**The optimal worst-input conditional accuracy is $(1+\eta_q(D))/2$.** For the upper bound suppose every input has accuracy at least $p$. Sum the good weight minus the erroneous weight over all inputs. This is at least $2p-1$ times the total surviving weight summed over inputs. Each tag contributes at most $w_z\eta_q(D)|A_z|$ to the difference by the definition. Dividing by the total gives $2p-1\le\eta_q(D)$.

For attainment choose a maximizing $A$ and let $b$ be its majority parity. Choose a uniform $D$-bit shift $s$, give it color $P(s)\oplus b$, and let it survive when $x\oplus s\in A$. Given any $x$, the shifted points of the surviving tags range exactly once over $A$. The fraction predicting $P(x)$ is therefore $(1+\eta_q(D))/2$ at every input. A term for the shifted DNF can be checked using at most $q$ source probes.

### Average certificate length

Let $G,E$ be the good and erroneous surviving weights, summed over all inputs. At every good tag and input choose one accepting transcript, and write $L$ for the sum of its number of distinct inspected source bits, weighted by the tag. The following inequality allows unrestricted lengths on the erroneous transcripts.

$$
                         DG-L\ \le\ DE.
$$

Indeed a good incidence of length $t$ stays accepted on at least $D-t$ neighbors by flipping an unread bit. Each such survivor is now erroneous with the same tag and weight. Each erroneous tag-input incidence can receive these charges from at most $D$ neighbors. This proves the inequality, including for nonuniform tag weights. In particular, with $G>0$ and $\bar q=L/G$, a uniform conditional success probability at least $p$ forces $p\le D/(2D-\bar q)$. For a worst-case probe cap $q$, an advantage $\epsilon$ needs $q\ge4\epsilon D/(1+2\epsilon)$. The earlier [postselected Walsh analysis](postselected-walsh-forecasts.md) already gives this pointwise bound for a worst-case cap and examples attaining it when $D-q>0$ divides $D$. The weighted inequality charges the mean of the chosen **correct** certificates. The mean is taken over the surviving mass on the whole cube, before separate normalization at each input.

### The one-probe optimum and its consequence

A width-one DNF is a union of literals. Its complement is empty or a subcube. Every positive-dimensional subcube has zero signed parity sum. Thus a one-probe survival set with nonzero signed mass must omit exactly one point. It then has signed mass of absolute value one and total mass $2^D-1$. Such sets exist by allowing the reply to name one coordinate where the input differs from a specified string. Hence $\eta_1(D)=1/(2^D-1)$.

Explicitly, give each $D$-bit guess $y$ the color $1\oplus P(y)$. It survives if the prover supplies one coordinate where $y$ differs from the input. Every guess except the true string survives. The better expert gets $2^{D-1}$ surviving guesses and the other gets $2^{D-1}-1$, even though arbitrary numbers of replies may certify some surviving guesses. The missing one determines a strict ordering. Recovering its sign from an inverse-polynomial-precision estimate of the conditional fractions is unjustified when $D$ grows sufficiently fast. One can also partition the coordinates into $\lceil D/q\rceil$ blocks for $1\le q\le D$, guess their parities and offer to check one disagreeing block. This attains the same expression with $\lceil D/q\rceil$ replacing $D$, without asserting optimality for those widths.

Counting every accepting deterministic branch separately changes the conclusion. With input-independent branch weights the difference of the two raw scores is a polynomial of degree at most $q$ on the cube, since each transcript indicator is a conjunction of at most $q$ literals. Its parity Fourier coefficient vanishes for $q<D$, while a strict correct sign everywhere would make that coefficient nonzero. Existential projection within each tag is what lets one probe give any strict preference here. Classical postselected query algorithms and their rational-function characterization are studied by [Cade](https://arxiv.org/abs/1804.10010). The journal's use of projected counts and their approximate recovery builds on [Stockmeyer's approximate counting](https://doi.org/10.1145/800061.808740) and the [postselected Walsh construction](postselected-walsh-forecasts.md).

For the attempted single-fork argument, a qualitative comparison of frequencies from locally verified guesses holds even on a fork with full mistake margin and independent parity pins. One must establish a comparison with enough numerical separation for its proposed decoder, or provide a different way to recover its sign within the clock. For $D$ comparable to $2^i$, the weighted bound already rules out inverse-$\operatorname{poly}(i)$ advantage throughout this explicit cube at any probe clock $2^{\delta i}$ with fixed $\delta<1$. Inspecting all pins computes parity on these formulas. The result concerns local advice before the first award and leaves the unrestricted SAT time bounds open. Historical priority for the extremal formulation has not been established.

[Finite audit of width-bounded survival sets, certificate charges and ordinary pinned formulas](../audits/postselected_advice_parity_audit.py)
