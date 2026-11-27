# A finite alternation trade for a planar tape and polynomial random-access storage

**Theorem.** A deterministic SAT solver with random access to its input, one unrestricted planar nearest-neighbor work tape, and at most $T^{1/4+o(1)}$ auxiliary random-access words at clock $T$ cannot run in $O(n^{541/500})$ time on every explicit input of $n$ encoded bits. The model has logarithmic words and a fixed instruction set with polylogarithmic bit cost. A cap on nonzero auxiliary words suffices. Tape cells may contain a logarithmic word.

Here $541/500=1.082$. For the same scratch cap, the single-iteration-family limit in the crossing-chart note is $(1+\sqrt{43})/7\simeq1.07963$. The general curve below improves that limit at every $0\le\omega<1/d$. The extension uses *two* applications of a conditional simulation under different public input bounds, following the structure of Williams's Section 7. The known $1.1887$ bound for a planar tape assumes subpolynomial random-access storage. Moving an entire $T^{1/4}$-word store alongside a pure tape head incurs a polynomial cost that swamps this small difference. Priority of the finite polynomial-store consequence has not been established. [Crossing simulator and single-iteration-family limit](hybrid-tape-crossing-chart.md) · [Physical simulation comparison](hybrid-scratch-read-write.md) · [Williams, §7.3](https://people.csail.mit.edu/rrw/automated-lbs.pdf)

## Rules and retained inputs

All numbers in the proof are exponents relative to $n$, suppressing $n^{o(1)}$ factors. A public input of exponent $b$ has at most $n^{b+o(1)}$ bits. Write $H[t]$ for deterministic time exponent $t$ on the indicated mixed machine with scratch exponent at most $t/4$. Write $R[t,s]$ for general deterministic random-access validation with time exponent $t$ and private workspace exponent $s$. An earlier public input remains accessible at a checkpoint. Selecting a segment requires just its two endpoints and the validator's *original* public input.

Three rules implement the schedule.

1. **Spatial division.** In an $H[t]$ computation, use translated squares of side exponent $5t/4-1$. There are at most $n^{t-(5t/4-1)+o(1)}$ crossings on a suitable translation. Recording the full scratch state at each crossing costs total exponent one. The time-$t$ verifier checks all periods in two orders and uses space $s(t)=\max\{2(5t/4-1),t/4\}$. The chart becomes immutable public input. The tables below use only exponents for which the side lies between $t/4$ and $t$ and the chart fits in time $t$. [Tile replay proof](hybrid-tape-crossing-chart.md#a-short-description-checked-in-small-space)
2. **Temporal division.** Split $R[t,s]$ into $n^z$ successive segments. Guess a table of size exponent $z+s$, then let the opposite sign choose one segment using $O(\log n)$ bits. With original public exponent $b$ its check retains only $\max(b,s)$ and costs $n^{t-z+o(1)}$ steps in the uses below, where $s\le t-z$. Check the true initial and final conditions along with the segment. Determinism also allows the complement orientation, guessing a table for the negated verdict. Successive blocks of the same sign merge. [Williams, Lemma 3.3](https://people.csail.mit.edu/rrw/automated-lbs.pdf)
3. **SAT slowdown.** Suppose for contradiction the stated SAT solver exists and write $c=541/500$. Removing one existential or universal block, its deterministic residual, and any data-selection phase gives a mixed computation. If the public input *before* the block, the guess, the retained input and the residual time all have exponent at most $b$, its time exponent is $cb$ and its auxiliary scratch exponent is $cb/4$. A fixed packed bounded-run reduction supplies individually accessible words of a 3-CNF of exponent $b$. Negate acceptance when removing a universal block. A general RAM can simulate the residual hybrid tape in polylogarithmic overhead, and the final hybrid solver reads through to the original public input. [Packed reduction](packed-band-transfer.md) · [Hybrid slowdown proof](hybrid-tape-crossing-chart.md#two-blocks-and-the-square-root)

For public input of exponent one, the crossing-chart induction gives
$$
H[e_i]\ \subseteq\ (\exists n^{1+o(1)})(\forall O(\log n))R[1,s(e_1)],
\qquad
e_1=8/7,\quad e_{i+1}=(3+e_i/c)/(7/2).
$$
The dual form begins with a universal guess. The last verifier has public exponent one. In the spatial split at $e_i$, take the temporal split $z=1-s(e_i)$. Both charts together cost exponent one, and the selected segment costs $e_i-z$. This equals 1 for $i=1$ and $e_{i-1}/c$ otherwise. Since the already guessed outer data and the selected endpoints fit exponent one and $e_{i-1}/c\ge1$, one slowdown places the residual inside $H[e_{i-1}]$. The next existential chart merges with the first. Only levels through three occur below, and all side and space conditions hold there. Scaling all these exponents by $v$ gives the same simulation with public exponent $v$ and clock $v e_i$. [Full induction](hybrid-tape-crossing-chart.md#iterating-the-inner-slowdown)

## Two uses of the three-level simulation

Set $a=59/50$, $v=1007/1000$, and put $s=s(a)=19/20$. Start with any $H[a]$ computation on an input of length $n$.

| Step | Data guessed or retained | Deterministic tail |
| --- | --- | --- |
| Spatial chart | Existential chart of exponent 1 | $R[a,s]$ with public exponent 1 |
| First time split $x=v-s=57/1000$ | Existential table joins the chart, giving exponent $v$. Universal short selector retains the original chart and two endpoints, of total exponent 1. | $R[a-x,s]$ |
| Second time split $1-s=1/20$ | A universal table of exponent 1 merges with the selector. A short existential selector retains public exponent 1. | $R[a-x-(1-s),s]=R[1073/1000,s]$ |
| Remove short existential | Remaining blocks have sizes $v,1$ and signs $\exists,\forall$. The residual public exponent is 1. | $H[580493/500000]$ |
| Apply three-level simulation, universal orientation | Its universal chart joins the universal block. Remove its short existential at cost exponent $c$. | $H[c]$ after $\exists n^{v+o(1)},\forall n^{1+o(1)}$ |
| Remove universal | The incoming public data have exponent $v\le c$ and the verifier time exponent is $c$. | $H[c^2]$ after the first existential block |
| Apply three-level simulation at scale $n^v$, existential orientation | Its first chart joins that outer block. The short universal retains public exponent $v$ and its residual time is $v$. | Removing it gives $H[cv]$, then removing the first existential gives $H[c^2v]$. |

In the second time split the earlier existential table of exponent $v$ is visible while selecting its first pair of endpoints. After that selection the segment checker uses only the spatial chart, the base input and those endpoints, which all fit exponent one. The later slowdown that removes the universal block explicitly charges the incoming exponent $v$. These two charges differ.

In exact arithmetic, $e_2=30722/26509$ and $e_3=116770214/100389583$. The two shortcuts apply because
$$
c\,(1073/1000)<e_3,\qquad c^2<v e_3 .
$$
The final clock is
$$
c^2v=294729767/250000000 < 59/50 = a .
$$
This would accelerate every deterministic hybrid computation of exponent $a$ to a strictly smaller exponent on the same hybrid model. A bounded universal hybrid interpreter yields the contradiction. To see it directly, choose $b$ strictly between $c^2v$ and $a$. On a padded machine description of at most $\log n$ bits, flip the simulated machine's decision if it halts within $n^b$ steps and its auxiliary storage stays within $n^{b/4}$ words. Truncate otherwise. The interpreter can read instructions from the input, simulate sparse registers in a dictionary, and pad or encode any fixed tape alphabet or logarithmic word size by a polylogarithmic dilation of the tape grid. With logarithmic overheads per simulated step and word, its time is $n^{b+o(1)}$ and its scratch bound is $n^{b/4+o(1)}$, both within the allowances at exponent $a$. Fixed word coefficients and alphabets for the diagonal language's hypothetical faster decider are covered on sufficiently long padded descriptions. That decider would always finish within the interpreter's caps, so they give opposite answers on its own description. Equivalently use the polynomial-gap mixed-model time hierarchy with a fixed instruction alphabet. Strict clock slack absorbs all polylogarithms and the fixed finite number of reductions.

## The exponent curve for polynomial scratch

For every fixed $d\ge1$ and $0\le\omega<1/d$, put $D=d+1+d\omega$. Let $c_0>1$ solve $Dc_0^2=c_0+d+1$. The same two uses of the conditional simulation exclude **every $c<r$**, where $r$ is the unique root in $(c_0,(d+2)/D)$ of
$$
 \big((2D-1)c^2-1\big)c(Dc-1)^2
 -(2d+1)(d+1)(Dc-1)-(d+1)^2=0.
$$
At $\omega=0$, expansion of this expression gives Williams’s Theorem 7.5 polynomial exactly. At $d=2$, $\omega=1/4$, the root lies strictly between $1.082755$ and $1.082756$.

For general dimension the tile side exponent is $(1+\omega)t-1$ and the space exponent is $s(t)=d((1+\omega)t-1)=(D-1)t-d$. It exceeds $\omega t$ at every $t>1$ used here, since $s(t)-\omega t=d(t-1)+(d-1)\omega t>0$. Set $e_1=(d+2)/D$ and $e_{i+1}=(d+1+e_i/c)/D$ as in the crossing-chart proof. For a starting clock $a$ and first public exponent $v$, split time at exponents $v-s(a)$ and $1-s(a)$. The residual replay has exponent $b=a-v+2s(a)-1$. The three strict comparisons needed for the shortcuts and the hierarchy are
$$
 c\max(1,b)<e_k,\qquad c^2<v e_k,\qquad c^2v<a .
$$
The remaining conditions are $1\le v<c$, nonnegative splits, $s(a)\le b$ and feasibility of the $k$ inner shortcuts.

For $c_0\le c<e_1$, the increasing sequence $e_i$ tends to $E=c(d+1)/(Dc-1)$. In fact $e_1>c$, $e_1<E$, and the affine update has slope $1/(Dc)<1$. Define target values
$$
 v= c^2/E= c(Dc-1)/(d+1),\qquad a=c^2v .
$$
At $c=c_0$ we have $E=c_0^2$, $v=1$ and
$$
 s(a)=1+c_0-c_0^2<1,\quad b=2c_0-c_0^2<1,
 \quad b-s(a)=c_0-1>0.
$$
In particular $b<E/c$. As $c$ increases, both $a-v=(c^2-1)v$ and $s(a)$ increase strictly. Thus $b$ increases and $E/c$ decreases strictly. At $c=e_1$, the formulas give $v=c$, $a=c^3$ and $E/c=1$. At this endpoint
$$
 s(a)-1=(D-1)c^3-Dc+1=(c-1)((D-1)c(c+1)-1)>0 .
$$
Hence $b>1=E/c$ there. This proves there is exactly one crossing $b=E/c$ between $c_0$ and $e_1$. Substitution of the formulas for $v$ and $a$ and multiplication by $(d+1)(Dc-1)>0$ gives the displayed quintic.

For $c_0\le c<r$ we have $v\ge1$, $v<c$ and $b<E/c$. If $s(a)\ge1$, then $b\ge1+v(c^2-1)\ge c^2>c/v=E/c$, a contradiction. Also $b-s(a)=a-v+s(a)-1$ increases from the strictly positive value at $c_0$. Thus $s(a)<1$, $s(a)<b$, and both time splits are positive. For the inner shortcuts, $E$ decreases with $c$ and $s(E)\le s(c_0^2)<1$, so every inner space exponent fits the normalized public input. Each $e_i/c>1$ covers the incoming public data at its slowdown.

Increase $v$ slightly, then choose $a$ slightly above $c^2v$, keeping $v<c$, both positive splits, $s(a)<b$, and $c\max(1,b)<E$. The last inequality has strict slack since $E>c$ and $b<E/c$ at the original values. Now $c^2/v<E$. Choose a finite $k$ with $e_k>\max(c\max(1,b),c^2/v)$. The three strict comparisons all hold. The case $c<c_0$ follows by monotonicity of the time and storage budgets. Rational time caps may be chosen inside the strict slack, relaxing an irrational scratch exponent slightly upward if necessary. For positive $\omega$, the universal interpreter uses cap $n^{h\omega}$ at an intermediate clock $h$ strictly between the two deterministic exponents. For $\omega=0$ use the conditional time hierarchy for subpolynomial hybrid stores in Williams’s Lemma 7.3 under the same SAT slowdown premise. At $\omega=1/d$ the starting value is $c_0=1$, and the positive margins used here vanish.

The [exact rational checker](../audits/mixed_tape_williams_schedule_audit.py) evaluates the three shortcut levels, retained input bounds and strict final inequalities. [Lean proofs](../lean/MixedTapeWilliamsSchedule.lean) check the rational shortcut clocks, public-input and space constraints and final strict inequalities. The model simulations and the hierarchy argument are manuscript proofs. The unrestricted RAM question permits a full clock's worth of independent writable words, beyond this example's scratch bound.
