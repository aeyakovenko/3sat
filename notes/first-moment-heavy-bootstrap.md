# A first-moment bound using explicit logs at expensive checkpoints

**Research journal, 24 November 2026.** For a deterministic UNSAT recognizer, let a prehalt memory state have cost $\min_z(1+|z|+q_z)$, where $z$ is an independent description that returns the correct word at every writable address within $q_z\ge1$ steps per query. A fixed evaluator can also read the original formula and the true native time. Its instruction set and word-width convention are fixed. CPU registers require only a constant number of extra words per selected checkpoint. Sum this minimum over all times before the first UNSAT signal. Missing descriptions have infinite cost. On the packed logarithmic-word RAM, a worst-case bound $N^{s+o(1)}$ on this sum over unsatisfiable formulas is impossible for each fixed $1\le s<s_0$, where
$$
  s_0^2(s_0-1)(s_0-1/2)=2-s_0,
  \qquad s_0=1.3760858894\ldots .
$$
The equation has a unique root in $(1,3/2)$ because the left side increases strictly and the right side decreases. The cost allows both the description and its query time to vary with the input and the exact snapshot. The proof combines a one-level verification that logs every read of expensive segments with the batched verification of [the first-moment audit](first-moment-snapshot-audits.md).

## Bounded computations and the checkpoint list

Allow two different machines. Suppose a deterministic UNSAT recognizer $A$ has first moment at most $N^{c+o(1)}$ on unsatisfiable inputs, and a nondeterministic UNSAT recognizer has some successful branch within $N^{d+o(1)}$ on every unsatisfiable input. Neither machine can give an UNSAT signal on a satisfiable input. Take $1\le c<3/2$, $1\le d<2$, and $cd<2$. A sufficient condition for contradiction is
$$
 d^2(c-1/2)(c-1)<2-d. \tag{1}
$$
At the stated self bound the deterministic recognizer is also the reference, since one unit is charged for every executed step.

Write $W(e,b)$ for the following assertion about each fixed bounded nondeterministic machine. Nonacceptance within $R$ steps on a public input of $m$ words has a sound nondeterministic certificate within $(R^e+m^b)H^{o(1)}$ steps, where $H=\max(2,m,R)$. The local packed reduction represents acceptance within the source clock by a formula of size $H^{1+o(1)}$, with packed words available from the original input in polylogarithmic time. Materializing this formula and using the reference yields $W(d,d)$. Under the nonacceptance premise the formula is unsatisfiable. The actual run of $A$ on it has first moment at most $H^{c+o(1)}$. [Machine, local reduction and hierarchy argument](packed-band-transfer.md)

Use windows of $w=H^{x+o(1)}$ native steps and choose a minimum-cost internal snapshot in each complete window. Include the true start and a final rejecting halt, with no description needed at either endpoint. Incomplete end windows can be skipped. The largest gap is at most $2w+O(1)$. Let $y=c-x$. The number of intervals, the total description lengths and the sum of the selected query caps are each $O(1+H^{y+o(1)})$. This follows by charging the minimum in each full window to its average. The certificate supplies actual times, controllers, packed rows, true lengths and caps, so their directory costs $H^{y+o(1)}$ words including rounding. The checker validates ranges before using these fields and makes every capped decoder into a total deterministic word function. On honest guesses its clock bounds hold for every address. Time zero uses genuine zero memory. [Complete endpoint comparison and sparse overlays](solver-snapshot-descriptions.md)

## One audit with public logs for the expensive segments

Assume $W(e,d)$ with $1\le e\le d$. Call a selected interval expensive when its *starting* decoder cap exceeds $w$. The sum-of-caps bound gives at most $H^{y+o(1)}/w$ expensive intervals. The outer certificate includes $O(w)$ words for each such interval, allowing a proposed value for each possible work-read slot in time order. The whole collection costs $H^{y+o(1)}$ words. The checker can validate all layout sizes and offsets in the stated directory and log budget.

One nondeterministic defect witness chooses a segment. For an ordinary segment replay from its starting row, with local writes overriding that row. It uses $O(w^2)$ decoder and simulation steps. In an expensive segment, replay using the logged values for reads that require the starting row, at a cost of $O(w)$ steps. The checker can additionally select any read slot of that tentative replay. If the slot required a starting-row value, compare its logged answer to a single genuine evaluation of the proposed starting decoder. Independently compare the ending controller and, for any chosen address at an internal endpoint, compare its final value to the proposed ending decoder. Obtaining the final value for a word untouched in the segment can require one further start evaluation. These additional evaluations each take at most $H^{y+o(1)}$ steps. Check genuine initial conditions and a final UNSAT signal.

On an honest history no defect exists. Conversely, if an expensive tentative replay used a wrong logged value, that slot supplies a defect even if later control has diverged. In the absence of such a defect all tentative reads agree with the starting configuration. Determinism identifies the whole segment. The arbitrary-address check then identifies its entire ending memory, including words never read in the segment. Induction over segments proves a true UNSAT signal. Every logged interval is available to the defect machine from the outer public data.

The defect machine has clock $H^{\max(2x,y)+o(1)}$ and public input $m+H^{y+o(1)}$. Its nonacceptance can be certified using $W(e,d)$. Take
$$
 x=\frac{cd}{d+2e},\qquad
 e'=\frac{2cde}{d+2e}.
$$
Here $x\ge c/3$ so $2x\ge y$, and $2xe=dy$. The guess cost is included since $d\ge1$. We obtain $W(e',d)$, using $e'\le d$ to absorb the part contributed by $H=m$. Starting from $e=d$, these exponents decrease to $d(c-1/2)$ for $c<3/2$. Indeed the update is increasing on positive arguments, has this fixed point, and is strictly below its argument above the fixed point. If an iterate drops below one the hierarchy contradiction already follows. Otherwise, for every fixed $E>d(c-1/2)$ sufficiently near this limit we obtain $W(E,d)$ after finitely many applications.

## Using this public-input exponent in the batched audit

Choose $E\ge1$ as above and set $b=dE$. Weakening the public-input exponent gives $W(E,b)$. Assume now $W(e,b)$ with $1\le e\le E$, so $b\ge de$. The outer certificate guesses the ordinary checkpoint rows. An existential defect witness tentatively replays a segment by guessing its starting-row read answers and the proposed answer to any endpoint query it needs. This gives $O(w)$ read records containing row, address and answer. It requires an actual failure of the controller, endpoint word or verdict test. To admit the defect, all the tentative decoder answers must agree with their claimed rows.

Take $x\ge y$ and put $U=\max(m,\lceil H^{y+o(1)}\rceil,1)$, where the upper bound used covers the full directory, all row data and the maximum selected query cap. Divide the log into contiguous groups of at most $U$ records. For each group the assertion that some record has a wrong answer is one bounded nondeterministic query. Select its record, evaluate its one decoder and compare. Both public input and query time are $U^{1+o(1)}$. The base UNSAT reference certifies no wrong entry for each group in $U^{d+o(1)}$ time. The outer defect machine guesses and runs the successful certificates sequentially for *all* the groups. Its public input from the preceding checkpoint choice still has size $m+H^{y+o(1)}$ because it guesses its own $O(w)$ tentative log internally. Its clock is
$$
 (wU^{d-1}+U^d)H^{o(1)}.
$$
Enforce the bounded reference clock on every branch. A false read in any group prevents an accepted defect of this type. Genuine mismatches admit the true log followed by successful group certificates. Thus nonacceptance of the outer defect machine has the requisite sign. [Batched decoder audits](first-moment-snapshot-audits.md)

Apply $W(e,b)$ to this outer defect machine, choosing
$$
 y=\frac{ce}{b+(2-d)e},\qquad x=c-y,\qquad
 e'=by=\frac{cbe}{b+(2-d)e}.
$$
The assumption $b\ge de$ implies $x\ge y$ and $xe=(b-(d-1)e)y$. If $m\le H^y$, this identity bounds the simulated time exponent by $e'$, up to the subpolynomial slack. If $m\ge H^y$, then $H^{xe}m^{(d-1)e}\le m^b$ and $m^{de}\le m^b$. This proves $W(e',b)$ including the transition region where $m$ is neither small nor comparable to $H$. As $cd<2$, the first update from $e=E$ gives $cdE/2<E$. The subsequent iterates decrease to $b(c-1)/(2-d)$. Condition (1) permits choosing $E$ sufficiently close to $d(c-1/2)$ that this limit is strictly below one.

Only a fixed finite number of invocations is needed for any strict interior parameter choice. Small rational slack in all guess and simulation clocks therefore preserves a final exponent below one. Apply the resulting $W(e,b)$ with $e<1$ to a bounded universal nondeterministic interpreter of clock $R=n_0^k$ for a fixed $k>b$ on $m=O(n_0)$ public words. A timely nondeterministic certificate of its own nonacceptance on its padded program would contradict its signed acceptance criterion. This is the same finite-depth complementary diagonal used by the base audit. The argument gives an exponent bound on the snapshot cost on unsatisfiable inputs. A deterministic solver can take linear time while accumulating a superlinear sum of these costs. [Signed diagonal](packed-band-transfer.md)

At $c=d=11/8$, four one-level updates from $e=d$ yield $161051/133568<309/256$. Use $E=309/256$ and $b=3399/2048$. Twelve batched updates starting at $E$ yield $10667518052474679/10671453758437376<1$. These exact rationals give slack for the bounded-clock implementation. [Exact mixed calculation in Lean](../lean/FirstMomentSnapshotTrade.lean) The limiting root $s_0$ itself does not follow from these fixed-depth strict inequalities.

## Boundary of the two cost calculations

Here is a separate numerical statement about the two cost estimates. In a scalar game start with time exponent $r=1$ and public exponent $m=0$. All exponents are nonnegative. At each move choose $v\ge m$ as the new public exponent and set $m'=v$. The two choices of charge for the new time exponent are
$$
 \begin{array}{ll}
 \text{public-log move} &r'\ge\min\{cr,\ 2(cr-v)\},\\
 \text{batched move} &r'\ge\max\{cr-(2-d)v,\ dv\}.
 \end{array}
$$
Success means reaching $d\max(r,m)<1$. Since the public exponent never decreases, every move on a winning sequence has $v<1/d$. The zero initial public exponent makes the barrier apply even with a negligible initial input. The minimum in the first charge includes the option of simply replaying at the full $cr$ exponent.

These charges relax the displayed estimates when read as exponent rules. For a public-log move allow the window width and high-latency threshold to have different exponents $x$ and $z$ in the initial scale. Write $h=\max(r,m)$ for the current source scale. The row estimate is $ch-x$. When $z\le ch-x$, charging the estimated high logs gives public exponent at least $ch-z$ as well. The light replay estimate $x+z$ is then at least $2(ch-v)$. When $z>ch-x$, the whole selected cap bound fits below threshold, and the direct light-replay estimate is $x+(ch-x)=ch$ for $x\le ch$. A window beyond the whole clock also permits the full replay estimate. In both cases the game uses only the weaker bound with $cr$. If the previous public input dominates the new rows, this merely increases $v$ in the first charge. For a batched move using the stated common packet size, the directory and inherited input give $v=\max(m,ch-x,0)$ up to exponent slack. The charged time is at least $dv$ and $x+(d-1)v$. Hence it is at least $cr-(2-d)v$. For a larger declared packet or public budget the game describes a relaxation with the same paired charges when that declared width is used for the packets. These numerical comparisons impose no lower bound on the cost of a different compiler or on an individual run.

Put $\alpha=(c-1)/(2-d)$ and $\rho=d\alpha$. For $cd<2$ one has $\rho<1$ and $\alpha\le c-1/2$. The latter follows from $c(d-1)\le d/2$, since $c<2/d$ and $4(d-1)\le d^2$. Until the public exponent reaches $\alpha$, a current $r\ge1$ remains at least one. For the public-log move both options are at least one, since $c\ge1$ and $2(c-\alpha)\ge1$. A batched move gives $c-(2-d)\alpha=1$. Suppose now that $d^2(c-1/2)(c-1)\ge2-d$. At the first and every subsequent stage with $v\ge\alpha$, the condition $r\ge\rho$ is preserved. A batch costs at least $d v\ge\rho$ and a public-log step costs at least $\min(c\rho,2(c\rho-1/d))\ge\rho$. The last inequality is precisely the assumed parameter condition. Finally $d\rho\ge1/(c-1/2)>1$ since $c<3/2$. Neither phase can terminate in a raw call of exponent below one. This barrier concerns the scalar game only.
