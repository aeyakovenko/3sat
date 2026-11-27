# Fast binary-time prediction when one feedback bank has a single tap

Let $a>0$, let $R$ be a finite set of positive integer delays, and specify all the ones at negative times by a finite set $S$. Consider the Boolean recurrence
$$
                  z_t=z_{t-a}\mathbin{\wedge}
                           \left(\bigoplus_{b\in R}z_{t-b}\right),
                     \qquad t\ge0 .
$$
Given $a,R,S$ and a horizon $H\ge0$ in binary, $z_H$ can be computed in deterministic time polynomial in the encoded input length. Both the singleton lag $a$ and every lag in the other bank may be large. For fixed numbers of seeds and taps the algorithm takes a constant number of binary arithmetic operations on integers of $O(B)$ bits, where $B$ is the maximum input integer length. A sharper ordinary linear bit clock applies to the fixed sampling family below. The two banks may overlap in this upper bound.

## Predicting the first time a progression stops

A zero at $t-a$ forces a zero at $t$. Each potentially live nonnegative residue $r\in[0,a)$ therefore starts at $r$ with $r-a\in S$. Its ones form an initial segment of $r,r+a,r+2a,\dots$. Only $k=|S|$ residues can start, and each can end once. A residue can fail at its very first point.

Keep the previously ended segments. Extend each still-live segment provisionally through $H$. To find the first genuine disagreement with this provisional sequence, consider times $t=r+aj$ on a live residue, from the current time up to $H$. For a fixed tap $b$ there are two contributions to its predicted bit.

* Every negative seed $s$ contributes exactly at $t=b+s$, when that time belongs to this progression and the search interval.
* A nonnegative one must belong to the unique residue $r'=(r-b)\bmod a$. If that segment exists, shifting its two endpoints by $b$ gives an interval of integer $j$'s. If the segment is empty, it contributes nothing.

Clip these intervals and singleton hits to the range being tested. Sort their start and end-plus-one events and accumulate their parity. This finds the first $t$ on this progression at which the other bank would be zero. Choose the earliest such $t$ over all live progressions. Every earlier provisional value agrees with the recurrence, since the input times of every tap are strictly earlier than its output. Thus the selected progression ends immediately before $t$. Set its last allowed time to $t-a$, retire it, and continue from $t+1$. If there is no event producing a zero, the provisional answers through $H$ are genuine. Residues already ended remain zero by the singleton factor.

There are at most $k+1$ rounds, at most $k$ live residues per round and at most $|R|(k+1)$ contributing intervals per residue. Only their endpoints require arithmetic, comparisons, sorting and integer division. Signed seed and lag sums and all clipped endpoints use $O(B)$ bits; products of intermediate $O(B)$-bit values also use $O(B)$ bits. In particular fixed $k,|R|$ give quasi-linear bit time with fast integer arithmetic. The algorithm needs no array indexed by $a$, $\max R$, or $H$.

## A fixed-rule linear bit clock

Write $D=\max(\{a\}\cup R)$. After any search restart at time $u$, suppose there is no death during $[u,u+D+a)$. On this interval the provisional sequence depends only on the residue modulo $a$. The windows $[u,u+D)$ and $[u+a,u+a+D)$ consequently agree. Determinism and the $D$-step memory imply that the rest of the sequence repeats with period $a$. Otherwise a death occurs before $u+D+a$ and the next search starts at most $D+a$ ticks after $u$. After at most $k$ deaths, every time from $(k+1)(D+a)$ onward therefore follows a period dividing $a$. This bound concerns stabilization; the endpoint algorithm reaches its answer independently of the numerical size of this bound.

For the sampling problem where $W$ is the whole input, fix the seeds at fixed negative offsets, the tap layout except for a single tap occurrence of positive lag $cW+c'$ (its opposite bank contains only fixed taps when it is the singleton), and the observation $H(W)=bW^5+s$ with fixed positive $b,c$ and fixed integers $s,c'$. Then **$O(|\operatorname{bin}W|)$ deterministic bit time suffices whenever either bank is a singleton**.

* If the singleton lag grows, let $M=\max(\{-s:s\in S\}\cup\{0\})$ and bound the fixed opposite lags by $d_0$. The earliest possible produced one must see a seed in both banks. Its time is at least $a-M$ from the singleton bank and at most $d_0-1$ from the other. For all sufficiently large $W$ these intervals are disjoint, so every future bit is zero.
* If $a$ is fixed, form $C=(k+1)(D+a)$ with a constant number of additions and fixed multiplications. For sufficiently large $W$, $H(W)\ge C$. Use the endpoint algorithm on $C+((H(W)-C)\bmod a)$, which has the same bit by stabilization. Computing $H(W)\bmod a$ requires just $W\bmod a$ and a fixed-size calculation. All divisions and variable-by-constant multiplications in the endpoint algorithm now use the fixed $a$, and there are only constantly many events. Linear bit scans suffice. The finite initial exceptions in $W$ can be handled separately.

In the homogeneous two-bank simulation this rules out a one-tap operand even if its partner has arbitrarily many fixed taps. With both banks disjoint, at most one initial one also forces all later bits to zero by the first-event argument. Multiple operand taps and enough initial support enter different steps of the simulation.

Lean verifies propagation of zeros on the singleton residue chain and indefinite periodicity once the two windows agree. The endpoint algorithm and its asymptotic bounds are manuscript arguments. The audit compares 31,500 exact small predictions with direct trajectories, checks several-thousand-bit horizons and lags, and checks the stabilized observation clock. [Lean lemmas](../lean/SingletonTapFeedback.lean) · [Binary endpoint implementation and finite audit](../audits/singleton_tap_feedback_audit.py) · [Two-bank collision and singleton-seed proofs](../lean/SingleProductFeedback.lean)
