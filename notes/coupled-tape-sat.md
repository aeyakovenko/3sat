# SAT on several geometric work tapes with occasional distant heads

Let a deterministic machine have random read access to an explicit input of $N$ bits, a fixed number $h$ of initially blank, separately writable $d$-dimensional tapes, and writable random-access scratch. Each tape has one nearest-neighbor head. One instruction can use all the scanned words simultaneously, a constant number of scratch words and the finite collection of logarithmic-width registers. Tape cells may hold logarithmic-width words. Assume that the machine eventually signals UNSAT on every unsatisfiable formula and that every signal is sound. The moving-head version below also covers several heads sharing a tape.

On a run through its first negative signal write $T$ for the number of instructions, $p_i(t)$ for the position of head $i$ before instruction $t$, and $S_t$ for the number of nonzero scratch words at that time. Use head 1 as the anchor. Define
$$
 A=\sum_{0\le t<T}(1+S_t),\qquad
 M=\sum_{1\le t<T:\ p_1(t)\ne p_1(t-1)}(1+S_t),\qquad
 \Delta_t=\sum_{i=2}^h\|p_i(t)-p_1(t)\|_1.
$$
Coordinates on different tapes are compared in their respective standard frames. The read-only input has its own independent random-access port.

**Theorem.** Suppose that on each negative run there exists a set $F$ of exceptional times. For fixed nonnegative exponents suppose
$$
 A=O((T+1)^{1+\omega}),\quad M=O((T+1)^{1+\rho}),\quad
 |F|=O((T+1)^\beta),\quad
 \sum_{t\notin F}\Delta_t=O((T+1)^{1+\eta}).
$$
Set $s=\max(\rho,\eta)$. These bounds exclude $T=O(N^c)$ for $c\ge1$ whenever
$$
 (d+1+ds)c^2<c+d+1,\qquad (1+\omega)c^2<c+1,\qquad \beta c^2<1. \tag{1}
$$
With no exceptional times the third condition is unnecessary. In particular, scratch occupancy and head separation can both average $O(T^s)$, with no bound on the space of any geometric tape, throughout the mixed-tape curve $(d+1+ds)c^2<c+d+1$ for $0\le s<1/d$. For this specialization $\rho\le\omega=s$ and the occupancy test follows from the geometric one. Indeed, if $(1+s)c^2\ge c+1$, then $(d+1+ds)c^2\ge d(c+1)+c^2\ge c+d+1$ for $c\ge1$.

For two planar work tapes take $c=11/10$, $\rho=\eta=1/8$, $\omega=2/3$ and $\beta=4/5$. In (1) the left sides are $1573/400$, $121/60$ and $121/125$, all strictly below $41/10$, $21/10$ and $1$. The heads can visit and retain linearly many distinct tape cells together. While the anchor is stationary, the other head can make a round trip of length $\Theta(T^{4/5})$. This single permitted excursion yields a total separation of order $T^{8/5}$, so its full-run average separation is of order $T^{3/5}$. The scratch can also hold $\Theta(T^{2/3})$ words during the excursion. These are compatible resource usages of sample trajectories. The theorem concerns machines solving SAT within the stated bounds on all negative inputs.

## Remote reads without copying the scratch at remote times

Take side $u\ge1$ and group size $b\ge1$. Use the same uniformly shifted cubical grid on every tape. The anchor owns the execution of each instruction. For each other head lying outside the anchor cube at time $t$, give a record containing time, head number, position, symbol read, and resulting symbol after the instruction. Represent a no-write by the unchanged symbol. The probability that two specified heads lie in different cubes is at most $\min(1,\|p_i(t)-p_1(t)\|_1/u)$ by the coordinate union bound. Define
$$
 D(u)=\sum_{t<T}\sum_{i=2}^h\min(1,\|p_i(t)-p_1(t)\|_1/u).
$$
The expected number of remote records is at most $D(u)$. Each anchor move changes cube with probability $1/u$. Its chronological boundary needs a full shared controller and scratch snapshot; the expected total of those costs is $O(M/u)$. A remote head can stay outside for many consecutive instructions while the primary computation continues in one uninterrupted interval. Its records each carry just its own read and write.

List, for each cube, the times at which it owns the anchor or has at least one remote head. Combine all events at the same cube and time into one occurrence. There are at most $hT$ occurrences. Break each cube's list into groups of at most $b$, cutting just before a nonfirst occurrence whose zero-based rank has a chosen residue modulo $b$. Conditional on the grid, a uniform residue starts a group at any particular nonfirst occurrence with probability $1/b$. At each internal group boundary share the complete state of the $h$ tape tracks in that cube. This costs $O_h(u^dT/b)$ words in expectation.

Chronological intervals of anchor instructions end where the anchor changes cubes or changes group inside a cube. If consecutive instructions have the same anchor cube, their two anchor occurrences are consecutive in its list. The additional expected cost of copying their controller and scratch at a group change is at most $O(A/b)$. The initial scratch is zero and the final signal needs only its controller. Summing expectations and fixing both choices yields a chart of
$$
 Y=O_{h,d}\big(1+M/u+(A+u^dT)/b+D(u)\big) \tag{2}
$$
words. Coordinates and record indices use logarithmic width. Equation (2) charges a remote head and an anchor change separately even when the scratch is large.

The chart gives a chronological partition into labeled primary intervals, shared controller/scratch records at internal interval boundaries, remote records indexed by time and head, and all internal cube states. Group the primary intervals and remote records by cube and group in increasing chronological order. Verify coverage and uniqueness, group lengths using the sum of interval lengths and the number of distinct satellite-only times, all chronological and group endpoints, sorted sparse scratch snapshots and the proposed signal. These structural tests sort compressed intervals and individual remote records. They use $O((1+Y)\operatorname{polylog}(N+T+2))$ time; they never expand all primary intervals.

A defect test chooses one cube group. Preserve its complete local state across all its occurrences. At each primary interval, initialize its controller and scratch from the unique chronological boundary. Simulate the instructions. Check each head's position before moving and determine from it which read values come from the cube and which must come from the directory. Require the remote record set at that time to be exactly the set of remote heads, with matching positions. Compute the transition using all those reads and the actual immutable input. Apply local writes, compare all computed remote writes with their records, and check the resulting control and scratch at the interval end. At a satellite-only occurrence, check every listed pre-write value against the actual local state of that head's tape, then apply its listed write. The structural tests require that every remote record is delivered to its coordinate's cube and that its time lies outside that cube's primary intervals. Reject any continuation past an earlier signal or halt. Shared cube endpoints are checked on both sides. Initialization of a fresh cube can be implicit, and an ending full cube need only be scanned when an explicit record was supplied. Scratch dictionaries are reset per primary interval and compared as complete sparse maps. Summed over one group, opening and checking its supplied snapshots costs $O(Y)$ word operations up to logarithmic factors. At most $b$ primary or satellite occurrences are replayed.

If no defect is found, induction over true chronological time identifies every replayed state with the genuine state. The anchor control and scratch arrive from the preceding instruction or the shared boundary. Every scanned word comes from the unique cube maintaining that tape location. For a remote head its cube has authenticated the read value and the anchor has verified the matching transition and resulting write. Each simultaneous instruction thus produces the genuine next controller and the genuine updates on all tracks. This includes instructions branching jointly on several remote reads. The challenge costs $(1+b+Y)\operatorname{polylog}(N+T+2)$ and the honest trace always passes. Lean checks the simultaneous transition gluing after the local chains have been verified. [Simultaneous read/write lemma](../lean/CoupledTapeSteps.lean)

## Only moving satellite heads need tape records

There is a stronger version of (1). Replace $\Delta_t$ in its hypothesis by
$$
 \Delta_t^{\rm move}=
 \sum_{i\ge2:\,p_i(t+1)\ne p_i(t)}
 \big(\|p_i(t)-p_1(t)\|_1+\|p_i(t+1)-p_1(t)\|_1\big).
$$
Take $p_i(T)$ after the last prescribed move. Omitting a final move after a halt is harmless. Since the heads move at most one unit, $\Delta_t^{\rm move}\le2\Delta_t+h-1$. The stronger version permits $\sum_t\Delta_t=\Theta(T^2)$ even with $\Delta_t^{\rm move}=0$ throughout a long phase: one head can stay still, supplying and changing its symbol on every step, while the anchor moves away. Both tapes can first accumulate linearly many symbols together.

For each satellite maintain the current scanned symbol in one controller register, initially blank. For each instruction read its cached symbol and compute its written symbol, move, next controller and scratch behavior according to the original transition. When the head stays, simply update the cached symbol. When it moves, write the updated symbol to the departure cell and load its neighbor's actual symbol into the register. At every time the backing tape agrees with the true tape off the current cell, and the register contains the true symbol at that cell. This proves the transformation for arbitrary sequences of overwrites, repeated visits and simultaneous transitions. The tapes are separate, so no other head can access a parked head's unflushed cell. [Lean cache invariant](../lean/CoupledTapeSteps.lean)

Use constantly many microsteps per instruction. Hold the anchor in its original cube through the satellite flush and fetch phases, then commit its own move. Treat unused tape ports as inactive, regardless of their positions. The primary checker enforces the active ports and operations implied by its controller. A remote write record names its destination and outgoing value; its owning cube applies it. A remote fetch record names its source and value; its owning cube authenticates it before the register uses it. Primary tape updates use the anchor's local cube. Satellite flushes and fetches occur in fixed order and their respective addresses are determined by the instruction and cached input symbols. At the constant-factor expanded clock the charges for anchor changes remain $O(M)$ and the time-summed scratch cost is $O(A+T)$, since an instruction changes only constantly many scratch words. The remote part of (2) is now at most the sum of each moving satellite's two clipped distances divided by $u$ before clipping, namely
$$
 \sum_{t,i\ge2:\,p_i(t+1)\ne p_i(t)}
 \sum_{z\in (p_i(t),p_i(t+1))}
       \min(1,\|z-p_1(t)\|_1/u).
$$
The notation in the inner sum lists the departure and arrival separately. This gives the same exponent transfer. A stationary satellite can branch on its current symbol and overwrite it for arbitrarily long periods with no remote records.

The movement-only theorem also permits a fixed number of heads to share a physical tape when its simultaneous-write collision rule is fixed and computable in constant word operations. Cache one symbol per distinct occupied physical address, keyed by tape identifier and coordinates. The controller knows all head positions. At time $t$, process the complete tuple of scanned symbols and resolve all writes to each occupied location using the specified rule. If $U$ and $V$ are the sets of occupied physical addresses just before and after the move, flush updated values at $U\setminus V$, carry the updated values at $U\cap V$, and fetch backing words only at $V\setminus U$. Every flush or fetch can be charged to the departure or arrival of a moving head. At a position occupied at both times, a collision or exchange of two heads preserves the same logical word. Decoding the backing array with the occupied cache overlaid thus gives the correct updated tape everywhere. The fixed-size map and all coordinate comparisons cost constantly many words and operations at fixed $h,d$. Include the anchor in this cache when it shares a tape. Its departure is local and any remote fetch at its neighboring arrival adds at most one expected record per $u$ actual anchor moves. The charge is $O(M/u+1)$, including the last move. Satellite-only group replays now update the track for the physical tape. Separate flush and fetch phases preserve the prescribed event order. [Shared-cache handoff in Lean](../lean/CoupledTapeSteps.lean)

## Exponent transfer

Use the uniform bounded-nonacceptance assertion $B(e,c)$ and packed compiler of the existing one-tape proof. With source clock $R$, public words $m$ and $H=\max(2,R,m)$, $B(e,c)$ gives a nondeterministic nonacceptance certificate in $(R^e+m^c+1)H^{o(1)}$ steps. The SAT hypothesis gives $B(c,c)$ by running the solver on the genuine ordinary 3-CNF of length $H^{1+o(1)}$. On a true negative source the local verifier above describes a run of length $T\le H^{c+o(1)}$. A general RAM can simulate the fixed number of geometric tapes by sparse dictionaries for this baseline, and can look up the packed reduction from the inherited source in the chart replay. [Compiler and diagonal](packed-band-transfer.md) · [One-tape resource accounting](hybrid-tape-cut-trading.md)

For a clean finite iteration put $\alpha=1/(d+1)$ and $p=c(1+ds/(d+1))$. The strict tests in (1) say precisely that
$$p-\alpha<1/c,\quad c(1+\omega)-1<1/c,\quad c\beta<1/c.$$
Choose a fixed rational $x<1$ sufficiently close to $1$ that $p-\alpha x<x/c$, $c(1+\omega)-x<x/c$, and $c\beta<x/c$. Use $b=H^{x+o(1)}$ and $u=H^{(cs+x)/(d+1)+o(1)}$. The exceptional times contribute $O_h(T^\beta)$ remote records and the remaining ones contribute $O(T^{1+\eta}/u)$ in (2). The spatial terms $H^{c(1+s)}/u$ and $u^dH^c/b$ have exponent $p-\alpha x$. Thus the chart uses $H^{x/c+o(1)}$ words and the defect search uses $H^{x+o(1)}$ time. Whenever $1\le e\le c$, guess that chart and apply $B(e,c)$ to absence of a defect with $O(m+H^{x/c+o(1)})$ physical public words. Its cost gives $B(ex,c)$ since $(x/c)c=x\le ex$; when $H=m>R$ the $m^c$ term covers $H^{ex}$. On short honest runs direct replay through the claimed signal suffices. Fixed rational margins absorb integer clocks and the finite uniform simulations. Start at $e=c$ and iterate this same step finitely often until $ex<1$. The complementary native diagonal with $R=n_0^D$, $m=O(n_0)$ and fixed $D>c$ contradicts the resulting subclock nonacceptance certificate. The constant-power SAT time exclusion follows.

The finite audit tests 8,124 path and parameter combinations, 70,620 shifted-grid and rank-residue choices, and 5,832 cached joint runs each for separate and shared tapes. It includes collisions and exchanges of head positions. The lower bound and exponent transfer have manuscript proofs.

The shifted-grid calculation for several heads was already used in the journal's separator for two-plane grates. Van Melkebeek and Raz proved the original one-tape SAT lower bound, Williams strengthened it for one tape with subpolynomial scratch, and Bečvář discussed simulation for one-dimensional heads at constant distance. The additional accounting here uses one controller/scratch chronology and individually verified simultaneous reads and writes on the other tapes, with clipping for exceptional times and charges for moving satellites alone. Historical priority for (1) is unverified. The proof supplies a restricted multitape separation. A fully random-access machine has no geometric condition forcing a comparable small chart. [Earlier geometric separator](spatial-grate-simulation.md) · [van Melkebeek and Raz](https://pages.cs.wisc.edu/~dieter/Research/sat-t.html) · [Williams, §7](https://people.csail.mit.edu/rrw/automated-lbs.pdf) · [Bečvář, §7](https://www.kybernetika.cz/content/1965/6/475/paper.pdf) · [Finite chart accounting](../audits/coupled_tape_audit.py)
