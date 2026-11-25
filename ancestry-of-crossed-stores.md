# A polynomial bound on the cells written by a repeated crossed scan

Let $S$ be a permutation of a finite word domain, start at $p_0$, and put $p_i=S^i(p_0)$. Let $L$ be the period of $p_0$. At opportunity $i$ the scan reads $x_i=M[p_i]$ and writes $M[x_i]\gets p_{i+\delta}$ with a fixed $\delta\in\{0,1\}$. An exit can truncate the run after a read and before its write. Let $H$ be the image of initial memory, enlarged by the payload of any single prologue store. Write $h=|H|$. If $m$ reads execute and $P=\lceil m/L\rceil$, the total number of distinct STORE destinations, including the prologue, is at most

$$1+(P+1)^2 h.$$

The count includes writes of the original value, overwritten changes, and addresses outside the orbit. It allows any memory after initialization, provided its image is included in $H$. [Public scan in the five-slot machine](public-scan-crossed-stores-on-ordinary-sat.md)

## Last writers

Associate the ordered pair $e_i=(p_i,x_i)$ to each read. If there was no scan write to $p_i$ before its read, $x_i\in H$. This includes the possible single write before the scan. Otherwise let $j<i$ be the last writer. Its destination was $x_j=p_i$, and its payload was $S^\delta(p_j)=x_i$. Thus

$$e_i=F(e_j),\qquad F(a,b)=(b,S^\delta(a)).$$

Following last writers strictly decreases the event index. Each pair arises from a root $(a,h')$ with $h'\in H$ by a chain of $F$ steps. The actual provenance is valid even when a write reproduced the previous value.

If $\delta=0$, $F$ just exchanges coordinates, so every pair meets $H$. If $\delta=1$, $F^2(a,b)=(S(a),S(b))$. On a chain of two links from index $u$ to $v$, it follows that $p_v=p_{u+1}$. Therefore $v-u\equiv1\pmod L$, and the two strict increases in time give $v-u\ge2$. Together these imply $v-u\ge L+1$, including $L=1$. This argument counts scan indices even across wraparound. For a chain of length $t$, grouping its links in pairs yields $\lfloor t/2\rfloor(L+1)\le m-1$. For $m>0$, this implies $\lceil t/2\rceil\le P$. In $t$ applications of $F$, the root coordinate $h'$ advances at most $\lceil t/2\rceil$ applications of $S$ and remains one of the two coordinates. Every read pair therefore meets

$$U=\bigcup_{s=0}^P S^s(H),\qquad |U|\le(P+1)h.$$

This set also contains the required root coordinate for $\delta=0$. STORE destinations in $U$ contribute at most $|U|$. A destination $x_i$ outside $U$ requires $p_i\in U$. Every address is read at most $P$ times in the first $m$ reads, so these destinations contribute at most $P|U|$. Adding the possible prologue proves the bound. For $m=0$ only the prologue could write. In the unshifted case one can use $U=H$ throughout. [Lean proofs of endpoint transport, index gaps, accumulated spans and the destination bound](CrossedScanAncestry.lean)

## Adaptive writes and the boundary at two-address lookahead

The same bound holds when the controller may skip any write or choose its offset $\delta_i\in\{0,1\}$ at the time of the write. Last writers still determine a chain, now with a separate map $F_i(a,b)=(b,S^{\delta_i}(a))$ for each ancestor. Over two links starting at $u$ and ending at $v$, the scan positions satisfy $p_v=S^{\delta_u}(p_u)$. If $\delta_u=0$, the strict separation of the event indices gives $v-u\ge L$. If $\delta_u=1$, it gives $v-u\ge L+1$. Thus $\lfloor t/2\rfloor L\le m-1$ on every chain, which again implies $\lceil t/2\rceil\le P$. A root coordinate can advance by at most one in each pair of links, and by at most one on the unmatched link. Hence every pair still meets $U$.

Allowing offset two gives a counterexample for every orbit size $L$. Scan the integers modulo $L$ in order from zero, initialize every cell to one, and always set $M[x_i]\gets p_{i+2}$. The first read returns one. Inductively $x_i=p_{i+1}$, since its store places $p_{i+2}$ at the next read location. A single pass writes all $L$ addresses with an initial alphabet of size one, changing $L-1$ distinct cells from their original value. Thus a second increment available as a STORE payload can destroy the sparse-memory conclusion.

## Consequence for the five-instruction DIMACS RAM

For the remaining public scan in the five-instruction reduction, $S(a)=a+d\bmod 2^w$ with a fixed nonzero integer $d$. At sufficiently large lengths $L\ge2^w/|d|\ge N/|d|$. A clock $O(N^{11/10})$ therefore gives $P=O_d(N^{1/10})$ and $O_d(N^{0.711})$ distinct writes on the virtual DIMACS instances, using $h=O(N^{0.511})$. Maintaining an address trie and generating original input words on demand costs a polylogarithmic factor in time and space. By Theorem 3.3 of the cited paper a nondeterministic linear-time random-access Turing machine first has a quasilinear-time nondeterministic multitape simulator. Its transitions have locally indexed bounded-run clauses. Starting from such a language on inputs of length $n$, the virtual 3-CNF has $N=n\,\log^{O(1)}n$ bits up to a constant-factor upper bound. The resulting random-access Turing machine would run in time $O(n^{1.101})$ and space $O(n^{0.712})$.

Corollary 5.8 of Fortnow, Lipton, van Melkebeek and Viglas excludes a deterministic simulation of nondeterministic linear time in $O(n^c)$ time and $o(n^{((c+2)/c^2-c)/2})$ space. At $c=1.101$ the forbidden space exponent exceeds $0.728$. The other cases in the five-instruction classification either use $O(h+1)$ stored values, miss an essential cell, or require $\Omega(N^2/\operatorname{polylog}N)$ time on the explicit periodic family. Consequently no correct program with at most five instructions in that model runs in $O(N^{11/10})$ on all ordinary DIMACS instances. [Primary theorem, Corollary 5.8](https://lance.fortnow.com/papers/files/tst.pdf) · [Machine and remaining cases](five-instruction-loops-on-dimacs-sat.md) · [Finite ancestry audit](crossed_scan_ancestry_audit.py)
