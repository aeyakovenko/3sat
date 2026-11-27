# A shifted crossed scan with a long transient on valid DIMACS

Changing the payload of the [unshifted scan](unshifted-crossed-scan-without-a-clock.md) from the current address to the next address changes the number of passes before the memory repeats. Even when the initial memory contains only three distinct values, the uninterrupted shifted scan has distinct boundary states for at least $\lfloor 2^w/512\rfloor$ full passes on valid one-clause DIMACS inputs. This is an example for the actual separate LOAD, increment and STORE instructions. Comparison branches in a SAT program could exit the loop earlier.

## The file

Take an arbitrarily large width $w$ divisible by 16, $Q=2^w$, $m=\lfloor Q/(2w)\rfloor$ and $n=mw$. The prescribed width $16\lceil\log_2(n+2)/16\rceil$ is exactly $w$ for all sufficiently large choices. Use one little-endian word beginning with the header `p cnf 3 1`, a newline and the clause `1 2 3 0`. Pad with spaces up to its final byte and put a newline in that byte. Call this word $B$. Fill all remaining $m-1$ input words with ASCII spaces and call the resulting common word $A$. The entire file is a satisfiable proper 3-CNF. The high bytes of $B,A$ are 10 and 32 respectively. For large widths $m\ll B<A<Q-1$, where here $m/B\to0$. The remaining physical memory contains zero.

Start the cursor at zero. For $p=0,1,\ldots,Q-1$ in cyclic order read $x=M[p]$ and write $M[x]\gets(p+1)\bmod Q$. A period is one complete scan starting at zero. Write $M_t$ for the memory after $t$ periods.

## Propagation in one period

Let $U_t$ be the union of the three integer intervals
$$
 [0,m-1+t],\qquad [B,B+t],\qquad [A,A+t].
$$
For $0\le t\le \lfloor Q/512\rfloor$ these intervals are disjoint and avoid $Q-1$. At each such boundary, every nonzero entry of $M_t$ has both its address and its value in $U_t$.

For induction, if a read of a nonzero $x$ at $p$ uses a write from the same period, let $r<p$ be its writer. That writer read $p$ and wrote $r+1$ there. The writer's own read of $p$ could not have come from a preceding write at $s<r$, as that would require $p=s+1$ with $s<r<p$. Thus every such forwarded read comes directly from an initial pair of this period. Initial nonzero pairs and pairs forwarded once can introduce only a successor of an existing position or value in $U_t$. A read of zero writes only at address zero, which is never read again in the period. At $Q-1$ the read is zero by the same bound on nonzero reads, so the final write resets address zero. The nonzero entries at the next boundary therefore use only $U_{t+1}$.

## Two unique values

At every indicated boundary $t\ge1$, put $a=m+t-1$ and $h=A+t$. Then
$$
 M_t[a]=h,\qquad M_t[h-1]=a.
$$
Each of $a$ and $h$ occurs exactly once as a memory value. In particular each period exhibits a value absent at all earlier boundaries.

For the first period set $a=m-1$ and $h=A$ temporarily. At $a$ the last original space word is read, and its write at $h$ has payload $a+1$. Until $h$ there are no more initial occurrences of $h$, and the only step that produces $h$ as a payload is $h-1$. A newly written copy at that step cannot itself be read strictly between $h-1$ and $h$. The step at $h-1$ does not read $h$. Consequently the read at $h$ sees $a+1$ and writes $h+1$ at $a+1$.

The same two writes occur on every subsequent induction step. At its start $h$ occurs only at $a$, and $a$ occurs only at $h-1>a$. Until reaching $a$, no read can return $a$, since its only new production would be the write at $a-1$ and there is no intermediate index before $a$. Thus the read at $a$ still sees $h$. The same reasoning near $h$ gives the following read at $h$ just as in the first period. In the first period there is no original occurrence of $a$, and the original occurrences of $h$ are all at or before $a$, which are the only weaker facts the argument needs.

In both cases $a+1$ and $h+1$ were absent as values at the beginning of this period. Each is written just once. A later read cannot give $a+1$ after position $h$, since the sole source was the write into $h$ at $a$. Thus $M[a+1]=h+1$ persists. To erase $M[h]=a+1$ after position $h$ would require a later read of $h$. Its new production at $h-1$ was to an address at most $h$, since every initial value is at most $h$ and all earlier payloads are smaller. No such later read is possible. Both unique copies therefore survive to the boundary. This proves the step after replacing $(a,h)$ by $(a+1,h+1)$.

The [exact simulation](../audits/shifted_dimacs_scan_wave_audit.py) represents constant intervals compactly. On word widths 160, 192, 256 and 512 it checked the first 65 periods of the actual files, including uniqueness of the two values. It cross-checks its sweep against explicit memory on small maps and at $Q=65{,}536$. The unbounded number of distinct states here concerns an uninterrupted scan of a fixed yes instance, so it supplies neither a five-instruction decider nor an impossibility proof for the shifted case.

A different set of proper formulas rules out a SAT decider on this schedule by erasing original signs. The proof permits the long transient exhibited above and never needs an upper bound on the number of distinct memory states. [Two-period erasure proof](arbitrary-stride-private-sign-erasure.md)
