# Adaptive read order on a RAM cycle

Let $S$ be a public cyclic order on $L$ distinct word addresses. Extend its successor to fix the other addresses. A deterministic RAM reads $x_i=M[p_i]$ at any adaptively chosen point $p_i$ of the cycle. Before its next read it may skip its write or set $M[x_i]\gets S^{\delta_i}(p_i)$, with $|\delta_i|\le r$ for a fixed integer $r\ge0$. All register operations and branching are charged. The content of every memory cell, including the packed input, is writable. We count both forward and backward steps using cyclic distance. The controller has $O(w)$ bits of state, and $h$ denotes the size of the initial memory image. The applications below have $h=O(1)$, $w=\Theta(\log N)$ and a polynomial time deadline. We assume the initial read can be derived from the public starting state. The bounds concern accepting runs of a controller sound on every valid file.

The hard distribution puts independent uniform signs on $k=\Theta(N/\log^2 N)$ vertex pins and determines its edge pins by graph parity equations. It uses proper ASCII DIMACS with $N$ input bits. Every vertex sign is sensitive on every positive input. Every balanced ownership partition of the vertex signs has an edge matching of size at least $\gamma k$ crossing it. Consequently each accepting transcript of an exact two-party simulation has probability at most $2^{-\gamma k}$, for arbitrary ownership of the other words. A productive cycle must contain all the vertex signs and $\Omega(N/w)$ sensitive guard words. The construction, initial alphabet bound, and rectangle proof are in the [parity-pinned SAT theorem](orbit-orders-and-parity-pinned-sat.md).

## Restarts and reversals between directed arcs

Suppose a run up to time $t$ can be partitioned into $A$ arcs of reads. Inside an arc, successive addresses advance by one fixed choice of $S$ or $S^{-1}$. The controller may choose the direction, length, and next starting position from its observations. A change of starting position costs one arc. Every write, including the final write of an arc, obeys the stated bound on its offset from the **current** read address. For any cut assigning a contiguous arc to Alice and its complement to Bob, the actual number of bits needed to simulate this run is

$$
 O_r\big((h+1)(A+t/L+1)^2w\big).
$$

Cut each directed arc into blocks of at most $\lceil L/2\rceil$ reads. There are $Q\le A+2t/L$ blocks, each without a repeated address. There are at most $3Q$ maximal stretches of consecutive reads with the same owner.

Trace a read backwards to the most recent write to its cell, until an initial value is reached. A link sends a pair $(p_i,x_i)$ to $(x_i,S^{\delta_i}p_i)$. Two successive links at indices $u<j<v$ send the two coordinates of $(p_u,x_u)$ to $S^{\delta_u}p_u$ and $S^{\delta_j}x_u$, respectively, with $p_j=x_u$. In particular $p_v=S^{\delta_u}p_u$. If the three indices are in one block, the directed progression covers at most $\lfloor L/2\rfloor$ steps. Its displacement in cyclic distance from $u$ to $v$ equals $v-u$, which is at most $r$. The middle position $p_j$ is therefore within $r$ steps of $p_u$, and $x_v=S^{\delta_j}p_j$ is within $2r$ of $p_v$ (already $p_j$ is within $r$ of $p_v$).

Group the ancestry in pairs of links backwards from its final read. Distinct groups crossing block boundaries traverse disjoint time steps, so at most $Q-1$ cross a boundary. After the last group lying entirely inside a block each further group increases cyclic distance between coordinates by at most $2r$. If every group crosses a boundary, one initial-value coordinate has advanced by at most $rQ$ in total, allowing for a possible unmatched link. Thus every read pair is within distance $2r(Q+1)$, or has an endpoint in $U=\bigcup_{|j|\le rQ} S^j(H)$ for the initial image $H$. A pair with an off-cycle endpoint uses the latter alternative.

One owner simulates consecutive local reads, defers writes to foreign memory, and at handoff transmits their last values together with the controller state, elapsed time and next address. Addresses outside the cycle can be assigned publicly to either party. In one ownership stretch, close pairs can write across the cut only to $O(r(Q+1)+1)$ positions near its two boundaries. Foreign destinations in $U$ give at most $|U|$ more records per stretch. The total number of reads with source in $U$ is at most $Q|U|$ since each block visits each address at most once. This proves the bound, including the messages needed to resume the actual data-dependent computation. Neither party needs to compute the ancestry classes.

Use any balanced cut on the marked orbit. Simulate up to a polynomial deadline, rejecting if a proposed communication budget is exhausted. Every accepted positive run with $A+t/L+1\le c\sqrt{k/w}$ fits the budget $\gamma k/2$ for a sufficiently small $c$. Such runs jointly have probability at most $2^{-\gamma k/2}$. For complete passes with data-dependent changes of starting point or direction, $A\le1+t/L$, so the fixed-order near-three-halves time lower bound persists. Arbitrarily many short arcs incur the stated charge.

## Cyclic travel with unrestricted changes of direction

For $m$ reads put $J=\sum_{i=0}^{m-2}\operatorname{dist}_S(p_i,p_{i+1})$; take $J=0$ before the second read. There is no assumption on individual jumps or on visits to a single address. For a cut with $F$ ownership stretches, simulation on this particular trace costs

$$
 O_r\big((h+1)F(1+\sqrt J)w\big).
$$

To see this, fix an integer $s\ge1$. Classify a two-link group $u<j<v$ as short if the cyclic travel on the time interval $[u,v]$ is at most $s$. Then $\operatorname{dist}_S(p_j,p_v)\le s$, so $\operatorname{dist}_S(p_v,x_v)\le s+r$. There are at most $J/s$ disjoint long groups. As before, every read pair is either within distance $s+r+2rJ/s$, or has an endpoint in $U=\bigcup_{|j|\le r(1+\lfloor J/s\rfloor)}S^j(H)$.

Here repeated visits to a source in $U$ require additional care. Its value on entry to an ownership stretch contributes at most one distinct foreign destination over that stretch. If its value was rewritten inside the stretch, its new value has the form $S^\delta(y)$ for some read address $y$ on the local side. If foreign, that value belongs to the fixed $O(r+1)$ positions near the two boundaries. This observation bounds the **distinct** foreign destinations due to sources in $U$ by $|U|+O(r+1)$ per stretch, however often the machine revisits them. Add the destinations in $U$ and those within the close-pair boundary neighborhoods and take $s=\max(1,\lceil\sqrt J\rceil)$. The simulation itself simply batches all foreign writes and operates without prior knowledge of $J$.

Order the $k$ distinct vertex sign words along the cycle. For each sign position take the cut whose Alice arc starts at that sign and ends immediately before the sign $k/2$ marked positions later. Each cut balances the vertex signs. Every edge of the address cycle serves as a boundary of at most two cuts. A jump between two reads can switch ownership only on cuts whose boundary it crosses along a shortest cyclic path. Summing over all cuts, a run incurs at most $2J$ switches, including when some jumps are arbitrarily long. Some one of the $k$ cuts therefore has at most $1+2J/k$ stretches on that run.

For each of these publicly specified cuts run its own deterministic simulation with bit cap $b$, aborting if exceeded. These protocols are sound also on the mixed sign inputs used by the rectangle argument. A positive run of travel at most $J_0$ and time within the deadline is accepted by at least one cut if

$$
 b\ \ge\ C_r(h+1)w(1+2J_0/k)(1+\sqrt{J_0}).
$$

Hence the mass of all such runs is at most $k\,2^{b-\gamma k}$. For a sufficiently small constant $c$ and $J_0=c(k^2/w)^{2/3}$ the mass is exponentially small in $k$. When the distance of each jump is bounded by a fixed constant, this gives an $\Omega(N^{4/3}/(\log N)^{10/3})$ time lower bound on some positive input, even with unlimited backtracking and workspace. If $r=0$, each last-writer link only exchanges the two coordinates; an endpoint always lies in $H$. The per-stretch cost is then $O((h+1)w)$, giving a travel threshold $c k^2/w$.

## Payloads equal to the read address up to its low bit

On the natural numeric cycle suppose the write payload may be $p$ or $p\mathbin{\mathrm{XOR}}1$. Every read pair has an endpoint in the fixed set $U=\{z:\lfloor z/2\rfloor=\lfloor h'/2\rfloor\text{ for some }h'\in H\}$ of size at most $2h$. In fact, upon replacing each coordinate by its high part, each last-writer link only interchanges the coordinates. One coordinate of a root pair comes from $H$. Since either permitted payload is at distance at most one from its source, the per-stretch bound for $r=0$ above applies here as well: a rewrite within the stretch can produce a foreign value only at a boundary. The actual cost is $O((h+1)Fw)$.

Consequently, for this payload class the directed-arc threshold strengthens to $A+t/L+1\ge c k/w$ outside a set of positives of exponentially small mass. This gives a necessary number of restarts when $t/L$ is small, for a model in which fully adaptive reads already permit general RAM memory simulation with a logarithmic overhead. The rank-based travel threshold is $c k^2/w$. [Two-probe bit memory and its initialization](adaptive-one-bit-address-payload.md)

On the natural physical cycle a tighter travel bound follows by writing the $k$ vertex pin clauses consecutively at equal row stride $q=\Theta(\log N)$ **words**. Each row has one long aligned variable identifier and the same two short dummy literals, so this ordering and stride fit the preceding hard distribution. Number the vertex sign words $v_0,\ldots,v_{k-1}$ in physical order. For $0\le i<k/2-1$ choose any of the $q$ address edges between $v_i,v_{i+1}$ as an arc boundary, and the corresponding edge $k/2$ rows later as the other boundary. Each resulting arc contains exactly $k/2$ vertex signs and each chosen edge is used just once. There are $(k/2-1)q=\Theta(N/w)$ cuts. Some cut on each real run has $F\le1+J/((k/2-1)q)$; taking the union of all capped protocols costs only this polynomial factor in the probability estimate. The resulting travel threshold for the one-bit payload rule is $\Omega(k^2 q/w)=\Omega(N^2/(\log N)^4)$. This is a measure of head travel. A standard RAM gives a distant read unit cost.
