# Long-lived reads on a random ordering of Horn equality records

There is a distribution of ordinary unsatisfiable formulas, independent of the solver, on which almost every run of each fixed deterministic SAT solver obeys two access bounds. Every sufficiently long interval of first record discoveries requires proportionally many additional accesses, either in the interval or as later returns to records first touched there. For a solver touching $o(N\log N)$ distinct work addresses, every central cut has $\Omega(N)$ distinct genuine returns or transfers across it. In particular a solver making $O(N)$ accesses must perform $\Omega(N)$ reads whose origins precede them by $\Omega(N)$ new record discoveries. Here the formula contains $2N$ records and $\Theta(N\log N)$ encoded bits. The construction admits an $O(N)$ word-time solver on the promised family.

## A solver-independent static law

Use the equality path from the earlier shuffled-input construction. For each $t\in[N]$ the two records encode $U_{t-1}=V_{t,a_t}$ and $V_{t,b_t}=U_t$, each by two binary Horn clauses. Pin $U_0$ true and $U_N$ false. Distinct $(t,v)$ have distinct names. The pins conflict precisely when all $a_t=b_t$. A mismatched link disconnects the path, so changing any one record's private symbol on a diagonal input changes the verdict. Use the same interchangeable fixed-width physical slots with enough public padding that a native read can meet potentially varying bits from at most one slot. A touch is any such read, including one that sees only the logical index or orientation. In a model allowing unaligned loads leave one full word of public padding between the varying regions. Split multi-access instructions into their $O(1)$ ordered accesses, retaining temporary registers in the controller. Work memory starts at zero, and addresses and words have $w=\Theta(\log N)$ bits. [Equality path and its encoding](shuffled-equality-reads.md)

Take $q=N^8$, choose the common symbols $a_t=b_t$ independently and uniformly in $[q]$, and place the $2N$ labeled logical records in a uniform permutation of the physical slots, independently of the symbols. Symbols and logical row identities each occupy $O(1)$ words. The encoded length is $L=\Theta(N\log N)$.

An equivalent sampling procedure on each fixed diagonal is to draw a uniform order $\pi$ of the labeled logical rows. Supply the next row of $\pi$ to each previously untouched slot on demand. The simulation fixes the whole record privately even if the instruction sees a single field. The run must touch every slot. Otherwise complete the unassigned slots arbitrarily on the diagonal, then change just one untouched symbol to obtain the opposite verdict with the same execution. For each fixed diagonal string the map from $\pi$ to the completed layout is a bijection. Its inverse is the actual first-discovery order on that static layout. Hence the resulting distribution of static layouts is uniform even when discoveries depend on prior symbol values. For off-diagonal inputs the same procedure, completed arbitrarily if the run halts early, defines an ordinary immutable formula with the prescribed verdict.

## All discovery intervals on one run

Let $I$ consist of $m$ consecutive discovery ordinals. Its time interval begins just after the preceding discovery, or at initialization, and ends immediately after its last discovery. Write $F_I$ for the $m$ newly touched physical slots. On the actual run define

- $R_I^-$ as the number of distinct slots discovered before $I$ and touched during $I$,
- $K_I$ as the number of distinct work addresses read in $I$ before any in-interval write to that address,
- $W_I$ as the number of distinct work addresses stored to in $I$,
- $R_I^+$ as the number of distinct members of $F_I$ touched again after $I$.

For every fixed correct solver there is $c>0$ such that, with probability $1-o(1)$, simultaneously for every interval of length $K\log N\le m\le N/2$,
$$
                        R_I^-+K_I+W_I+R_I^+\ \ge\ cm.                 \tag{1}
$$
Here $K$ is a sufficiently large absolute constant. For a disjoint collection of intervals, the first three counts can be charged to distinct actual accesses inside those intervals. Charge the last count to one later return for each slot. A single access can receive at most two charges in total, since the $F_I$ are disjoint and a work load and a work store are separate substeps. None of the charges is a first input-slot discovery. A return can read a different constituent word of the same record.

For a fixed $I$ in uniform $\pi$, let $k$ count logical pairs having exactly one row in $I$. Its mean is $m(2N-m)/(2N-1)\ge3m/4$. Expose the sampled labels one at a time. Completions with two different choices for the next label can be coupled by transposing the two labels in the remaining permutation. The resulting sample subsets differ by at most one exchange, changing $k$ by at most two. The bounded-difference martingale inequality gives $\Pr[k<m/2]\le \exp(-c_0 m)$ for an absolute $c_0>0$. A union bound over all intervals proves simultaneous expansion for $K$ large.

Fix an expanding $\pi,I$. Reveal all symbol values except those at the $k$ split positions. Alice receives the symbol on each split row inside the interval and Bob the corresponding outside symbol. Within each nonsplit pair use its fixed common symbol. The formula is unsatisfiable exactly on the communication diagonal $x=y$ in $[q]^k$. Positions in $\pi$ specify ownership even if the order of the physical slots depends on private data. The following protocol certifies an UNSAT verdict.

1. Bob simulates the prefix. Merlin provides the set $F_I$ in $\lceil\log_2{2N\choose m}\rceil$ bits. Bob checks it is disjoint from the assigned prefix slots and passes the controller to Alice.
2. During $I$ Alice assigns successive rows of $\pi$ to new slots in $F_I$. She requests the contents of any slot outside $F_I$ that she touches from Bob, who rejects if it was never assigned in the prefix. She caches every reply. Before reading a work address lacking a local write or cached value, Alice asks Bob for its actual prefix-final word. She retains all of her own stores, including zeros.
3. After $m$ discoveries Alice returns the controller and the full final address/value list of all work addresses stored by her in the interval. Bob applies these to the prefix memory. Each later touch of a member of $F_I$ can be answered by Alice and cached. Bob assigns all remaining new rows of $\pi$ himself and knows all the prefix rows. Require that the simulation reaches both handoffs and ends with UNSAT.

Any accepting transcript reproduces a genuine execution, by induction on the accesses. Honest advice reproduces the whole run on every diagonal. Give each message a self-delimiting type and use fixed-width counts, addresses and record contents. The honest certificate and protocol transcript together cost at most
$$
 \left\lceil\log_2{2N\choose m}\right\rceil + O\big(w(1+R_I^-+K_I+W_I+R_I^+)\big).
$$
For fixed advice, each complete deterministic accepting transcript gives a rectangle. Its diagonal contains at most one point, since a rectangle containing two would accept a mismatch. Include the advice in the count of all binary transcripts. There are $q^k\ge 2^{4m\log_2 N}$ diagonal lists, while the subset index costs at most $m\log_2(2N)+1$ bits. For sufficiently small fixed $c$, the fraction violating (1) is at most $2^{-\Omega(m\log N)}$, uniformly over the fixed nonsplit symbols. Averaging those symbols and taking the union bound over the intervals proves (1) on the stated static law.

## Charging the work words actually transferred into and out of an interval

Let $s_I$ be the number of distinct work addresses touched in $I$, and $M$ the number on the complete run. Let $C_I^-$ count distinct loads of prefix-written addresses during $I$ before any write there in $I$, counting each address once. Let $C_I^+$ count distinct addresses written during $I$ and loaded in the suffix before any suffix write there. The origin for each charged work word is its genuine last store. On the same high-probability event, for every interval in (1),
$$
 w(1+R_I^-+R_I^++C_I^-+C_I^+)
       + s_I\log_2(1+M/s_I)\ =\ \Omega(m\log N).                   \tag{3}
$$
Define the second term to be zero when $s_I=0$. The address term is in bits, while $s_I$ counts physical addresses regardless of their magnitudes.

In the three-phase protocol write $P_0$ for the set of work addresses written in the prefix, $B_1$ for addresses read in the interval before any interval store there, $P_1$ for interval-written addresses, and $B_2$ for addresses read in the suffix before any suffix store there. Merlin advertises $H^-=P_0\cap B_1$ and $H^+=P_1\cap B_2$. Bob verifies $H^-\subseteq P_0$ and supplies the final prefix value for each listed key. A first separator takes its rare label on $B_1\setminus H^-$, its common label on $P_0\setminus H^-$. Bob checks the common label on all his prescribed keys. To use an unadvertised initial word in the interval, Alice checks the rare label and reads zero. Local writes always take precedence. At the second handoff Alice verifies $H^+\subseteq P_1$ and transfers the final interval value for these keys. A second separator takes its rare label on $P_1\setminus H^+$ and its common label on $B_2\setminus H^+$. Alice checks every prescribed rare label. For an unadvertised frozen suffix word Bob checks the common label and obtains its value from his own end-of-prefix memory. He retains all of his subsequent stores. Both handoffs remain exact for any certificate that passes the checks, even if a prefix or interval store set a word to zero. The other parts of the protocol, including the physical slot advice and both kinds of input returns, are as for (1).

Each separator has at most $M$ prescribed keys, of which at most $s=s_I$ need its rare label. For $s>0$ assign the rare label independently with probability $p=\min(1/2,s/M)$. The probability of meeting any such prescription is at least $p^s(1-p)^M$, whose negative binary logarithm is $O(s\log_2(1+M/s))$. For $s=0$ use the constant common label. There are at most $(1+2\cdot2^w)^{M+1}$ prescriptions. Selecting independent functions and taking a union bound as above gives a public covering family with index length $O(s\log_2(1+M/s)+\log(M+2)+\log(w+2))$. The two size parameters and additive header terms fit in $O(w)$ bits. Hence the complete transcript length is at most the physical subset-index cost plus a constant times the left side of (3). The same split-pair concentration and rectangle count prove (3) for all intervals.

For example, suppose the actual run makes at most $T\le A N$ accesses for fixed $A$. Partition a constant fraction of discoveries into $r$ disjoint intervals of comparable length $m\asymp N/r$ in the range of (1). Across them $\sum s_I\le T$. Concavity and monotonicity of $s\log_2(1+M/s)$ give
$$
             \sum_I s_I\log_2(1+M/s_I)\le T\log_2(1+Mr/T)
                      \le A N\log_2(1+r).
$$
Consequently all but an $O(\log(1+r)/\log N)$ fraction of the intervals have $R_I^-+R_I^++C_I^-+C_I^+=\Omega(m)$. The exceptional fraction tends to zero for every $r=N^{o(1)}$, including polylogarithmic $r$. Each such obligation is witnessed by actual returns or work versions read across an interval boundary. For disjoint intervals, a linked work load can witness both an outgoing transfer from its store's interval and an incoming transfer to its load's interval. It cannot witness outgoing transfers from two disjoint intervals. The corresponding at-most-two counting also holds for input returns. This conclusion holds for every such partition of the same execution.

## Genuine last-writer transfers at every central cut

Cut just after the $j$th discovery. Let $R_j$ count distinct prefix-discovered private slots touched again after that cut. Let $C_j$ count distinct work addresses actually written in the prefix and then read after the cut before any post-cut write there. This counts an explicit prefix store of zero whose word is later loaded and excludes an initialized zero at a never-written address. On the same distribution, with probability $1-o(1)$, simultaneously for $N/2\le j\le3N/2$,
$$
                      M+w(1+R_j+C_j)\ =\ \Omega(N\log N).            \tag{2}
$$
There is no workspace assumption in (2).

For each central cut the number of split logical pairs has mean $j(2N-j)/(2N-1)\ge 3N/8$. Expose the smaller side of the cut and use the preceding exchange argument. Except with probability $\exp(-\Omega(N))$, every central cut has $k\ge N/4$ split pairs. Fix such an order and cut, reveal the nonsplit symbols, and give the prefix-side split symbols to Alice and suffix-side symbols to Bob. Alice simulates to the cut. She transmits the controller and a $2N$-bit characteristic vector of the physical slots already occupied. Bob can now ask her for the true record of any returning slot and cache it. Remaining fresh rows are all available to Bob in the prescribed order.

For work memory, put $P=\{$prefix-written addresses$\}$ and $B=\{$addresses loaded in the suffix before any suffix store there$\}$. Merlin lists $H=P\cap B$. Alice verifies $H\subseteq P$ and sends the final prefix value for each listed address. To certify default values at all other frozen addresses, prescribe a Boolean function equal to zero on $P\setminus H$ and one on $B\setminus H$. These disjoint prescriptions concern at most $M$ keys. There is a public family of $O(2^M(M+1)(w+1))$ functions hitting every binary prescription on at most $M$ keys. Indeed, one uniform Boolean function succeeds with probability at least $2^{-M}$ and there are at most $(1+2\cdot 2^w)^{M+1}$ prescriptions. A union bound on independent functions proves existence. Both parties can fix a family for every integer size bound by unbounded local computation.

Merlin sends $M$ and a function index. Alice checks zero on *all* of $P\setminus H$. When Bob needs the old value at any unlisted key he checks one there and returns zero. Post-cut stores, including clears, always take precedence. Induction shows that even wrong advice can never cause acceptance on a mismatch. The certificate length on the true run is $O(N+M+w(1+R_j+C_j))$, including the size bound and index. This is the address-set disjointness step from information-transfer arguments, applied to the actual adaptive discovery cut. [Pătraşcu and Demaine, *Logarithmic Lower Bounds in the Cell-Probe Model*](https://erikdemaine.org/papers/DynamicConnectivity_SICOMP/) and [the earlier many-phase protocol](simultaneous-cuts-on-a-sat-execution.md)

The diagonal entropy is at least $(N/4)\log_2 q=2N\log_2 N$. The same rectangle count shows that, for sufficiently small implicit constant in (2), the violating fraction of diagonal symbols is $2^{-\Omega(N\log N)}$. A union bound over $j$ establishes (2) simultaneously with (1).

## Lifetimes and the attainable time bound

Associate each repeated private input access with the initial discovery of that slot. Associate each work load that has a preceding store with the *last* store to that address. The lifetime of such a link is the number of discovery cuts between its origin and destination, counting a cut immediately after the origin and before the destination. At each cut every slot counted in $R_j$ and every work address counted in $C_j$ supplies a separate crossing link by taking its first eligible post-cut load. Thus the sum of all link lifetimes is at least $\sum_j (R_j+C_j)$ over central cuts.

On the event in (2), if $M=o(N\log N)$, this gives $\Omega(N^2)$ total lifetime. If the execution makes only $O(N)$ memory accesses, it has $O(N)$ links and each has lifetime at most $2N$. Consequently $\Omega(N)$ distinct reads each have lifetime $\Omega(N)$. Both conclusions are statements about physical accesses, even when the word operations between them are arbitrary. They are attained in order by scanning the records and tabulating by logical index. Validate the promised format and one record of each orientation per index, then compare the paired symbols. A general SAT solver can handle other inputs. The algorithm takes $O(N)$ native word operations on this family. The long links of the theorem can overlap across many cuts, and their aggregate lifetime is compatible with this running time. The unrestricted SAT time lower bound in encoded bits remains open.

[Finite check of layout uniformity, cut witnesses and lifetimes](random_order_equality_accesses_audit.py)
