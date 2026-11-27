# Pushdown intersection as a source for adaptive SAT reductions

Fix $k\ge1$. The input to $P_k$ lists one pushdown automaton and $k-1$ finite automata over a common constant alphabet. The question is whether their intersection contains a word. Write $B$ for the total **binary** length of their ordinary transition lists. On sparse machines of maximum size $N$, counting states and transitions, $B=O_k(N\log(N+2))$. Use binary identifiers of the usual fixed width. Balasubramanian and Majumdar's November 24 revision rules out deterministic multitape time $O(N^{2k-\epsilon})$ for every fixed positive $\epsilon$. Their relation-program construction gives the following more precise source bound. [Balasubramanian and Majumdar, v2, Theorems 5, 10, 12 and 14](https://arxiv.org/html/2611.27814v2)

## An exponential hierarchy clock

For each fixed $k$ there exists $D_k>0$ such that no deterministic multitape machine solves even the sparse constant-alphabet instances within

$$
 O\!\left(B^{2k}/2^{D_k\sqrt{\log_2(B+2)}}\right).
$$

Take a fixed multitape language in time $O(2^m)$ outside time $O(2^m/m^3)$, using the deterministic time hierarchy with its logarithmic simulation overhead. Take a binary clock $T$ equal to a sufficiently large fixed multiple of $2^m$ for its decider. Theorem 10 takes $m,T$ in binary and uses address length $H=\log_2T+O(1)=m+O(1)$ and local description size polynomial in $H$. Theorem 12 gives a relation program of size polynomial in $m$, in polynomial time. Theorem 14 builds the sparse automata in $O(N\log N)$ time, with $N\le \mathrm{poly}(m)2^{H/(2k)+O(\sqrt H)}$. All preprocessing, including writing the binary transition lists, fits $2^{m/(2k)+O_k(\sqrt m)}$. Choose a fixed $a_k>0$ with $B\le X_m=2^{m/(2k)+a_k\sqrt m}$ for large $m$.

The claimed time expression is eventually increasing in $B$, so we may bound the hypothesized cost by its value at $X_m$, up to constants for bounded inputs. Its base-two logarithm is at most

$$
 m+2k a_k\sqrt m - D_k\sqrt{m/(2k)} + O(1).
$$

Choose $D_k>(2ka_k+1)\sqrt{2k}$. The resulting runtime, including preprocessing, is $O(2^m/m^3)$, which contradicts the hierarchy choice. The binary specification of $T$ is essential here. The source theorem uses the detailed estimates of the cited compiler. Its original proof applies those estimates to polynomial clocks.

For $k\ge2$, a constant $E_k$ likewise excludes unrestricted deterministic logarithmic-word RAM time $O(B^k/2^{E_k\sqrt{\log_2(B+2)}})$ for $P_k$. To simulate $t$ RAM steps on tapes, scan a list of at most $t$ address/value records for the latest write and scan the read-only input for an input query. Each word operation, including ordinary multiplication and division, costs polynomial in the word width. This gives $O((t+1)(t+B+1)\,\mathrm{polylog}(t+B+2))$ time. The proposed upper clock dominates $B$ eventually for $k\ge2$. Choose $2E_k>D_k$ to absorb its tape simulation's logarithms. This lower bound concerns the explicit automata problem.

## Many SAT calls can cost less than one combined call

Let a uniform deterministic multitape controller for $P_k$ use $C$ steps outside oracle calls. Its SAT queries are explicit formulas of bit lengths $\ell_1,\ldots,\ell_r$, and later queries may depend on earlier answers. Under an unrestricted deterministic $O(n^c)$ logarithmic-word RAM algorithm for SAT, $c\ge1$, the controller can be simulated on tapes in time

$$
 C+O\!\left(\sum_{i=1}^r(\ell_i+2)^{2c}\,\mathrm{polylog}(\ell_i+2)\right).
$$

Each call starts from a blank work memory. Copy its query to private tapes, run the tape simulation just described, return the answer and clear its used tapes at cost at most its time. The controller pays for producing its queries and retains its own tapes between calls. As usual the query tape starts at its left end for each call, or its head restoration is charged to the controller. Thus the source bound applies to the sum of the individual costs. In particular $O(B^b)$ queries of at most $O(B^a)$ bits with $2ca+b<2k$ and $C=O(B^{2k-\delta})$, for some $\delta>0$, would exclude $O(n^c)$ RAM SAT. The same comparison allows a $2^{\Theta_k(\sqrt{\log B})}$ improvement instead of a fixed power if it absorbs the displayed costs. This is a sufficient reduction criterion. Such a controller for $P_k$ is missing.

## Why a single positive grammar certificate is too big

For infinitely many $B$, sparse accepting instances with constant input and stack alphabets have the following property. **Every binary straight-line grammar producing any common accepted word has at least $B^{2k}/2^{O_k(\sqrt{\log(B+2)})}$ rules.** A binary grammar here is an acyclic list of rules giving a letter, the empty word or a concatenation of two earlier words, with a designated output. It may reuse a rule without cost. The proof uses the two calls made by the conjunction gadget of the same compiler. The yes/no equivalence in its theorem statement alone would be insufficient.

Take an $H$-bit counter $j$, with $H$ a multiple of $2k$. Build a relation program whose predicate $A(j)$ succeeds immediately for $j=0,1$, and otherwise requires both $A(j-1)$ and $A(j-2)$. Implement the two decrements as distinct procedures. For subtracting $2^s$, with $s=0,1$, branch on the least set bit in positions $s,\ldots,H-1$, numbered from the low end. Guard the branch by testing that bit and all intervening zero bits. Set the intervening bits to one, clear the chosen bit, and call $A$ on the result. The two base cases and the $j\ge2$ guard are bit tests and Boolean combinations. Compound expressions expand to $O(H^2)$ primitive variables using union, intersection, bit tests and single-bit edits. The guards see the original argument. Every $A(j)$ is true in the least fixed point by induction on $j$.

Apply the construction in §5 of the paper to $j=2^H-1$. Within the balanced run for a conjunction, stages 2 and 5 are **disjoint** subruns. The compiler encodes an argument $xy$ across the entry and exit of a balanced call, with one half in each endpoint. Its ordering and endpoint lemmas give both children exactly the same ordered pair of encoded halves as their parent. Disjunction chooses a child. For a bit edit the child's endpoint pair describes the specified modified argument, including when the bit being set belongs to the exit half. The guards therefore force the two recursive $A$-subruns at a positive nonbase $j$ to have arguments $j-1$ and $j-2$. One may use a distinct stack return tag per call site to make these returns explicit. This costs $O(|\Pi|)$ tags before the compiler's constant-alphabet recoding. All primitive transitions consume a symbol. In §5.2 the synchronized product realizes each unsplit transition one step at a time. In §5.3 contracting the fresh private intermediate states of an accepting path recovers the old path, and each encoded transition uses at least one letter. Thus the lower bound on unsplit run length carries through both compilation stages. [Conjunction, synchronization and recoding in §5](https://arxiv.org/html/2611.27814v2#S5)

For the minimum length $L(j)$ of a successful balanced $A$-call with that argument, $L(0),L(1)\ge1$ and $L(j+2)\ge L(j+1)+L(j)$. Induction gives $L(2r),L(2r+1)\ge2^r$. Consequently a grammar for an accepted word must have at least $\lfloor(2^H-1)/2\rfloor$ rules, since $g$ binary rules can generate length at most $2^g$. The grammar length bound and the recurrence are checked in Lean. The automata compilation comes from the paper. [Lean verification](../lean/PushdownWordWitness.lean)

The binary encoding has $\log_2 B\le H/(2k)+O_k(\sqrt H)$. The construction has at least $2^{H/(2k)}$ states before alphabet recoding, retained as original states in the encoding (also for the single PDA, whose state set includes the width-$W$ segment). Thus $H=\Theta_k(\log B)$ and the rule lower bound has the stated form. Conversely, the product of the machines has $O_k(N^k)$ states and constant stack alphabet. The usual balanced-path grammar has one symbol per ordered pair of states, with rules for neutral transitions, matched pushes and pops, concatenation and the empty path. For each productive symbol choose one rule from its first productive round. All children belong to earlier rounds, so at most $O_k(N^{2k})$ chosen rules suffice. Replacing a bounded-length right side by binary concatenations costs a constant factor. This proves optimality at the exponent scale. Grammar certificates for CFL reachability and rational indices measuring shortest common words have earlier literature. [Chistikov, Majumdar and Schepper](https://arxiv.org/abs/2102.13095) · [Pierre](https://doi.org/10.1016/0304-3975(92)90269-L)

The witness lower bound applies to schemes supplying a straight-line grammar for a common word. On the constructed family, nonemptiness itself follows from the short induction that $A(j)$ holds for every $j$. A hierarchy contradiction for SAT would still require an efficient decision reduction on the hard instances for the source algorithm. The long-word family and the time-hierarchy family may differ.
