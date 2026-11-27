# Selecting public input words at the last SAT reduction

**Research journal, 24 November 2026.** On the explicitly specified packed binary 3-CNF and logarithmic-word RAM of [the local transfer](packed-band-transfer.md), SAT cannot simultaneously run in $O(n\log^a n)$ time and $O(n/\log^{2a+7} n)$ **bits** of work space for any fixed $a\ge0$. In particular the space cap is $O(n/\log^7 n)$ at linear time. This is a space-restricted refinement of the classical checkpoint argument. It uses an ordinary explicit SAT instance at the last alternation removal, where the simulating machine may store the whole reduction. I have not established priority for the logarithmic exponent.

## An explicit short instance when the public input dominates the run

Give a fixed nondeterministic program $m$ read-only words and a cap of $R$ native steps. Take $L=\log_2(m+R+2)$ and word width $W=\Theta(L)$. In the application all such widths are within fixed factors of the original phase word width. Up to harmless polynomial-in-$L$ setup, there is a uniformly constructible satisfiability instance of
$$
O(R L^3+m L^2)\quad\text{encoded bits}.
$$
The $R$ term uses the word arithmetic and bounded-fan-in gate templates specified in the local transfer. In particular each arithmetic step has $O(W^2)$ gates. Non-input memory, nondeterministic switches and the chronological trace have $O(RL^2)$ gates in all. A bounded number of memory or input accesses per instruction only multiplies $R$ by a constant. Pad unused events using an inactive tag checked by the instruction verifier. Out-of-range input reads are checked by their fixed public convention, for example zero, and excluded from the in-range lookup list.

Here is how to verify the read-only queries while charging only $O(mL)$ additional gates. Construct a directed acyclic bounded-degree $m$-superconcentrator with $O(m)$ vertices and edges. Its sources carry the constant pairs $(k,x_k)$, $0\le k<m$. Use the first $\min(m,cR)$ output vertices as available ports, where $cR$ bounds the number of input reads. At each vertex guess either inactivity or an active incoming and outgoing edge, allowing a path to start only at a source and end only at an available port. Enforce matching flags on the two ends of every edge, with at most one selected incoming and outgoing edge per vertex. A path carries the entire tagged address and value through its selected edges. Each vertex and incident edge requires $O(W)$ Boolean gates, since its degree is bounded. An active port's pair must therefore originate at the source holding those actual data. Conversely, for any set of $k$ distinct queried addresses, superconcentration routes them to the first $k$ available ports by vertex-disjoint paths. Their order at the ports is immaterial. Explicit linear-time construction of the graph is stated in Cheung, Kwok and Lau, in their superconcentrator compression algorithm. [Cheung, Kwok and Lau](https://cs.uwaterloo.ca/~lapchi/papers/matrix-rank.pdf) · [Gabber and Galil's construction](https://doi.org/10.1016/0022-0000(81)90040-4)

Take a list consisting of the port records and the trace's input-read records. It has $O(R)$ entries. Guess a permutation with a Beneš network, then check adjacent entries are sorted by activity, address, and source-before-read type. In each active address group require that the first entry comes from a port, that every remaining entry is a read, and that adjacent values agree. One may allow an unused genuine port. This tests **every** read of a repeated address against the same true value. An inactive port or dummy read cannot supply an active group. Routing and checking the list costs $O(RL^2)$ gates. The same witness can certify all actual input reads on any honest execution. Conversely a satisfying witness supplies exact input words and an internally consistent execution, so the source accepts.

Tseytin clauses with explicit binary variable indices use $O(L)$ bits per gate, yielding the claimed bit length. Given the graph adjacency lists, the source data, and the program templates, a deterministic RAM can **write** the entire instance in $O(RL^3+mL^2+\operatorname{poly}(L))$ time. Here only the total construction time is used; the generator need not return a single edge in constant time with a small work tape. If the input has multiple public banks, concatenate fixed layouts and retain the bank tag in the addresses. An empty input or a cap with no possible input reads can bypass the routing graph.

## Using the cheaper public-input term

Assume a SAT solver with the stated time and space cap. Put
$$
 A=a+3,\qquad p=a+2,\qquad B=(2a+7)-2=A+p .
$$
For *balanced* source clock $H\ge m$, the regular local generator supplies a deterministic simulation costing $O(HL^A)$ time with snapshots of $O(H/L^B)$ **words**. This simulation uses the virtual formula and its local generator, including at every internal checkpoint stage. For the last conversion from nondeterministic to conondeterministic time, run the solver deterministically on the materialized formula just constructed. Even for $m>R$, the time at this last conversion is
$$
 O(RL^A+mL^p+\operatorname{poly}(L)).
$$
It works for the complemented direction as well. All clocks in a fixed number of applications remain within a fixed logarithmic factor of the initial polynomial clock or the relevant public-input bound, as in the [band derivation](sat-time-space-band.md).

For clarity write $H=\max(m,R)$ in an internal stage. Split the deterministic run into $P=\lceil L^u\rceil$ segments. Its checkpoint list and the original input occupy $O(m+PH/L^B)$ words. A guessed defective segment takes $O(HL^A/P+H/L^B+\operatorname{poly}(L))$ steps to test. On its first use, the last-conversion bound therefore gives overall time $O(HL^{e_1}+mL^p)$ with
$$
 e_1=(2A+p-B)/2=A/2,\qquad u=(2A+B-p)/2.
$$
Indeed the two competing exponents are $2A-u$ and $u-B+p$; at the balanced split $u=3A/2$ they are equal. The additional cost $HL^{A-B}$ from loading the endpoints fits. Polynomial-in-$L$ terms are absorbed throughout.

After this first use $e_1\le p$, so a complementary simulation with bound $O(\max(m',R')L^e+m'L^p)$ always costs $O(R'L^e+m'L^p)$ even on an unbalanced defect query. Repeating the same split with
$$
u=(A+e+B-p)/2,\qquad e'=(A+p+e-B)/2
$$
halves $e$ at the stated boundary. One more application gives $e=A/4$.

Finally use two nested checkpoint lists, of lengths $L^{x_1}$ and $L^{x_2}$, and apply that complementary simulation twice. At the inner level the chosen outer index has already been specified. Copy its two boundary snapshots and pass those and the original input to the inner check. The full outer list is charged once as public input to the outer alternation removal. Counting the outer list, inner list, and final replay respectively gives time
$$
 O\!\left(H\left[L^{x_1-B+p}+L^{x_2-B+p+e}+
 L^{A-x_1-x_2+2e}\right]+(m+H/L^B)L^{p+e}+\operatorname{poly}(L)\right).
$$
The two quantifier changes and the lengths supplied to each are proved in the [two-level derivation](sat-time-space-band.md). Choose $x_1=11A/12$ and $x_2=2A/3$. All three exponents in brackets equal $-A/12$. The extra snapshot exponent $p+e-B=-3A/4$ is smaller. On the hierarchy inputs with $H$ quadratic in the original binary input length, $mL^{p+e}=o(H)$ as well. This gives a complementary $o(H)$ simulation of the bounded diagonal program on its own fixed-width RAM, a contradiction. Rational approximations to split exponents preserve the strict final saving, with arbitrarily small slack in intermediate bounds. [Machine model, compact snapshot replay, and complementary diagonal](packed-band-transfer.md)

The materialized construction reduces the cost of a *public* word at a final reduction. Comparing permutation and input records in the full native trace still carries the distinct $RL^3$ cost, and the internal simulations still require the space cap.
