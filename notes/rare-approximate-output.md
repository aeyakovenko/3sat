# Generating even a weak approximation to one unary output

**Research journal, 24 November 2026.** Assume a deterministic packed-word SAT solver takes time $O(n^k)$ for $k=1,2,3$. Write $H=1/k^2$. One fixed program, on an all-zero input of $B=2^m$ bits with its length available, prints a packed $B$-bit table $Y_m$ in $O(B/m)$ word operations. For some constant $C$, at every sufficiently large arity, a bit predictor whose advice length plus worst-case lookup time is at most

$$2^{Hm-Cm^{2/3}}$$

has agreement at most $1/2+2^{-\lfloor m^{1/3}\rfloor}$ on the uniform index. This uses the same program across every fixed polynomial saving in the lookup exponent. It also applies to bounded-fan-in Boolean circuits, after increasing $C$ for the cost of their gate lists. [Fixed-parameter code and decoder](biased-hard-table-lookup.md) · [Exact source table](output-linear-hard-tables.md)

Under **linear SAT**, this table gives a test for attempts to simulate RAM computation in small space. Fix a randomized transducer with write-only sequential output and one-way fair coins. Give it arbitrary precomputed advice of $a$ bits, and $S$ bits of accessible configuration, including work addresses on a sparse RAM. The unary input and the read-only advice may be rescanned. For every fixed $0<\epsilon<1$ and $0<\zeta<1$, if

$$a+S\le B^{1-\epsilon},\qquad T\le 2^{m^{2-\zeta}},$$

then the probability that its first $B$ output bits arrive by time $T$ and have agreement **strictly greater** than $1/2+2^{-\lfloor m^{1/3}\rfloor}$ with $Y_m$ is less than $2^{-B^{1-\epsilon}}$, for all sufficiently large $m$. In particular, a polynomial-time, polynomially space-saving sampler would have to fail even at this weak approximation task. The unrestricted bulk constructor itself uses unrestricted workspace.

## Uniform choice of coding parameters

Take $r=u=\lfloor m^{1/3}\rfloor$, $b=\lfloor m/(r+1)\rfloor$, $Q=2^b$, $d=2^{b-6r-16}$, and original grid size $M=d^r$. Use a fixed fallback at small arities. Thus $Q=2^{O(m^{2/3})}$, $\tau=2^{-u}$, and $Q\tau^5\to\infty$. With $v=m-(r+1)b\le r$,

$$m-\log_2 M=b+v+6r^2+16r=O(m^{2/3}).$$

Indeed $r^2-r\le b\le(r+1)^2$. The degree of a quadratic-curve restriction is at most $2r(d-1)\le Q\tau^5/2^{15}$, since $r\le2^r$. The [Hadamard list, curve interpolation, and common-anchor argument](biased-hard-table-lookup.md) therefore applies with its stated constants.

The field tables and Lagrange weights take $Q^{O(1)}\operatorname{poly}(m)=o(B/m)$ time. Extending the grid in each coordinate costs $O(rd Q^r)\le O(rB/2^{6r+16})=o(B/m)$ field-table operations, even allowing a polynomial in $m$ for index arithmetic. The packed Hadamard blocks have $Q$ bits each. The $2^v$ repeated copies can be appended in overall $O(B/m)$ time since $Q/m\to\infty$. The source constructor has time $O(M/\log M)$. A fixed exact-table evaluator can run the reconstruction given $m$ as advice, so the varying dimensions require one source constructor. In particular the field and the number of coordinates are determined by algorithms.

For a proposed predictor with cost $s+q$, fix the best high-index copy in $v$ advice bits. Let the curve-decoder store $O(\log M)$ trials, each with two $r$-dimensional anchors, their parameters, and one field value. These data take $\operatorname{poly}(m)$ bits. At a point on a curve the decoder computes its $r$ coordinates, queries the predictor on $Q$ masks and enumerates the correlated symbols. Univariate interpolation and root enumeration per curve have a fixed polynomial bound in $Q$, independent of $r$. The coefficient array, number of equations and degree for these operations are each $Q^{O(1)}$. Work involving the coordinate count is polynomial in $m$. Including trials, the total lookup cost of recovering one exact source bit is at most

$$\operatorname{poly}(m)\big(s+Q^{C_0}+(q+1)Q^2\big)$$

for an absolute $C_0$. Since $M^H/\operatorname{polylog}M\ge2^{Hm-O(m^{2/3})}$, taking $C$ sufficiently large contradicts the exact source lower bound. These parameters give weaker bias at a fixed polynomial saving than tuning the dimension to that particular saving. One sequence now works as the hardness exponent tends to $H$. [Sudan, Trevisan and Vadhan](https://people.csail.mit.edu/madhu/papers/1999/stv-journ.pdf)

## A rare approximate output gives a short seed

Suppose the approximation event has probability $p\ge2^{-B^{1-\epsilon}}$. Take $T\ge B$ by harmless padding, use a clock, and stop the output after $B$ bits. Fix the unary input, advice, and target table. A branching program reading the coins in order can check the event with state length $O(S+\log T+m+\log(a+2))$. It has an output position, a match count, and the current transducer configuration. The comparison with the fixed $Y_m$ is hardwired in the transition function. This nonuniform comparison is needed only for the existence of a seed. Allowing a word of fresh bits per operation increases the coin bound by a polynomial factor. Random access to previously read coins requires counting those bits as ordinary accessible storage.

Nisan's generator produces a seed of length

$$O\big((S+\log T+m+\log(a+2)+\log(1/p)+1)\log(T+2)\big)$$

which makes the transducer succeed. For example enlarge the block length in the finite-state theorem to absorb the log width, log number of coin positions, and $\lceil\log(2/p)\rceil$. The distinguishing error is then strictly smaller than $p$. One seed hits the event. Its blocks can be expanded on a work tape by a depth-first traversal with space linear in this displayed bound and time polynomial in $T+B+a+S+\lceil\log(2/p)\rceil$. The expander never stores its full coin output. [Nisan, Sections 2–4](https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2013W/Nisan_PRG.pdf)

Give the seed and the original advice to one fixed bit predictor. For query $i$, the resulting deterministic tape computation replays the transducer and returns bit $i$ of its emitted sequence, with a fixed default at timeout. Its public controls include $m$ and the clocks. A sparse RAM can be replayed by scanning address/value records in polynomial time and space proportional to their charged length, with the advice on a read-only tape. The public input plus tape configuration length is at most $B^{1-\epsilon}\operatorname{poly}(m)$ and the logarithm of the new clock is $O(m^{2-\zeta})$. Under linear SAT the bounded tape reachability construction recovers that bit in time

$$B^{1-\epsilon}\operatorname{poly}(m)\,2^{O(m^{1-\zeta/2}\sqrt{\log m})}=B^{1-\epsilon+o(1)}.$$

The seed is the same for all indices. Advice plus this time fits the lookup bound above at $k=1$, which contradicts the chosen seed's agreement. If space is stated in nonzero words, charge their addresses, values and registers. A strict polynomial margin absorbs this logarithmic overhead. [Bounded reachability and uniform alternation elimination](linear-quantifiers.md)

## Comparing the requirement with general simulations

An unconditional simulation that produces such a weak approximation to *every* output-linear unary RAM in these simultaneous time, space and success bounds would exclude linear SAT. Pure-space simulations permit much longer runs. The existing one-writable-tape simulation and its RAM consequence do not give this simultaneous clock. An independent fair-coin printer can always hit the approximation threshold with some probability. For independent fair output bits the upper Chernoff bound is $\exp(-2B\tau^2)$, already smaller than $2^{-B^{1-\epsilon}}$ for every fixed $\epsilon>0$ and large $m$. That printer does not furnish the required simulation. The quadratic and cubic hypotheses above give the bit-lookup statement. The rare-output proof uses linear SAT to accelerate the tape replay. Priority of these parameter combinations remains unverified. [Li and Tell, Section 1 and footnote 1](https://eccc.weizmann.ac.il/report/2026/233/download/)
