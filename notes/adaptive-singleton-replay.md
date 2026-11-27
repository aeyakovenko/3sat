# What adaptive isolation reveals about a specified hard table

**Research journal, 24 November 2026.** Let $E$ be the $L$ easy words in $\mathbb F_2^m$, $U=2^m$, and fix $y\notin E$. An oracle for a bucket $B$ tells whether it contains zero, one or more than one hard word and returns the word in the singleton case. I allowed arbitrary adaptive buckets, even ones whose descriptions would be too expensive to compute on a RAM. The algorithm can reuse its randomness and publish a word it synthesizes from the whole transcript. For strategies invariant under affine relabeling, concentrating on one hard word requires finding easy words first. The first three discoveries give a cubic probability bound. Which higher-order discoveries help depends on the additive structure of the actual easy set.

## The first three easy words

Assume $m\ge2$. An algorithm may use any coordinate-dependent strategy if it is tested on a uniform secret invertible affine relabeling $g(E)$ and its output is pulled back by $g^{-1}$. Equivalently the algorithm and its internal choices can already be affine-equivariant. Under the first formulation, the target is $g(y)$, and the hidden $g$ is independent of the algorithm's coins. This averaging does not grant a corresponding bound for an arbitrary strategy on a fixed, publicly labeled set $E$.

After at most $Q$ oracle calls the probability of outputting $y$ in the original coordinates is at most

$$
\sum_{s=0}^2 {M\choose s}\frac{(L)_s}{(U)_{s+1}}
+ {M\choose3}\frac{(L)_3}{(U)_3},\qquad M=2Q+3.
$$

Here $(a)_s$ is a falling factorial, taken as zero when $s>a$. The bound applies without requiring that the next query, conditional on previous answers, be uniform or symmetric.

To prove it, simulate each bucket oracle by point membership queries to $g(E)$. Use any fixed order in the visible labels, cache all previous membership answers, and stop scanning when two hard points have been found. The prescribed replies, including the actual singleton word, can now be supplied exactly. In each bucket there are at most two *new* hard probes. Thus before finding three distinct easy points or finishing with fewer, the number of new probes is at most $M$. This is a counting simulation; enumerating the points of an implicit bucket is not charged as an efficient RAM implementation.

Fix the algorithm's coins. For a run finishing with exactly $s<3$ distinct easy discoveries, specify the $s$ positions of their probes among the $M$ slots. Replay the procedure with a yes answer exactly at those slots and no on other new probes. Any inconsistent or unfinished simulated execution can be discarded. This yields one tuple of $s$ distinct probe labels and a possible output label, determined without $g$. To output the hard target, the output label must be distinct from those $s$ probes. The affine group in characteristic two is transitive on ordered triples of distinct points: subtracting the first point leaves two distinct, nonzero, hence independent differences, and a map between two such pairs extends to a linear isomorphism. So the probability of the designated $s$ labels belonging to $g(E)$ and the output equaling $g(y)$ is $(L)_s/(U)_{s+1}$. For a run making at least three discoveries specify the first three discovery slots and stop replay at the third. The chance all their labels belong to $g(E)$ is $(L)_3/(U)_3$. Summing over slot sets and averaging the private coins proves the bound.

For fixed $L\ge3$ and $QL/U=o(1)$ this is $O(1/U+(QL/U)^3)$. The cubic term can occur. Take an easy set of three distinct points $a,b,c$ and the specified hard point $y=a+b+c$. Probe uniform distinct singletons to learn easy points, and output the XOR when all three have appeared. The event has probability $(Q)_3/(U)_3$. Its output transforms correctly under an affine relabeling because the sum has an odd number of terms. For $U^{2/3}\ll Q\ll U$ this exceeds the $1/U$ scale. Adaptivity or retaining replies really can beat the [single symmetric trial](dense-hard-table-sampling.md). This easy set illustrates the oracle effect; it is not the set of short native program outputs.

## Charging discoveries only when they enlarge the known affine span

There is a target-dependent refinement. Write $A_s$ for the number of ordered affinely independent $s$-tuples in the ambient space, with $A_0=1$, $A_1=U$ and $A_{s+1}=A_s(U-2^{s-1})$ for $s\ge1$. Write $I_s$ for the number of such tuples in $E$. Split it into $I_s^{\rm in}$ and $I_s^{\rm out}$ according as their affine span contains $y$ or excludes it. The empty tuple has empty span. For $1\le r\le m+1$ and $M_r=2Q+r$ a bound on the same probability is

$$
{M_r\choose r}\frac{I_r}{A_r}
+\sum_{s=0}^{r-1}{M_r\choose s}
\left(\frac{I_s^{\rm in}}{A_s}+\frac{I_s^{\rm out}}{A_{s+1}}\right).
$$

In the simulation use the growing affine span of the easy discoveries. Do not count any membership probes inside that span. Outside it, probe points, cache their replies and enlarge the span at each easy discovery. The count of new outside probes is at most $2Q+r$ until the $r$th enlargement, because only hard probes fail to enlarge the span. For replay, prescribe both the slots of the enlargements and the ordered *original* easy points $e_1,\ldots,e_s$ supposedly discovered there. On a probe inside the current visible span, the visible basis gives unique affine coordinates. Substitute the prescribed original points in these coordinates and answer from $E$. Outside the span use the prescribed slot replies. All these simulated decisions are independent of the hidden $g$, including checks on any points previously probed outside and now lying inside. Inconsistent records can be discarded. For the correct prescription every replayed response agrees with the actual run.

The $s$ visible enlargement points are affinely independent. Their probability of being the images of the specified original tuple is $1/A_s$ by transitivity on affine bases and their subtuples. When $y$ lies outside the original span, also mapping $y$ to the specified output costs a factor $A_s/A_{s+1}$, or is impossible if the simulated output lies inside the visible span. For a run stopped at its $r$th enlargement no output condition is needed. This gives the display. The earlier three-point result uses that the affine span of two distinct points over $\mathbb F_2$ contains exactly those two.

For example, if $y$ cannot be written as the sum of fewer than $r$ distinct easy words with an odd number of summands, all $I_s^{\rm in}$ vanish for $s<r$. If $y$ is outside the entire affine span of a nonempty $E$ of affine dimension $b<m$, group symmetry alone gives the stronger bound $1/(U-2^b)$ for every $Q$: the stabilizer fixing that span pointwise is transitive on its complement. These statements apply to the actual time-bounded easy set as soon as the affine averaging hypothesis on the procedure is met.

## The step still needed for unrestricted SAT

For a public easy word $a$, querying the two-point line $\{a,z\}$ gives a perfect hardness test on every $z\ne a$. A scan from a specified list of candidates can then choose its first hard member without symmetry. In fact, giving the scrambler to the algorithm would let it construct the visible labels for this very scan. Thus the adaptive probability bound cannot exclude the general strategy. To instantiate the line oracle on a RAM one must decide absence of a timely short program for $z$, including possible completions beyond the sampler's own deadline. I have no implementation achieving this. Related pseudodeterministic query lower bounds study canonical solutions to search problems with a different oracle and a worst-case input requirement. [Goldwasser, Impagliazzo, Pitassi and Santhanam](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2021.36)

Lean checks replay from the positions of positive responses and the bound of two fresh negative probes per bucket. The affine-group counting argument is a manuscript proof. [Probe replay in Lean](../lean/AffineProbeReplay.lean)
