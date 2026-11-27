# Where genuinely new outputs must appear between two cutoffs

**Research journal, 24 November 2026.** Under linear-time SAT, almost every sibling of the actual native first omission contains a constant fraction of words still missing shortly before the final cutoff. Can that force too many distinct late outputs when many times or orders are considered? A single decoder gives a joint lower bound for every time and output cell targeted by a fast sampler. Summing these lower bounds is consistent with a finite budget, even when the sampler uses past release counts. [Sibling-density argument](coordinate-omissions.md)

Give the native interpreter public length $D$, put $U=2^D$, and run all names shorter than $D$ to $B=U^{20}$. Use clocks $t_0=U^3$ and $t_j=t_0D^{aj}$ through the last $t_j\le B$. Take $a$ sufficiently large for the fixed algorithms below. A deterministic sampler on a uniform $D$-bit seed can halt with a pair $(j,z)$, where $z$ is a $D$-bit label. Count this choice only if it halts by $t_{j-1}$. Let $s_{j,z}$ be its number of counted seeds. The sampler may compute earlier statistics with the assumed solver as part of its timed computation. Its words have polynomially many bits in $D$. For each stage allow a uniformly polynomial-in-$D$ label function on output words, with cells $C_{j,z}$ consisting of words carrying label $z$. These partitions can change between stages and need not match how the sampler computes its labels.

Let $H_{j,z}$ be the number of words in the cell that are still missing at $t_{j-1}$, and $\Delta_{j,z}$ the number first produced in $(t_{j-1},t_j]$. Under **linear deterministic time for ordinary explicit SAT**, there is a fixed integer $c$ depending on the construction such that every stage and cell satisfies

$$
  \Delta_{j,z}\ \ge\ \min(H_{j,z},\,N_{j,z}), \qquad
  N_{j,z}\ \ge\ 2^{-c}s_{j,z}-1. \tag{1}
$$

In fact $N_{j,z}$ are explicit, disjoint integer allocations with sum at most $2^{D-c}$. If the cell has a word still missing at the **end of this stage** $t_j$, saturation is impossible, so $H_{j,z}>N_{j,z}$ and $\Delta_{j,z}\ge N_{j,z}$. This applies to the cell of the actual first omission under **any** selected order, as well as to every other surviving cell. For a partition consisting of the whole space, there is always a missing word by the count of names. Thus the distribution of first-production times dominates a fixed proportion of each attainable sampler distribution, up to rounding. To exclude linear SAT it would suffice to exhibit one uniform sampler and partitions with $(\Delta_{j,z}+1)/s_{j,z}$ tending to zero on cells that still contain some missing word at $t_j$. The witness words need not be the canonical omissions or stay missing at $B$.

## Computing the allocations and fresh outputs

Put the pairs $(j,z)$ in increasing time and then label order. Write $S_{j,z}$ for the number of counted seeds before this pair. Assign the half-open integer interval

$$
  \left[\left\lfloor S_{j,z}/2^c\right\rfloor,\
  \left\lfloor(S_{j,z}+s_{j,z})/2^c\right\rfloor\right)
$$

to the pair. Its length is $N_{j,z}$. For each seed the sampler gives at most one pair, so all intervals fit in $[0,2^{D-c})$. A fixed program takes a raw suffix of length $D-c$ giving an index $x$ in this range. Choose $c$ larger than its fixed header length, with the program recovering $c$ as $D$ minus suffix length. This leaves the complete name shorter than $D$.

To compute a cumulative seed count within stage $j$, test whether at least $r\le U$ seeds give stage $j$ and a label at most a queried boundary by $t_{j-1}$. Guess $r$ strictly increasing seeds. Universally select one of their indices, check that seed's timely sampler verdict using one bounded accepting computation transcript, and guard out-of-range indices. There is a fixed number of quantifier blocks. The encoded circuit and its construction take $(U+t_{j-1})\operatorname{poly}(D)$ because the list has at most $UD$ bits and only one computation is checked. Under linear SAT, eliminating these blocks and binary-searching $r$ takes $(U+t_{j-1})\operatorname{poly}(D)$ time. [Uniform fixed-block elimination](linear-quantifiers.md)

Process stages in order until $x$'s interval is reached. Within its stage, binary search finds the label using $O(D)$ cumulative-count queries, even with $U$ possible labels. Now the local integer $x-\lfloor S_{j,z}/2^c\rfloor$ specifies a zero-based rank among $t_{j-1}$-missing words in that cell. Count missing words subject to a binary prefix by guessing a sorted list of distinct words satisfying both restrictions, then universally checking that no short name has a valid transcript outputting any listed word by $t_{j-1}$. The one simulated output is compared to the whole guessed list. This costs $(U+t_{j-1})\operatorname{poly}(D)$ with the same hypothesis. Rank selection follows the binary prefix using these counts. On ranks below $H_{j,z}$, print the selected word. The other ranks can halt without output.

All earlier stages and all searches still cost $t_{j-1}\operatorname{poly}(D)$. The overhead exponent uses $\log t_j=O(D)$ and fixed quantifier depth. Choose $a$ large enough to pay this cost, including native interpretation, before $t_j$. The $\min(H_{j,z},N_{j,z})$ selected words for a given pair are distinct and were genuinely absent at $t_{j-1}$. At one stage the cells are disjoint, and across stages the birth intervals are disjoint. Some other name might print a selected word first during the same interval. Its first production is still in the charged cell and interval. This proves (1).

## An adaptive selection rule can be met within a single finite budget

The number of disjoint clock intervals grows on the order of $D/\log D$. Picking an interval of below-average release mass *after seeing its endpoint count* requires information unavailable to an on-time sampler. Even access to the entire history of earlier release counts gives no purely numerical contradiction to (1).

Consider any countable family of prospective rules. Given the past counts $(b_1,\ldots,b_{j-1})$, write $p_{i,j}$ for the fraction of seeds of rule $i$ stopping at $j$. Along every completed history require that each seed stop at most once. Fix positive weights $w_i$ summing to at most one. Recursively set

$$
  b_j=\left\lfloor U\sum_i w_i p_{i,j}(b_1,\ldots,b_{j-1})\right\rfloor .
$$

There is no circular evaluation because only past counts enter the right side. On the realized history $\sum_j p_{i,j}\le1$ for each rule, hence $\sum_j b_j\le U$. Nevertheless $b_j\ge Uw_i p_{i,j}-1$ at every stage for every rule. This construction concerns numerical time totals. It does not furnish a native interpreter or establish the cellwise conditions for all changing partitions. It shows precisely why a pigeonhole argument using only previous time totals and sampler-dependent constants leaves the required contradiction open. Weighted domination has classical precedents in universal semimeasures. [Gács on the classical universal semimeasure](https://cs-web.bu.edu/faculty/gacs/papers/kolmq.pdf)

Lean checks that adjacent integer allocations telescope, their loss to division is less than one index, and a surviving cell pays its allocation in full. The computation and time-distribution results are manuscript proofs. [Lean file](../lean/ClockRelease.lean)
