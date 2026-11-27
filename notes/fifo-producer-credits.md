# One fixed producer header realizes a scaled halting probability in new outputs

**Research journal, 24 November 2026.** In the word-completion argument, several halting programs can pay for the same future word. Assigning disjoint requests to the programs makes the mass of actual new outputs exactly a fixed dyadic multiple of the prefix machine's halting probability. The assignment can be recognized cheaply when the fast decoder has access to the ordered word ranks. This gives a genuine enlargement of the original verifier and an exact accounting for attempts to iterate it. [Word-completion setup](word-completion-cost.md) · [Globally prefix-free machine](prefix-lengths.md)

Use the same source $U$, deadline $B(m)=2^{20m}$, disjoint windows $s$, offered blocks $j$ and $h=2^{j-b_s}+1$ selected lengths in each block. We require infinitely many successful windows. Each has an offered block with fewer than $h$ heavy lengths. Select any $h$ distinct lengths at each offered $j$ by a timely rule. At a selected length $m$, request each target word outside the sound evidence set $E(j,m)$ once, in a fixed order, at cost $2^{-m}$. Counts and unranking satisfy the bounds in the word-completion note. A success has an actual missing word on these lists irrespective of how the lengths were selected. Maintaining the same lists in subsequent passes will be useful below.

## Credits, cells and deadlines

Fix a decoder that reads $\operatorname{gamma}(d)$ and then simulates a program $p$ on the prefix stream. Count the input bits consumed and the step $t_p$ at which $p$ halts. There is one credit for every halting input of $U$, including programs with empty or malformed output. Its weight and arrival window are

$$
   q_p=2^{-|p|-d},\qquad
   s_p=\max(t_p+1,\ |p|+d+1,\ s_*).
$$

Here $s_*$ is a fixed initial threshold for the clocks. At the start of each window enqueue all arrivals, breaking ties by length and then lexicographically. In increasing window, block and length order, assign the requests to the oldest credit still outstanding. When no credit remains, simply skip requests until the next arrival window. A word is assigned only once. At length $m$, every outstanding balance is an integer multiple of $2^{-m}$. Earlier assigned words used no larger lengths, and arrival makes $m>|p|+d$ for every eligible $p$. Consequently a word never has to split across credits. A batch can be handled by comparing integer counts and balances, without listing every word.

On the actual input branch for $p$, run the same dispatcher. Within its own credit, the request for a word at length $m$ receives one raw binary cell of depth $m-|p|-d$. Assign these cells consecutively starting at zero. Previous endpoints are aligned to the new grid. Each time the decoder reaches a batch paid by $p$, read just enough bits of this field to select or skip its interval. A selected rank invokes the word unranker. Invalid paths do not publish any target word. No part of a matching name is read beyond its cell. The complete name length for the requested output is

$$
   |\mathrm{header}|+|\operatorname{gamma}(d)|+|p|+m-|p|-d<m
$$

for a fixed $d>|\mathrm{header}|+|\operatorname{gamma}(d)|$. The asserted **single prefix** of the native machine includes this particular $\operatorname{gamma}(d)$ as well as the compiler tag. Other values of $d$ give different subtrees. The generator does not need its own header length.

The dispatcher can discover all credits eligible through window $s$ by simulating exact program names of length at most $s$ for at most $s$ steps, keeping a halting name only if exactly its supplied bits were consumed. This takes $2^{O(s)}\operatorname{poly}(s)$ time. Here $s\ll\log N$ for $N=2^j$ in that window, so the overhead fits the polynomial factor in $N$. A large batch needs only its count and one queue comparison per exhausted credit, plus the last partial credit. Balances and grid endpoints through $m$ need $O(m)$ bits. Earlier windows' actual success tests may be replayed at the next window's much larger clock. Direct tape scans of $2^{\alpha N}\operatorname{poly}(N)$ time for $\alpha<10$, or RAM scans with $\alpha<5$, therefore finish after native interpretation by $B(m)$. With the early simulation base of the other note, the new words finish by $2^{17m}$ for all sufficiently large lengths. Choose $s_*$ to skip a fixed finite exceptional prefix.

## The actual mass and its recognition

Every credit clears by the end of the first successful window at or after its arrival. Otherwise that credit has remained outstanding throughout the window, so every request there was assigned. The assigned words now all have short native producers. The other target words already have genuine evidence in $E$. All offered blocks would have $h$ heavy lengths, contradicting success. The raw cell field for each $p$ thus uses exactly unit measure. Across different $p$ the output pairs are disjoint by dispatch, and within a batch unranking is injective. Let $M$ be the sum of $2^{-m}$ over distinct assigned $(m,y)$. Then

$$
       M=\sum_{p\text{ halts}}q_p=2^{-d}\Omega_U .
$$

In particular the tail beyond window $u$ contains all the weight $2^{-d}(\Omega_U-\Omega_{U,u})$, where $\Omega_{U,u}$ counts halts by step $u$. This applies even when the total *requested* mass is not finite. The success condition and **exact requests outside $E$** matter. If spare ranks in a deferred replay may be dummy or duplicated, the identity counts assigned cells and does not in general count that mass of new words.

On feedback masks, the assigned mass on successful windows has a computable sum since the successful window of phase $r$ requests at most $2^{1-r}$. Thus the mass assigned on *failed* windows alone differs from $2^{-d}\Omega_U$ by a computable real. In the early simulation example it measures actual words absent at $2^{3m}$ which acquired a producer in the single displayed subtree by $2^{17m}$. Other programs may produce one of those words earlier within the same interval.

To recognize this subtree's paid words at an offered $(j,m)$, calculate the dispatcher through that batch. If the number paid there is $k_m$, the accepted ranks are precisely the first $k_m$ in the original ordering of the missing words. With lexicographic unranking, binary-search its sorted outputs to test whether a given $y$ is in this prefix, using $O(m+1)$ unranking calls. With a different ordering, one may instead guess a rank below $k_m$ and check its output, if that extra existential test fits the relevant SAT clock. For linear SAT the usual fixed-block elimination permits this when the original computation is timely. An expensive deferred replay does not automatically give timely recognition. In the fast ordered case the whole paid set can be added to $E$, even though its normalized mass is an uncomputable real.

## What a repeated pass does

Keep the same selected lengths and orders. After the first pass the unmet requests in each batch are its remaining suffix. A second first-in-first-out queue takes the initial part of that suffix, so the combined image is another initial segment of the original batch. More generally, consider finitely many passes that receive their credits at window boundaries, have balances aligned to the word grid when used, and use the same ordering. If a batch has cost $x$ and the pre-batch balances are $b_1,\ldots,b_k$, the union pays exactly $\min(x,\sum_i b_i)$. The remaining total balance is $(\sum_i b_i-x)_+$. This follows by successively subtracting the minimum of the next balance and the remaining demand. Starting at zero, the entire union is therefore computed by one scalar queue with the **sum** of the layers' grants. One need not recompute which lengths have the smallest deficiencies or simulate every nested unranker. Changing those lengths adaptively invalidates this particular pooling identity.

This collapse speeds up the accounting. It does not create additional short native names. With separately tagged copies of one shared dispatcher, a prefix-free layer tag of length $\lambda_i$ reduces the allowable credit from a given $p$ to $2^{-d-\lambda_i-|p|}$ for the same length saving. Summing copies pays at most $2^{-d}\Omega_U$. For infinitely many tags the total-capacity bound still follows from Kraft. Treating their sum as a directly usable online grant requires a computable schedule and grid alignment, which the inequality alone does not supply. A single generator that assigns each $p$ to just one layer obeys the same capacity bound without tags. No way to turn this tagged iteration into coverage of all failed requests has been established.

Lean verifies the common-grid finite queue equalities and conservation of credit. The prefix-stream implementation, cutoff estimates and halting-probability identity are manuscript proofs. [Queue verification](../lean/FifoProducerCredits.lean)
