# A private-coin program for an explicitly printed word of arbitrary length

**Research journal, 24 November 2026.** Suppose a fixed ordinary sampler publishes a word $y$ by time $t=2^q$ with probability $p>0$, where $q\ge1$. There is a fixed private-coin decoder and a deterministic choice of program of at most $\lceil-\log_2 p\rceil+O(1)$ bits which, with probability at least $0.99$, prints the entire word, consumes exactly the program, and finishes in

$$
t p^{-3}\,\mathrm{poly}(q+\log(1/p)+2).
$$

Here and below the sampler publishes at most once, output is explicit, program input is sequential with no end signal, and the decoder has separate independent fair bits. The length of $y$ can be as large as the sampler's output device permits. A randomized encoder given $(q,y)$ also finds a suitable program within this bound with probability at least $0.99$. Constants can depend on the source and the native simulation conventions. The earlier proof used the rank of the word as part of a bounded integer and required $|y|\le q$. [Short-word theorem and midpoint decoder](private-coin-prefix-coding.md)

## Giving a word and an epoch joint probability

Use the two-branch sampler in the synchronization proof. On its first simulation retain the word and the epoch $j$ of its completion. Its direct branch uses $h=j,d=0$. The other branch estimates the cumulative probability at $j$ by repeated bounded simulations, selects a dyadic threshold $2^{-d}$, then scans for an epoch $h$ by independent cumulative estimates. All tests compare the explicitly published result of a fresh simulation to the retained word. The proof of the crossing probabilities used only equality of words. Thus one branch has a set of runs of probability at least $c_0 p$ giving the same $(y,h,d)$, where $j\le h\le q+1$, $2^d=O(1/p)$, and $c_0>0$ is independent of the target. In the direct branch this uses a completion bin of mass at least $p/128$. In the other branch restrict these runs to the good estimates in the synchronization proof, on which their preliminary trial count is $O(2^d)$. [Probability and stopping estimates](sampling-at-a-numeric-length.md)

Output the ordered pair $(k,y)$, where

$$
k=h+d+C\lceil\log_2(h+d+2)\rceil+C
$$

for a fixed sufficiently large integer $C$. Use a self-delimiting field for $k$ and copy the finite word literally. To check the clock for long words, store the retained word once. In a trial bounded by $2^i$, storing or comparing the fresh output costs at most $2^i\mathrm{poly}(i+1)$ time, with its length recorded. Even scanning the retained word once per trial costs at most $2^j\mathrm{poly}(j+1)$, since the original run printed it by then. In the scan up to $h$ the total number of trials is at most $2^d\mathrm{poly}(h+1)$. Simulations, comparisons, counters and the final copy consequently cost at most $2^{h+d}\mathrm{poly}(h+d+2)$ on the selected runs. This accounting also covers a machine that publishes one logarithmic-size word per step. In particular, there is one fixed sampler $W$ and a constant $c$ such that some pair satisfies

$$
\mu(k,y)=\Pr[W\text{ publishes }(k,y)\text{ by }c2^k]\ge c_0p,
\qquad
2^k\le(t/p)\mathrm{poly}(q+\log(1/p)+2).
$$

## Estimating ordered cuts using only the observed outputs

Order the pairs first by increasing tag $k$, then by word length and lexicographic order. Weigh each pair by its probability of publication by its *own* tag deadline. Their total mass is at most one. For parameters $J,d'\ge1$, run $M=\lceil C_1 4^{d'}(J+d'+1)\rceil$ independent trials through $c2^J$. A trial contributes its pair only if its tag is at most $J$ and its actual completion meets the tag deadline. Otherwise it contributes a sentinel above every valid key. The mean CDF on cuts through tags at most $J$ agrees exactly with the desired cumulative mass. Through this finite clock only finitely many outcomes are possible. Embedding these ordered outcomes into the real line preserves the empirical CDF and both cuts adjacent to each atom.

With $e=2^{-d'}$, the probability that *any* such cut has empirical error exceeding $e$ is at most $2\exp(-2Me^2)$ by the Dvoretzky–Kiefer–Wolfowitz inequality. Choosing $C_1$ large makes the sum over all $J,d'$ smaller than $0.01$. This bound is independent of how many distinct words the sampler could print in $2^J$ steps. Sort just the observed valid keys and keep counts. Each comparison and copy costs at most $2^J\mathrm{poly}(J+d'+2)$ steps, and the list requires $O(M\log(M+2))$ comparisons. Enumerating pairs of parameters by $J+2d'$ gives a total of $2^H\mathrm{poly}(H+2)$ steps through score $H$. [Massart's empirical CDF bound](https://doi.org/10.1214/aop/1176990746)

For an atom of mass $\mu>0$ let $z$ be the midpoint of its cumulative interval. Choose the depth $b=\lceil-\log_2\mu\rceil+5$ cell containing $z$. Supply its address after a three-bit header specifying $b\bmod 8$. Apply the earlier midpoint decoder to the observed keys. It finishes if both cell edges fit inside an empirical atom with margin $e$. It reads eight more bits if some empirical cut lies strictly inside the current cell with clearance greater than $e$. Otherwise it advances to the next table. The empirical cuts needed are zero and the cumulative counts after observed keys. In particular an unobserved key adds no distinct empirical cut. At every such cut used to advance, the true cut at the corresponding valid position is also inside the cell on the simultaneous accuracy event.

At the target table $J=\max(1,k)$, $d'=b$, the target atom is observed since its mass exceeds $2e$ and both adjacent estimates are accurate. Its two empirical endpoints therefore occur in the scan. A proper testable ancestor has width greater than $4\mu$ and contains $z$, so one of the true atom endpoints lies in the ancestor with clearance at least $\mu/2$. The final cell has width at most $\mu/32$ and clearance at least $\mu/2-\mu/32$ from the atom edges. These margins give exact consumption and publication on the common good event. The clock is $2^k\mu^{-2}\mathrm{poly}(k+d'+2)$, including printing $y$. Substitution proves the bound in the opening paragraph.

## Finding the name given the output

Run the original sampler through $t$ on independent trials until a fixed large number of matches for $y$. With the required constant confidence this uses $O(1/p)$ trials and returns a conservative dyadic estimate $u\in[p/8,p]$, as in the short-word encoder. Compute a known bound $N=(t/u)\mathrm{poly}(q+\log(1/u)+2)$ with constants large enough to cover $2^k$ above. Use fresh runs through $c2^{\lfloor\log_2 N\rfloor}$ to estimate the CDF of admissible pairs. With $O(u^{-2})$ trials both cuts of every atom are accurate to $c_0u/16$ with arbitrarily high constant confidence. The qualifying atom of mass at least $c_0p$ then appears, and every empirically selected pair projecting to $y$ with observed mass at least $c_0u/2$ has true mass at least $c_0u/4$. For the selected tag, independently estimate the two endpoints to error $c_0u/1000$ and use the largest dyadic width at most the estimated mass divided by 28, centered by choosing the cell containing the empirical midpoint. The short-word encoder's clearance bounds apply to any ordered atom. Sorting samples and the three independent probability estimates take $Nu^{-2}\mathrm{poly}(q+\log(1/u)+2)$ time on the encoder's good event. Its confidence and the decoder's confidence can each be fixed separately.

This removes an output-length obstruction for *randomized* descriptions. To refute linear SAT via the short-word coding test, a long output would still have to force a failure of deterministic coding within the range covered by a transfer to SAT. Arbitrarily long randomized outputs by themselves give no such transfer. [Deterministic transfer for polylogarithmic-length words](recovering-longer-outputs.md)
