# Adding shared producer proofs on every sufficiently late feedback phase

**Research journal, 24 November 2026.** A sound verifier for bad candidates in a feedback mask can be extended by one explicit family of native producers. The family certifies additional candidates on actual failed windows in **every** sufficiently large phase. One can trade the number of new certificates for how far their true heavy-length counts exceed the threshold. This yields intermediate-time first outputs on the original prefix machine. [Feedback masks, clocks and residual cost](adaptive-window-lists.md)

Use the globally prefix-free multitape machine with input only on a one-way stream and cutoff $B(m)=2^{20m}$. Block $j$ has $N=2^j$ lengths $N\le m<2N$. A length is heavy when every $m$-bit word starting with $j$ zeroes is printed by a name shorter than $m$ by $B(m)$. Write $e_j$ for its block's fraction of heavy lengths. In window $s$, let $b_s=2^s$, $W_s=2^{b_s}$, and $I_s=[J_s,J_s+W_s)$ with $J_s=2^{3b_s}$. The feedback mask in phase $r$ consists of the first $2^{-r}W_s$ members of $I_s$. A success means that some mask member has $e_j\le1/W_s$. The phase advances on a success. Each phase ends in a success because the total $\sum_j e_j$ is finite. Previous-window outcomes are computable by exhaustive simulation well within the next window's budget. [Prefix source](prefix-lengths.md) · [Window spacing and budget](shorter-window-proofs.md)

## Filling a specified portion of the residual candidates

Let $V$ be a deterministic test which can scan its verdicts in window order through any candidate $j$ in the allowed online time. The direct tape bound is $2^{\alpha N}\operatorname{poly}(N)$ for fixed $\alpha<10$. The RAM bound is the same with $\alpha<5$ and a square for tape simulation. Let $\ell(r)$ denote the length of the prefix code $E(r)$ consisting of the gamma code of the bit length followed by the low bits of $r$. Choose an integer $g=g(r,d)\ge1$ that is uniformly computable cheaply from $r$ and the fixed parameter $d$. For sufficiently large phases assume $\ell(r)+d+g\le r-1$. Set

$$
   Q_r=2^{-\ell(r)-d-g}.
$$

Start at the beginning of phase $r$. Among offered candidates that $V$ declines, reserve a prefix in their chronological order of *total normalized cost* exactly $Q_r$, if enough exist. Each member of window $s$ costs $1/W_s$. Every reserved $j$ satisfies

$$
   e_j\ \ge\ 2^g/W_s .
$$

This assertion for the reserved candidates does not require $V$ to be sound. Soundness is used to prove that the pool fills and the union with the original test is still sound.

The single native generator reads $\operatorname{gamma}(d)$ and $E(r)$, and recovers the beginning of phase $r$ by replaying earlier windows. The reserved candidates in window $s$ receive adjacent binary cells of length $2^{-L_s}$ in $[0,1)$, with $L_s=b_s-\ell(r)-d-g$. These cells represent normalized costs multiplied by $1/Q_r$. The $L_s$ increase across windows, so every earlier endpoint is aligned with the next grid. There are enough later bits to reach $L_s$ when needed. The decoder stops at its selected cell without reading past it. It can skip empty stages. At any current candidate only earlier decisions, $V$'s current verdict and the already known phase are needed. Learning the actual outcome of this entire window is required only for advancing to a later one, where its exhaustive simulation fits. Negative $L_s$ in initial small phases may be ignored. Under the stated parameter bound and $r\le s$ they do not occur in the sufficiently late phases used here.

At its selected $j$, the decoder reads $j-b_s+g$ raw bits selecting an offset among the first $2^{j-b_s+g}$ lengths in the block. It then reads $m-j$ raw bits, prefixes $j$ zeroes, and prints the resulting word. The choice $g\le r\le b_s$ keeps the offsets in the block. The complete name length, including the fixed header of length $h$, is

$$
  h+|\operatorname{gamma}(d)|+\ell(r)+L_s+(j-b_s+g)+(m-j)
   = m+h+|\operatorname{gamma}(d)|-d.
$$

Choose $d>h+|\operatorname{gamma}(d)|$ *after* fixing the decoder, which reads $d$ from the input. All words of all the displayed lengths now have a short producer. The test for reservation is itself online. Simulate the same deterministic scan through $j$ and check the scaled integer endpoints. The tape decoder's outer interpretation costs at most a square, hence $2^{2\alpha N}\operatorname{poly}(N)$ under the direct tape bound. In the RAM case the total exponent is at most $4\alpha N$. Both lie strictly below the native cutoff since $m\ge N$. Reading the raw offset and output fields adds only $\operatorname{poly}(N)$. These calculations concern a deterministic $V$. If $V$ is instead specified by an existential circuit, the same construction works **under** a SAT hypothesis when the resulting deterministic online scan meets the specified bound. A short witness for membership alone does not supply this native decoder with timely negative answers.

When $V$ is sound for $e_j>1/W_s$, the eventual successful window has a good candidate declined by $V$. That candidate cannot be reserved, by the explicit producer construction. Since the current grid contains all old endpoints, failure to fit its cell means the allocation was already full. The mass newly certified **on failed windows** is therefore at least $Q_r-2^{-r}$, the deduction being the entire mass of the single successful window. With $V$ empty and $g=1$, all the first $2^rQ_r$ windows of the phase are proved to fail. With arbitrary sound $V$, take $g=r-\ell(r)-d-1$. The pool then has exactly two full windows' worth of normalized cost. At least $2^{-r}$ newly certified failed mass has an excess *factor* $2^g=\Theta(2^r/[r(\log(r+2))^2])$ over the ordinary badness threshold. Thus even limiting attention to candidates far above the threshold leaves the old verifier incomplete in every large phase.

## Testing the extension on genuine production times

Take the deterministic base test that certifies $j$ when more than $N/W_s$ lengths are already fully covered by step $2^{3m}$. It directly simulates all short names on tapes at each length, in $2^{8N}\operatorname{poly}(N)$ total tape time through $j$. The newly certified candidates were declined by this test. Among their first $2^gN/W_s$ fully covered lengths, at least

$$
  (2^g-1)N/W_s
$$

each has a word that no short name produced by $2^{3m}$. Yet every word at each of these lengths is produced by the new generator by $2^{(16+o(1))N}$ native steps. This puts genuine first short-producer times in an explicit interval strictly inside $B(m)$ on at least $2^{-r}$ additional failed mass per large phase with the last choice of $g$. It is unconditional for this tape base test.

## What repeated extensions can buy

Applying the construction a second time to the union test certifies a disjoint set, with a new decoder-dependent constant. Any fixed finite number of iterations is valid. In the first extension with $g=1$, the certified mass already has the same $1/[r(\log r)^2]$ order as the previous necessary lower bound on residual failed mass. That lower bound also applies to the *extended* verifier. Recovering this much once does not exhaust what remains. [Residual bound (2)](adaptive-window-lists.md)

The extension can also escape multiple previous verifiers at once. If $V(i,j)$ is a uniformly timely family with all its positive verdicts sound, and scanning the union for $i\le s$ fits one common online budget with strict margin, take that union as the base at stage $s$. The additional strong candidates at sufficiently late phases are declined simultaneously by every fixed finite initial subfamily. This statement requires a uniformly sound family and a clock for its union.

One explicit attempt to sum infinitely many rounds reads an additional prefix-free round tag of length $\lambda_i$. For generators with common $d$ and common $g$, the corresponding pool for round $i$ is at most $2^{-\ell(r)-d-g-\lambda_i}$, by the same name-length identity. Kraft's inequality bounds their sum by $2^{-\ell(r)-d-g}$. Equal budgets for arbitrarily many rounds cannot be obtained by this coding scheme. Similarly, trying to use the extension as its own base test gives circular evidence for a candidate already accepted by that base because only assignments to actually declined candidates receive new names. Neither attempt certifies all failures. A construction exceeding the residual bound while controlling the total remaining cost is still missing.

A different attempted union checks bounded proofs of positive badness statements in a fixed arithmetic theory $T$. Suppose $T$ is consistent, effectively axiomatized, meets the hypotheses for Gödel's second incompleteness theorem, and proves that arbitrarily large indexed blocks are good. A formalized finite Kraft argument suffices for the latter in PA. Uniform reflection asserting that every $T$-proof of badness of length $\le L(j)$ is correct cannot itself be a theorem of $T$ when $L(j)$ provably eventually exceeds the size of the proof obtained by explosion from any fixed contradiction proof. In fact, given a contradiction proof $p$, append a proof of badness for any sufficiently large $j$ at the small cost of writing its formula and the fixed inference. The uniform reflection claim would give badness at every sufficiently large index, contradicting the existence of arbitrarily large good ones and proving $\operatorname{Con}(T)$. The exponential proof budgets here easily cover the numeral and inference. This rules out that uniform self-soundness step. It leaves open individual bounded reflection or a direct construction of producer proofs with suitable lengths. [Related reflection argument](certificate-reflection.md)

Lean checks the parameter-dependent name length, the unsuccessful-window portion of a full pool, and the count of lengths requiring a later producer. The program construction and clocks are manuscript arguments. [Lean file](../lean/ProducerProofExtension.lean)
