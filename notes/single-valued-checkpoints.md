# A tight conditional count for nondeterministic descriptions with large checkpoints

**Research journal, 24 November 2026.** Assume a uniform deterministic logarithmic-word RAM decides explicit SAT of encoded bit length $m$ in $O(m)$ time, with unrestricted workspace. Under this hypothesis we can count, to leading exponential order, the strings for which *every successful path* of every sufficiently cheap nondeterministic description encounters a tape configuration with a large circuit description.

Goldberg, Hu, Lu, Lyu and Oliveira prove in Theorem 8 that, for each $1/2<\gamma<1$, every dense subset of the strings with nondeterministic Levin complexity at least $\gamma n$ lies outside two-sided nondeterministic time $2^{\varepsilon(\gamma)n}$. Testing all programs of cost $\gamma n$ by expanding their runs into SAT instances can cost $2^{\gamma n}$ per run. The paper supplies no inequality making that reduction a contradiction. I instead tested only the branches with short checkpoint descriptions. The counting and construction below then give an every-length consequence independent of the paper's existential constant. I have not established priority for the conditional count. [Goldberg et al., definitions in §1.2 and Theorem 8](https://arxiv.org/abs/2610.20188)

Daylight, Koolen and Vitányi already proved an abundance result for strings with low unrestricted description length and high time-bounded description length. The count below also charges the time needed to recover a missing extension and imposes the checkpoint condition on nondeterministic successful paths. [Daylight, Koolen and Vitányi](https://arxiv.org/abs/0809.2965)

## Statement

Fix a native, time-efficient universal nondeterministic multitape machine $U$, with ordinary nondeterministic transitions. A program $p$ is an $h$-cost description of $x$ when there is a time $t$ with $|p|+\lceil\log_2t\rceil\le h$, all paths halt by $t$ with output $x$ or failure, and some path outputs $x$. Write $\mathsf{nKt}(x)$ for the minimum cost. Fix a universal machine simulating each fixed multitape machine in quasilinear time. Include all mutable tapes in a configuration. A write-only output can instead be tracked with its length and its contents up to the $n$-bit output limit on successful paths. Read-only program bits and the fixed initial blanks are public.

Fix rational constants $0<\delta<\rho<\gamma<1$. Put $S=2^{\lfloor\delta n\rfloor}$, $k=\lfloor\gamma n\rfloor$. Take $q=2^a$ for $a=\lceil\sqrt{n\lceil\log_2(n+2)\rceil}\rceil$. A checkpoint is a multiple of $q$ along a path, together with its terminal configuration. Its description gives the control state, head locations, output bookkeeping, and a Boolean circuit mapping tape identifier and address to symbol on all reachable cells. Count gate and wire indices in the encoded bit length.

Let $D_n$ consist of strings $x$ of length $n$ with $\mathsf{nKt}(x)\le\lfloor\rho n\rfloor$ for which every successful branch of every $k$-cost description has a checkpoint with description length greater than $S$. Then, under the SAT hypothesis,

$$
 2^{(\rho-\delta)n-O(\sqrt{n\log n})}
 \le |D_n| \le
 2^{(\rho-\delta)n+O(\log n)}
$$

for all sufficiently large $n$. In particular, the cost and configuration conditions apply to the *same* strings. The upper bound holds unconditionally.

## A partial map from programs to outputs

For each binary $p$ of length at most $k$, give its simulation the maximal clock $T_p=2^{k-|p|}$. Define $R(p,y)$ to mean that some branch halts by $T_p$ with $n$-bit output $y$, and has checkpoint descriptions of length at most $S$ throughout. Define $F$ as the set of $y$ for which some $p$ has $R(p,y)$ as its **unique** surviving $n$-bit output. A program with several surviving outputs contributes nothing. Thus $|F|\le2^{k+1}-1$, even though the local filter may make a globally multivalued program appear single-valued.

If a genuine $k$-cost description $p$ of $x$ has even one successful path with small checkpoints, then $R(p,x)$ holds. Every path counted by $R$ is a genuine path. The time bound and global single-valuedness of $p$ imply $R(p,y)$ fails for every other $y$. Hence $x\in F$. This proves the all-successful-path conclusion for every missing output. [Lean check of the restriction and uniqueness implication](../lean/SingleValuedCheckpoints.lean)

## Clock of the membership test

On a common padded horizon $q^{\lceil n/a\rceil}\ge2^n$, use a binary clock, allow halts to stutter, and send nonhalting paths at their individual deadline to an absorbing failure state. The verifier carries times and padding tags separately from the budget for the native configuration. For each non-leaf interval guess circuit descriptions of its $q-1$ internal boundaries, universally choose a child, and continue with that child's endpoints. At a leaf, guess a sequence of $q$ nondeterministic moves. Starting from the circuit for the first endpoint, simulate this segment using its explicit log of writes, check the final control state and head positions, and universally compare the final symbol at one address against the other endpoint circuit. In particular a leaf can verify all its transitions before comparison against an adversarially chosen address. A leaf needs $O((qS+q^2)\operatorname{poly}(n))$ word steps, including evaluation of a size-$S$ circuit on a read. One may use a bound of the same order to validate the description syntax and verify the terminal output. A multitape path reaches at most $2^{O(n)}$ cells, so every address takes $O(n)$ bits. Endpoints represent full configurations, which lets branches chosen independently in consecutive intervals concatenate. [Segment test and configuration encoding](linear-sat-batches.md)

There are $O(n/a)$ alternating blocks. Their initial encoded size is at most $(qS+q^2)\operatorname{poly}(n)$ times a polylogarithmic reduction overhead, including checkpoint bits and uniform generation. Each elimination multiplies encoded size by at most a fixed power of its logarithm. The logarithm of the size remains $O(n)$ throughout, since the initial logarithm is $O(n)$ and each of $O(n/a)$ stages adds $O(\log n)$. Thus the test for $R$ runs in deterministic RAM time

$$
 M = S\,2^{O(\sqrt{n\log n})}.
$$

Bounded runs of this fixed deterministic test for either answer admit existentially certified RAM transcripts. Wrapping the program guess, the condition $R(p,x)$, the universal exclusion of a second output, and the prefix-extension query “is any extension outside $F$?” costs only a fixed number of additional blocks and polylogarithmic factors. These bounds include producing the explicit SAT instances. [Uniform elimination and transcript verification](linear-quantifiers.md)

## Producing and counting missing extensions

Fix a prefix length $b$. Each prefix with no missing extension accounts for $2^{n-b}$ distinct elements of $F$. Thus at least a $1-2^{k+1-n}$ fraction of the $2^b$ prefixes have a missing extension. From such a prefix recover its first missing extension by $n-b$ prefix queries. Encode the prefix literally with $n,b$ and a fixed decoder, using $b+O(\log n)$ bits. The deterministic RAM recovery has time $M\operatorname{poly}(n)$.

For the native nondeterministic machine, guess the recovery algorithm's RAM transcript, including its short output, verify it, and print only the checked output. A fixed multitape verifier scans the transitions, sorts the address records by address and time by mergesort, and checks initialization and successive read values. It verifies operations on $O(\log M)$-bit words in polynomial word-bit time. The verified transcript takes $M\operatorname{poly}(n)$ native time including universal simulation. Use a fixed sufficiently large clock constant to reject overlong guesses. All paths halt by this clock, and exactly the true output is possible on any successful one. Consequently the recovered extension has cost at most $b+\log_2 S+O(\sqrt{n\log n})$. Different prefixes yield different strings. Taking $b=\lfloor(\rho-\delta)n-C\sqrt{n\log n}\rfloor$ with sufficiently large fixed $C$ proves the lower estimate.

Conversely, a $t$-step successful path has at most $O(t+1)$ visited cells. Listing their addresses and symbols gives a lookup circuit of encoded size $(t+1)\operatorname{poly}(n)$ at every checkpoint, since $\log t\le n$. On a string in $D_n$, take a description of cost at most $\rho n$. Its successful path therefore takes at least $S/\operatorname{poly}(n)$ steps. Its program has length at most $(\rho-\delta)n+O(\log n)$. Each globally single-valued program gives at most one output, proving the upper estimate.

## Where the SAT argument stops

The elementary counting ceiling agrees in its leading exponent with the family constructed under linear SAT. To force a contradiction from this count one would need an independent uniform deficit in the supply of such descriptions or an algorithm that converts their successful computations to small checkpoints within the original cost budget. For example, even a general time-to-space simulation would need to preserve the combined length and time budget on the replacement description. The count supplies neither improvement. [Williams, *Simulating Time with Square-Root Space*](https://arxiv.org/abs/2502.17779)
