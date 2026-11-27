# What one short winning strategy per opponent would separate

On the calibrated RAM diagonal, a clocked machine with only existential choices covers one padding per opponent exactly when some language at its nondeterministic time bound escapes the deterministic diagonal clock. A finite alternating proof that charges only its positive strategies gives such a machine by running the positive certificate checker. This converts a proposed compression argument into a concrete test of its consequences. The quantifier over successful paddings can also be read exactly at individual lengths or under uniform random padding.

## The clock and the existential program

Write a valid self-delimiting prefix as $p=(P,c)$ for a deterministic RAM program and a positive integer. The input is $x=py$, $n=|x|$, and $L(n)=\lceil\log_2(n+2)\rceil$. Fix $T(n)=n^r$ with integer $2\le r\le9$. Run $P$ on **all of $x$** for at most $\min(c,L(n))T(n)$ guest steps. Set $J^*_T(x)=1$ exactly when $P$ rejects by this deadline. Call $1-J^*_T(x)$ the saturated bit, which is one on timeout. Use the journal's packed machine of width $12L(n)$ with initially zero work memory. Malformed prefixes receive a fixed default. Take a nondecreasing clockable $u$ with $n\le u(n)\le n^4$. All machines are uniform and constants in their time bounds are independent of the input. [Calibrated diagonal and total alternating games](padded-game-separation.md) · [Native instructions and width conversion](native-unary-clock-band.md)

A clocked nondeterministic program $V$ has value $V(x)=1$ if some branch accepts. All branches halt within $O(u(n))$. A padding is successful if $V(py)=J^*_T(py)$. The following statements are equivalent.

1. There is such a $V$ for which each valid $p$ has successful paddings at arbitrarily large lengths.
2. There is an $H\in\mathrm{NTIME}_{\rm RAM}(u)$ outside $\mathrm{DTIME}_{\rm RAM}(T)$.

For $1\Rightarrow2$, take $H=\{x:V(x)=1\}$. If a deterministic $D$ decides $H$ in $O(T)$ steps, take a prefix $p=(D,c)$ with $c$ above its time coefficient. On all sufficiently long extensions of that prefix the diagonal flips $D(x)$, contradicting success.

For $2\Rightarrow1$, run the nondeterministic recognizer of $H$ on the suffix $y$. For each fixed valid $p$, define a deterministic machine $D_p$ on $y$ that returns the saturated bit of the opponent on $py$. The fixed prefix costs only an additive constant in length. Since its coefficient $c$ is fixed, $D_p$ runs in $O_p(T(|y|))$ time. There is an **exact identity** between the successful suffixes and $\{y:D_p(y)\ne H(y)\}$. Finitely many such disagreements would put $H$ in deterministic $O(T)$ by hardwiring their corrections. Lean verifies the equivalence assuming self-prefix inversion, the saturated simulation, closure under finite corrections and lifting a language to suffixes. [Formal quantifier argument](../lean/CalibratedCylinderSeparation.lean)

The simulator on $x$ can parse any prefix in $O(n)$ time. It reads packed words of the suffix using a bounded number of original input loads and evaluates the guest with its width $12L(|y|)$. A guest word guess is one host guess with the excess bits masked away. For $D_p$, the prefix and a bounded number of packed reads of $y$ supply each virtual input word of $py$. Its guest width can be larger than the host width by a fixed factor for all sufficiently long $y$. The fixed-depth sparse-memory simulation and constant-limb arithmetic cost $O(1)$ per guest step after setup costing $O(|y|+1)$. At the stated clocks the number of allocated rows times the digit radix $O(|y|^{1/4}+1)$ fits the $12L(|y|)$-bit host address space for every fixed $p$ at large lengths. Finite small lengths can be hardwired. [Sparse address and division implementation](native-unary-clock-band.md)

## Positive size bounds and free negative proofs

Let an alternating program $M$ have the prefix-forgetting strategy format. A positive proof may take one player-1 action at its own choices and must include every action at player-0 choices. The roles reverse in a negative proof. Either proof is finite. A real input admits at most one of the two signs, even if some unrestricted plays never halt. Fix a uniformly constructible global positive size cap $1\le b(n)\le n^4$ with construction time $O(n+(b(n)+1)L(n))$.

Assume that on some arbitrarily long extensions of every valid $p$, the correct $J^*_T$ sign has a positive proof within $b(n)$ if the sign is one, or a finite negative proof of any size if the sign is zero. Then the language

$$
A_b=\{x:M\text{ has a positive proof of size at most }b(|x|)\}
$$

belongs to $\mathrm{NTIME}_{\rm RAM}(n+(b+1)L)$ and lies outside $\mathrm{DTIME}_{\rm RAM}(T)$. Run the positive proof checker with an explicit clock. On a successful positive padding, one branch accepts. On a successful negative padding, every branch rejects because even an uncapped positive proof would contradict the negative strategy. Thus the same paddings give the existential coverage above. The forward proof of the equivalence applies at this running time even if it slightly exceeds $n^4$. That cap was used for the original trie checker. [Exact checker and opposite-sign exclusion](strategy-dag-certificates.md)

The reverse conversion needs no tree of shared states. Use the existential program for $H$ on $y$ from the preceding proof. When it accepts, an accepting path is a positive DAG of $O(u(n))$ size with no forgets. When it rejects, the full clock-bounded tree is a finite negative proof. Each word choice has finitely many actions at every fixed input length. The tree can be much larger than the clock. This gives the upper and lower time scales for the partial-DAG criterion, with one factor of $L$ from checking arbitrary merges. If a positive size estimate has an unknown constant depending on $p$, it converts to a single constructible cap after multiplying by any diverging clockable factor within the allowed range. An exponent or logarithmic strict margin can absorb that factor.

For the ordinary SAT target take $r=8$ and $a\in\{2,3\}$. If a clocked existential machine covering the calibrated diagonal runs in $u=O(n^{8/a}/L^{3+\epsilon})$ for fixed $\epsilon>0$, its native acceptance query has clock $O(u)$ and its ordinary 3-CNF has $O(u L^3)$ bits. A deterministic $O(N^a)$ SAT solver would decide its language in $O(n^8/L^{a\epsilon})$, contradicting the equivalence. The same driver works for the uncalibrated cutoff $n^8$ since this is $o(n^8)$. For an arbitrary partial-DAG checker the corresponding positive size cap is $O(n^{8/a}/L^{4+\epsilon})$. The logarithm saved for an existential path comes from directly simulating the verifier. The existence of either covering program at these scales is unresolved. [Virtual packed compiler](packed-band-transfer.md) · [Original diagonal calculation](strategy-dag-certificates.md)

## Length frequency and density of successful paddings

The proof also compares more demanding notions of coverage. In the first row of the table a machine agrees on a length when it is correct on **all** inputs of that length. In the second row the fractions refer to independent uniform bits at the indicated fixed length.

| Coverage required for every fixed prefix $p$ | Equivalent property of some $H\in\mathrm{NTIME}_{\rm RAM}(u)$ |
| --- | --- |
| At least one success at every sufficiently large length | Every deterministic $O(T)$ machine agrees with $H$ on only finitely many lengths. |
| The successful fraction of suffixes has strictly positive limit superior | For every deterministic $O(T)$ machine $D$, its error fraction on $H$ has strictly positive limit superior. |

For the forward implication, take any such $D$ and its calibrated prefix $p=(D,c)$. Every success on that cylinder is an error of $D$ on the language of $V$ at that length. The cylinder accounts for the fixed fraction $2^{-|p|}$ of the whole input cube. The density bound may depend on $D$. For the converse use the suffix recognizer and the exact disagreement identity for $D_p$. Appending $p$ just shifts lengths by $|p|$, and uniformly random suffixes correspond to uniformly random inputs to $D_p$. The same reasoning works with positive limit inferior in both density statements. A clocked alternating-DAG checker with the corresponding stronger positive/negative coverage inherits the forward implications. Infinitely-often agreement on an entire length is the usual complexity-theoretic convention. [Fortnow and Santhanam](https://arxiv.org/abs/1012.2034)
