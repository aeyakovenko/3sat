# A hard set of indices before a SAT solver halts

Fix a correct deterministic SAT solver on the logarithmic-word RAM, a depth $d$, and a modulus $m\ge2$. There is a rational $0<a<1$ and a solver-dependent family of explicit unsatisfiable 3-CNFs of lengths $2^k\le N_k\le 2^k k^{O(1)}$, one at every sufficiently large scale $k$. Put $K=\lfloor k^a\rfloor$, $u=k+K$, and $T=2^u$. Either the solver has yet to halt at $T-1$, or on its actual run there are one output bit $f$ and a set $H$ of exactly $2^{\lfloor3K/4\rfloor}$ distinct indices before halt such that **every** depth-$d$ ACC$[m]$ circuit $C$ of size at most $2^{\lfloor K/3\rfloor}$ satisfies
$$
\left|\Pr_{i\text{ uniform in }H}[C(i)=f(i)]-\tfrac12\right|\le 48/\sqrt K.
$$
The circuit sees the original $u$-bit index. The bit belongs either to the chronological controller $G$ or to the sorted timestamp function $Q$ from the single-index theorem. In the latter case the indices are ranks of prehalt instructions in address order. On an instruction set with multiplication or division, the chronological output includes the canonical native gate evaluations specified there. No time or workspace hypothesis is needed. A global near-linear running-time bound would exclude the first alternative. Both the coordinate and the set can depend on the run. [Single-run theorem and machine model](one-index-solver-memory.md)

## Restricting to the genuine part of the run

Apply the single-index theorem at depth $d+30$ and modulus $m$, fixing $a$ only after this depth is chosen. Suppose the solver first halts at row $E\le T-1$. The controller is constant from $E$ onward. Every timestamp $t\ge E$ is a dummy, and every prehalt timestamp comes before it in address order. Active instructions are sorted first, and prehalt dummy timestamps occur earlier in the dummy group. Hence $Q(i)=i$ for $i\ge E$ and every smaller rank names a prehalt instruction. Each bit of either suffix is a constant or a bit of the index. A circuit correct on $I=\{0,\ldots,E-1\}$ can extend it to all $T$ slots by a comparison with the hardwired $E$ and a selector. The number of output coordinates is polynomial in $k$.

Write $h=2^{\lfloor3K/4\rfloor}$, $s=2^{\lfloor K/3\rfloor}$ and $\epsilon=16/\sqrt K$. Work at sufficiently large $k$ that $\epsilon<1/4$. If $|I|<h$, listing all prehalt values per coordinate and adding the known suffix costs $h\operatorname{poly}(k)<2^K$ gates for all coordinates together, at constant depth. This contradicts the single-index theorem. Thus $|I|\ge h$.

## From weak prediction to an exact trace

Use all circuits of depth at most $d+1$ and size at most $s+1$ as weak readers. Suppose that for each coordinate $f$ and every probability distribution on $I$ with masses at most $1/h$, some weak reader has agreement greater than $1/2+\epsilon$. For a fixed coordinate, finite minimax yields a mixture of readers with mean agreement greater than $1/2+\epsilon$ against every such distribution. Indeed, the capped simplex is the convex hull of uniform distributions on $h$-element sets, and the maximum of finitely many continuous agreement functions attains its minimum. Fewer than $h$ indices can have pointwise success at most $1/2+\epsilon/2$ under the mixture. Otherwise a uniform distribution on $h$ of them would violate this guarantee. Keep those exceptional indices for an explicit table. [Impagliazzo, Hard-Core Distributions for Somewhat Hard Problems](https://doi.org/10.1109/SFCS.1995.492584)

At any remaining index draw $n_0=\lceil16/\epsilon^2\rceil$ independent readers and take their majority, using a fixed tie rule. The chance of error is at most $\exp(-n_0\epsilon^2/2)<1/64$. An OR of ANDs over the threshold-sized subsets of the outputs computes this majority using at most $2^{n_0}+1$ gates and two extra layers. Here $n_0\le K/16+1$.

Use independent copies of this group to build a fixed-depth amplifier. Each bottom AND takes $L=\lceil\log_2 k\rceil$ group outputs. Each OR takes $k^2$ independent bottom ANDs. The final AND takes $k$ independent ORs. At a point with $f(i)=1$ a bottom AND succeeds with probability at least $(63/64)^L$, so the failure probability at the output is at most $k\exp(-k^2(63/64)^L)$. At a point with $f(i)=0$ a bottom AND succeeds with probability at most $64^{-L}\le k^{-6}$, giving output error at most $k^{-4k}$. Both are smaller than $2^{-2k}$ for sufficiently large $k$. A union bound over at most $2^u$ indices leaves some fixing of all readers correct at every nonexceptional index, since $u<2k$.

Override the fewer than $h$ exceptions using equality tests on their full indices, then extend each bit across its known suffix. Independent fixings per output bit suffice. The resulting $G,Q$ have total size at most
$$
\operatorname{poly}(k)\big(h+s+2^{K/16+1}\big)<2^K .
$$
The small readers, the two majority layers, the three amplifier layers, the exceptions, and the suffix selector all fit depth $d+30$. This contradicts the single-index theorem on this formula. Consequently some coordinate has a distribution $p$ on $I$ with atom masses at most $1/h$ under which every weak reader has agreement at most $1/2+\epsilon$.

## Rounding to a uniform set of exactly the stated size

Draw independent inclusion bits with probabilities $h p_i$. The expected set size is $h$ and the expected number of correct indices for any particular reader is at most $h(1/2+\epsilon)$. Additive Chernoff bounds give probability at most $2\exp(-\epsilon^2 h/3)$ of a deviation in size by more than $\epsilon h$, and at most $\exp(-\epsilon^2 h/3)$ that a particular reader has more than $h(1/2+2\epsilon)$ correct indices. The logarithm of the number of circuits in the enlarged reader class is at most $O((s+u+2)^2\log(s+u+2))$ by listing gate types and connections. For a MOD gate, repeated wires can be recorded modulo the fixed $m$. This count in the union bound fits because $s^2=2^{2K/3+O(1)}$ while $\epsilon^2 h=2^{3K/4+O(1)}/\Theta(K)$.

Choose an outcome satisfying all bounds. Add or remove at most $\epsilon h$ positions in $I$ to reach exactly $h$. Every reader now has agreement at most $1/2+3\epsilon$. Negating an original depth-$d$, size-$s$ reader still belongs to the enlarged class, giving the other side of the claimed inequality.

The set may be sparse in the full prehalt domain, and the proof supplies no efficient sampling procedure for it. It can also select a bit of the ordering by work address. These quantifiers leave open average prediction at a uniformly random chronological step and the elapsed-time lower bound for unrestricted SAT. The argument applies the classical hard-core method to the exact trace obstruction and accounts for the fixed-depth majority simulation and the halt boundary. Priority for this trace consequence is unverified.
