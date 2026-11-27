# A smaller last-stage formula for one checkpoint selector

**Research journal, 24 November 2026.** In a checkpoint-list test one nondeterministic index selects two entire configurations. That common selector saves a logarithm in the cost of encoding the list for the last SAT call. It improves the single-level exclusion to $b>3a+9$ on the specified packed model. The previously recorded mixed checkpoint method already does better. A comparison of proof rules below shows why this particular local improvement cannot advance its numerical frontier. [Packed 3-CNF model](packed-band-transfer.md) · [Existing mixed rule](mixed-checkpoint-profiles.md) · [FLMV, especially Lemma 5.3](https://lance.fortnow.com/papers/files/tst.pdf)

## Word-bit transposition and literal names

Give a nondeterministic verifier an ordinary public input of $n$ words and a separate public array of $P$ rows of $S$ words. It selects one row by a single index $j$ and then runs for $R$ steps on the selected row and the ordinary input. Two successive rows can be paired by duplicating the table entries, with constant-factor cost. Include the selected endpoint loading and legality checks in $R$, with $R\ge S$. Write $L=\Theta(\log H)$ for the common address width in the checkpoint construction, where all relevant times and sizes are within fixed logarithmic factors of the reference clock $H$, apart from possibly smaller ordinary inputs. Assume words of $O(L)$ bits. Append dummy rows to round the row count to a power of two and require $j<P$.

Choose a power of two $g$ of order $L$ satisfying $2^g\le\sqrt H$; if the padded row count is smaller, take $g$ to be that count. Write the row index as a group label and an offset $d<g$. For all $0\le \tau<2^g$, make Boolean wires $T_\tau$ with the meanings “bit $d$ of $\tau$.” Obtain the one-hot wires $[d=k]$ by a decoding tree of size $O(g)$, use $T_0=0$, and for every nonzero $\tau$ use the gate equivalence
$$
       T_\tau=T_{\tau\mathbin{\&}(\tau-1)}\oplus[d=\nu_2(\tau)] .
$$
Clearing the rightmost one proves the meaning for every value of the *same* unknown $d$. Construct one-hot group labels as well.

For each group, output-word position and bit lane, pack the $g$ public bits across the rows into the literal number $\tau$. Reference $T_\tau$, gated by that group's selector, and OR the gated terms over groups. This produces the exact bits of the selected row. The selector costs
$$
        O(2^g+g+\lceil P/g\rceil S L)
             =O(\sqrt H+S L+P S)
$$
bounded-fan-in gates. If one group suffices an output is just one literal reference. Each gate equivalence has $O(1)$ width-three clauses and every binary literal name has $O(L)$ bits. The circuit depends on the actual public list. The generator can construct each $\tau$ with a naive $g$-word column scan. Across the array this uses $O(PSL)$ native steps after constant-factor padding. Emitting all clauses takes $O((\sqrt H+SL+PS)L)$ native steps even if writing one bit at a time. Computing the public $\nu_2$ values in order takes linear total time in $2^g$ by counting trailing zeros. All indexes, including numbers below $2^g$, fit in a constant number of words. No random-access guarantee on the generated formula is needed at this final conversion.

Bind these output wires as the initial value bits of the $O(S)$ selected-row records in the ordinary access-checking circuit. They can be included with the $O(R)$ trace records in its permutation network because $R\ge S$. The ordinary $n$ public words use the pre-existing materialized reduction. With its compiler and an $O(N\log^a N)$ SAT solver, the resulting deterministic simulation costs, for fixed $a\ge0$,
$$
          O(RL^{a+3}+nL^{a+2}+PSL^{a+1}+\sqrt H\,L^{a+1}).
$$
The last term is harmless for all the fixed checkpoint clocks in question; alternatively choose the table bound using $R+n+PS$ instead, which is polynomially comparable to $H$. The selector generator and full SAT input may be stored in the final complementary machine, which has no space cap. Any larger packed workspace assumption is used earlier, when the original deterministic simulation must have short snapshots. [Ordinary input and memory-access compiler](materialized-input-census.md)

## What one direct collapse buys

In the packed convention $A=a+3$, $p=a+2$, $q=a+1$, $B=b-2$: the real balanced simulation takes time $HL^A$ and has $O(H/L^B)$ words per snapshot. Split it into $P=\lceil L^x\rceil$ segments. The word length of the list is $O(PS)$ and the defect test has $R=O(HL^{A-x}+S+\mathrm{poly}(L))$. Use the last-stage reduction above on the nondeterministic choice of defective segment; a deterministic SAT decider can serve either complementary polarity. Including the universal list and ignoring the ordinary input term $n L^p$ and sublinear table setup, the time exponents relative to $H$ are
$$
                 2A-x,\qquad x-B+q,\qquad A-B.
$$
With $x=(2A+B-q)/2$ the first two equal $(2A+q-B)/2$. If $B>2A+q$, all are negative. On the quadratic hierarchy clock $nL^p=o(H)$ and the result contradicts complementary-time diagonalization. In original units this excludes $b>3a+9$. A single direct collapse with the ordinary public-list charge $p$ needs $b>3a+10$. Neither statement supersedes the published-in-this-journal mixed calculation $b\ge1.71828175a+6.15484525$.

## Why this primitive cannot advance the mixed threshold

Use exactly the old mixed constant-depth checkpoint rules, extended by allowing the special direct conversion just proved at any level. Normalize with $\rho=p/A$, $\eta=1/A=1-\rho$ and $c=(B-p)/A$. A level has work $d$, shifted ordinary-input floor $f$ and shifted own-list floor $\ell$. Ordinary profiles have $\ell=f$; the new *direct* primitive has $(d,f,\ell)=(1,0,-\eta)$. Its $n$-word input still pays $p$. For levels indexed outside-in, write $D_i=\sum_{h\le i}d_h$, $D_0=0$, $v_i=\ell_i+D_{i-1}$ and $F=\max_i(f_i+D_{i-1})$. Before the first proposed negative exponent all work coordinates are nonnegative. The balanced term, nonnegative-width floor and innermost endpoint cost are
$$
  E=\frac{1+\sum_i(v_i-c)+D_k}{k+1},\qquad
  \max_i(v_i-c),\qquad D_k-\rho-c .
$$
The last cost comes from paying to replay or copy the innermost endpoints even on a short final segment. Charging previously selected endpoints as ordinary input can add further $f_i+D_{i-1}-c$ terms; all such terms are negative whenever $F<c$. This accounting applies the same endpoint convention as the existing proof. A derived generic simulation has ordinary input floor $F$ and pays that floor on any list when reused. The primitive does not assert that a SAT solver on its generated input itself accesses the old list through one common index.

For every $2/3\le c<1$, adding this primitive gives **no finite negative proof unavailable to the ordinary rules**. Already the ordinary base $(1,0)$ followed by one ordinary single-level transformation provides $(d_*,0)$ with $d_*=1-c/2\le2/3\le\rho$. The endpoint and width floors are smaller than $d_*$, and the input guard holds. Thus $d_*\le 1-\eta$, the sum of the special primitive's work and list floors.

Here is the replacement argument. A derived generic profile with $F\ge c$ cannot be used to obtain a negative exponent or as a level in a useful intermediate profile with floor below $c$: its own list costs at least $F-c\ge0$ in the former case and its ordinary input floor is inherited in the latter. Only the direct primitive may have unequal floors. In a final negative tuple any ordinary level must have $f_i+D_{i-1}<c$. If the terminal level is special its endpoint cost forces $D_{k-1}<c+\rho-1=c-\eta<c$. A special level before the end is impossible: it adds one to the prefix, ruling out any subsequent ordinary level by its list floor and a terminal special by its endpoint charge. Thus any negative tuple has $F<c$ even if it uses the primitive. A nonnegative intermediate tuple with $F<c$ likewise has at most one special level, and it must be last, since any following level inherits a prefix of at least one.

Replace that terminal level by the available ordinary $(d_*,0)$. The ordinary floor stays the same. The sum governing $E$ does not increase because $d_*\le 1-\eta$. The endpoint charge decreases. The increased terminal list floor is $D_{k-1}-c<0$, so it cannot worsen any nonnegative target exponent or prevent a negative one. The other endpoint and guess charges are covered as before. Replacing componentwise better previously derived profiles only helps. Inducting through the finite proof replaces every use of the new primitive needed to reach the first negative result. For any intermediate whose work had been weakened to satisfy an input guard, one may perform the same weakening after replacement.

In particular the previously checked obstruction at $c=0.71825$ still applies to this extension. At linear time this is $b=6.15475$. A lasting improvement in the numerical band requires a different transfer effect, for example a cheaper charge for arbitrary public data *after* a deterministic SAT computation has made data-dependent probes of the selector representation. The shared-selector construction only handles the stage before those probes. This is a limitation of the defined rules, not of other lower-bound arguments. [Original finite lower envelope](mixed-checkpoint-profiles.md) · [Selector and profile audits](../audits/shared_selector_checkpoint_audit.py)
