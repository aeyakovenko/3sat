# Counting randomized RAM runs along a fixed address trace

There is a fixed $\sigma_3>0$ with the following property. Take a perfectly correct randomized SAT solver in the clocked word RAM below. Suppose its distribution of address traces is the same on all **satisfiable** files in the dense ASCII list reduction at encoded length $n$. It may have any distribution on unsatisfiable files. If it takes at most $T$ word steps on every tape and the processor can be implemented with $g(w)$ Boolean gates per step at word width $w=\Theta(\log n)$, then at every sufficiently large byte-aligned length
$$
       T\bigl(g(w)+w\bigr)=\Omega\bigl(n(\log n)^{\sigma_3}\bigr).
$$
The trace may change with the input for **each fixed random tape**. When $g(w)=w^{1+o(1)}$, this forces at least $(n/w)w^{\sigma_3-o(1)}$ steps. The exponent is for the field $\mathbb F_3$. The estimate uses a lower bound for a tensor network that sums over the tapes. [List-volume theorem over each finite field](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/MatrixExponent/BatchDescent/Hard.lean#L17-L29) · [Dense DIMACS projection](checking-the-sat-circuit-bound.md)

## RAM and transcript conventions

Use a fixed program with a fixed number of word registers, constant-arity word operations, and ordinary random access to the physical input and writable workspace. Count a bounded number of ordered memory slots per step. A slot emits a physical address or an idle symbol. Count its time position in the trace. This permits branching, address/data computations from earlier reads, and early halting by padding the clock. Accesses to different physical arrays include the array identity. Read versus write and the values moved need not appear in the trace. For multiple slots per instruction, split it into a constant number of phases.

The gate cost $g(w)$ includes control and local computation using the fixed registers. At most $b=O(w)$ fresh fair bits can be obtained at each step. Assign an independent block of $b$ tape bits to each step and ignore unused bits. A program that requests a data-dependent number of fresh bits has the same execution law under this convention. Bits saved by the program can be read again from registers or its charged memory. Denote the padded tape length by $R=bT$. The bound charges for these bits. It assumes a worst-case time bound and correct answers on every tape on the indicated promise. Merely bounding expected Las Vegas time does not supply the finite padded clock used here.

Perfect obliviousness commonly refers to equality in law of observed access sequences. The hypothesis here specifies clocked slots, or a bounded-cost processor transition per observed slot. Equality in law only after deleting idle slots need not preserve the timing information used by this proof. Online ORAM bandwidth lower bounds, and offline ORAMs with free local computation, have other hypotheses and cost measures. [Boyle and Naor](https://eccc.weizmann.ac.il/report/2015/146/) · [Larsen and Nielsen](https://users-cs.au.dk/larsen/papers/oram.pdf)

## Normalizing one fiber

Write $f(x)$ for the SAT answer on a projected input. For a trace $z$ of $T$ steps (expanded by the fixed number of slots per step), let $c_z(x)$ be the number of padded tapes whose run on $x$ produces $z$. On every input,
$$
              \sum_z c_z(x)=2^R.
$$
Because $2^R$ is a unit in $\mathbb F_3$, at least one fiber has nonzero mass modulo three. When the counts are independent of the satisfiable input, choose such a trace on one satisfiable input. Its nonzero residue $c$ works for every satisfiable input. This also works if equality of the counts holds only modulo three.

Simulate the processor along this one trace on the real formula and an as-yet-unfixed tape. Check the computed address or idle symbol against the specified symbol at every slot. For each address thread a word along its consecutive occurrences in the trace, starting from its physical input word or initial zero. A conditional write updates this word. A read uses the current word. Since the trace is fixed, these connections are fixed wires. If the machine supplied a mismatched address the simulation may thereafter use arbitrary replies, because a mismatch has already falsified the trace check. By induction the simulation passes all checks exactly on the tapes in the genuine fiber. It costs $O(n+R+T(g(w)+w))$ ordinary bounded-fan-in gates and wires. Fanout, equality tests, maintaining the predicate for validity so far, and multiplexing written values are included.

Let $A_z(x,\rho)$ be the bit that the trace matched **and** the simulation accepted. All tapes are correct, so summing $A_z$ over $\rho$ gives $c_z(x) f(x)$ as an integer. In $\mathbb F_3$ the sum of $c^{-1} A_z(x,\rho)$ therefore gives $f(x)$ on both signs. A deterministic bit circuit for the trace predicate is a trivalent network with one consistent assignment to its inner gate wires per exterior input and tape. Sum over the tape wires. To obtain the distinctness bit on the raw list, use the per-tape scalar
$$
                    2^{-R}-c^{-1}A_z(x,\rho).
$$
The dense projected formula is satisfiable exactly on lists containing duplicates, so the contracted scalar is distinctness. Its final fixed-field value can be produced by a constant-size tensor on the decision bit. This directly handles complementation after summing. The projection uses constants and copies and has encoded length $n$ comparable to the raw bit length. Padding supplies every sufficiently large byte-aligned length. The list-volume theorem proves the displayed time bound. For general SAT programs the hypothesis need hold only on the projected files used in the reduction.

## An unconditional tradeoff for several traces

Let $M$ be the finite matrix over $\mathbb F_3$ on satisfiable projected files $x$, with one column per trace $z$ and $M_{x,z}=c_z(x)\bmod3$. Every row sums to $2^R$, so the all-ones vector belongs to the column span. Choose a set $S$ and nonzero coefficients $a_z$ such that
$$
                \sum_{z\in S} a_z M_{x,z}=1\quad\text{for all such }x.
$$
Some choice uses at most $\operatorname{rank}_3(M)$ traces by taking a column basis. A smaller selection can suffice. Put $U(S)$ equal to the number of distinct nonempty prefixes of the selected traces, using the expanded slot length up to a constant factor. Then, for **each** such weighted selection and every correct randomized solver, regardless of its trace distribution,
$$
               n+R+U(S)\bigl(g(w)+w\bigr)
                         =\Omega\bigl(n(\log n)^{\sigma_3}\bigr).
$$

To see this, simulate each prefix once, sharing its state with its child prefixes. Every node uses the random bits indexed by the actual clock, shared across all nodes at that depth. Along a root-to-node path the previous occurrence of the current address is fixed. All such connections across the prefix tree and all processor fanouts cost $O(U(S)(g(w)+w))$ wires. An input bit or tape bit may be used at numerous nodes, and the consumed input positions of the simulated gates already cover those uses. Each leaf yields the accepting trace indicator there. Over the common tape, sum the scalar $2^{-R}-\sum_{z\in S}a_z A_z(x,\rho)$. The arithmetic accumulator over the fixed field costs $O(|S|)$ Boolean gates and a final bounded-arity scalar tensor. On a satisfiable input the acceptance term contracts to one. On an unsatisfiable input all accepting indicators vanish. This computes distinctness and proves the tradeoff.

For example, if the tape law on satisfiable inputs depends on an $h$-bit value, $M$ has at most $2^h$ different rows. The rank bound and $U(S)=O(T|S|)$ imply
$$
          2^h T(g(w)+w) = \Omega\bigl(n(\log n)^{\sigma_3}\bigr).
$$
The law may in fact depend on more values and still have small rank. A deterministic program is the case in which different satisfiable traces correspond to disjoint indicator columns. Every such trace must then appear in a selection, since omitting it zeroes a row. The existing [possible-last-writer simulation](matrix-list-unit-sat.md#testing-the-transfer-on-a-ram) counts a different property of the executions.

## Hitting a nonzero digit of a trace count

The selected traces need not even span the constant vector. Let $e_z(x)$ count the **accepting** tapes with trace $z$. Suppose there is a collection $S$ and positive integers $d_z$ such that on every satisfiable projected file some $e_z(x)$, $z\in S$, is not divisible by $3^{d_z}$. Assume no tape accepts an unsatisfiable file. The following bound holds even if some tapes reject a satisfiable file:
$$
     n+ \left(\sum_{z\in S}3^{d_z}\right)
            \bigl(R+T(g(w)+w)\bigr)
               =\Omega\bigl(n(\log n)^{\sigma_3}\bigr).
$$
For $d_z=1$ a trace occurring with residue one on some satisfiable inputs and two on others already counts as a hit on both. For instance, the three rows $(1,0,3),(1,1,2),(2,0,2)$ of a four-tape channel need all three columns in a linear cover. The first column alone has nonzero residue in each row, so its square is identically one modulo three.

To count a higher digit, fix $z$ and let $k=3^j$. Simulate the fixed trace on $k$ independently supplied tapes and require the tapes to be in strict lexicographic order and to pass the matched-and-accepting test. The number of satisfying tuples is exactly $\binom{e_z(x)}{k}$. Each order comparison costs $O(R)$ bounded-fan-in gates. If $e=\sum e_i3^i$, expand $(1+X)^e=\prod_i(1+X^{3^i})^{e_i}$ over $\mathbb F_3$. The coefficient of $X^{3^j}$ is $e_j$, the $j$-th ternary digit. Thus the exact distinctness bit is
$$
       \prod_{z\in S}\prod_{0\le j<d_z}
          \left(1-\binom{e_z(x)}{3^j}^{\!2}\right)
          \quad\text{in }\mathbb F_3.
$$
On an unsatisfiable file every digit is zero. On a satisfiable one at least one tested digit is a unit and its square is one. Implement each factor on two independent ordered bundles of $k$ tapes. Let $B$ be the bit asserting that both bundles pass their tests. The sum over those $2kR$ tape bits of the scalar $2^{-2kR}-B$ equals the displayed factor. Allocate separate tapes to every factor so their contractions multiply. Since $2\sum_{j<d}3^j=3^d-1$, the claimed cost includes the ordering checks, the replicated trace verification, and the input fanout. This construction uses the trivalent tensor model's sum over internal wires. A deterministic search over all of those tapes would have a different clock.

## How a statistically close trace law can escape this argument

Let $h$ different inputs have traces in $\{0,1,\ldots,h\}$. On input $i$ allocate one tape to trace $i$ and all $2^R-1$ others to trace zero. For even $R>0$, any two laws have total variation distance $2^{-R}$. Their common column vanishes modulo three, since $2^R-1$ is divisible by three. The exceptional columns form the identity. Every cover must use all $h$ exceptional traces. The same issue arises simultaneously over any fixed list of odd prime characteristics by choosing $R$ a common multiple of their $p-1$. This example can be implemented by a read of a public-position input word followed by either a fixed dummy probe or an input-indexed probe according to the fair coins. Its verdict can be constant. The example demonstrates the gap between statistical closeness and a sparse modular cover. Higher digits can still be used here by paying for the ordered tape bundles. The example does not establish hardness of computing its verdict.

A general solver may reveal arbitrarily many input-dependent address traces. In particular the list promise admits a radix or dictionary algorithm in $O(n/w)$ word steps for the corresponding packed lists. This usage of the list theorem alone still does not exclude $O(n)$ word steps for SAT in encoded bits. Priority for the randomized trace lemma has not been established. [Word-RAM algorithm and prior deterministic trace counts](matrix-list-unit-sat.md#testing-the-transfer-on-a-ram)

The [Lean checks](TraceMultiplicityCover.lean) cover the nonzero fiber, its normalization, weighted recovery under perfect correctness, and vanishing of the common residue in the rare-exception example. The network simulation, finite-dimensional basis argument and asymptotic estimate are given above. The [enumeration](trace_multiplicity_cover_audit.py) finds the smallest cover for all 3,375 channels with three rows, three traces and four tapes, replays a perfectly masked read on a two-unit SAT test, verifies 50 rare-exception channels, and checks the digit identity and separating product on finite multiplicities. Run `lean TraceMultiplicityCover.lean` and `python3 trace_multiplicity_cover_audit.py`.
