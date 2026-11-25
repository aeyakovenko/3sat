# Adding an instruction and preserving a packed-word deadline failure

Fix the [separate-operation RAM](five-instruction-loops-on-dimacs-sat.md), a fixed admissible logarithmic-width rule, and a real multiplier $0<K<2$. There are explicit finite suites of proper ASCII DIMACS formulas indexed by the number $m$ of editable packed words. For every program with at most $C$ stored instructions, some formula in the suite is misclassified or exceeds the deadline $K\lceil n/w\rceil$, whenever

$$
 (2-K)m>2C+A_K .
$$

The constant $A_K$ is independent of $C,m$ and of the program's literals. Every formula within a suite has the same encoded bit length $n$. If the inequality holds for $C,m$, it therefore holds for $C+1,m+\lceil 2/(2-K)\rceil$. For example, eight additional marked words preserve the inequality when one instruction is added at a deadline of $7/4$ steps per input word. The proof quantifies over **every** replacement program of the larger size. Distinct suites may use different program failures. For every globally correct decider, the all-pristine formula itself exceeds the stated deadline.

## Counting the production of addresses

Use the base from the [homogeneous-word construction](executed-operands-on-homogeneous-sat-words.md) and its $m$ one-sign alternatives. The formula is satisfiable on the base and unsatisfiable after any single edit. There are $h=O(1)$ different initial memory word values, including zero. Only a fixed number $r_0$ of other values is supplied in the initial registers. At most $2C$ word values are present as data literals in the program, since an instruction has at most two source operands. Direct control-flow targets are separate from data. All writable addresses are available.

If a machine answers correctly on the suite, its base run must LOAD the original word at each of the $m$ distinct marked addresses. An edit to a word that the run never observes cannot change its verdict. Each marked address must therefore occur as a numerical value used by the machine. Initially, at most $h+r_0+2C$ of those addresses are available. A register copy, LOAD or STORE copies a previously available value. A branch chooses a finite-control target. Only a data-producing numerical operation can introduce a value outside the initial stock, and it produces at most one such value per execution. Hence the base needs at least $m-(h+r_0+2C)$ numerical instructions in addition to the $m$ LOADs. This proves

$$
 T\ge 2m-h-r_0-2C .
$$

The file at length $n$ uses $m=\lfloor n/w(n)\rfloor-C_D$ marked words with a layout constant $C_D$ and at most $m+C_D+1$ physical words. Taking $A_K$ at least $h+r_0+K(C_D+1)$ proves the criterion. Every sufficiently large integer $m$ occurs: along increasing byte-aligned lengths, $\lfloor n/w(n)\rfloor$ is unbounded and increases by at most one per eight added bits once $w\ge8$. A width change may cause a decrease, which does not skip any value on the next upward crossing. A new suite can be selected at a larger length even when the width changes. [Lean arithmetic for the lift](AddressStockLift.lean)

## The endpoint of exactly two steps per word

Static control supplies a second count which survives the endpoint $K=2$. Let $C\ge1$, let $U$ count nonbranch instructions on the halting base trace, and let $b$ count its branches. A consecutive segment of nonbranch instructions has at most $C$ steps. Otherwise a static instruction repeats within the segment. Its successive program counters then cycle forever independently of the data, contrary to halting. The same reasoning permits fixed unconditional jumps within a segment if counted as nonbranch. Thus $U\le C(b+1)$ and $CT\ge (C+1)U-C$. Both the compulsory LOADs and first numerical productions counted above belong to $U$.

Write $d_0=h+r_0$ using a uniform upper bound on the palette and metadata, and choose $b_0$ so $\lceil n/w\rceil\le m+b_0$. If $T\le2\lceil n/w\rceil$, these inequalities require
$$
  2m\le (C+1)(d_0+2C)+C+2Cb_0.
$$
Consequently a single suite of $m=O(C^2)$ marked positions suffices to defeat every program of size at most $C$ at this exact two-steps-per-word deadline. For a constructive successor, increase $m$ by $\lceil(4C+5+d_0+2b_0)/2\rceil$ when increasing $C$ by one. This is the difference of the two cutoff polynomials divided by two, rounded upward. It preserves a previously strict violation for every rewritten program of the larger size. Equivalently, a candidate passing all these instances under the endpoint deadline needs $\Omega(\sqrt m)$ static slots. The per-program asymptotic lower coefficient from this counting argument is at least $2+2/C$; it approaches two as program size grows. [Endpoint arithmetic in Lean](AddressStockEndpoint.lean)

## What a finite clock forces the code to contain

At a deadline $K\lceil n/w\rceil$ with fixed $K<2$, the same argument forces at least $(2-K)m-O(1)$ different **marked addresses themselves** to be available as immediate values. Each missing one needs its own first numerical production. After subtracting the constant original memory alphabet and metadata, the remaining addresses must be carried by the program. Under ordinary explicit binary charging of literals this costs $\Omega_K(m\log m)=\Omega_K(n)$ bits of text. Indeed among $k$ distinct residues at least $k/2-O(1)$ require integer representatives of absolute magnitude at least $k/4$. Literal truncation modulo the word width cannot create more residues from smaller integers. This count assumes ordinary machine text, with literal uses charged directly or with distinct literal values charged once in a pool.

On the favorable widths of the homogeneous-word construction, an unrolled five-step test per triple meets any fixed deadline strictly above $5/3$ steps per packed word, for sufficiently large files. It uses $O(m)$ instructions with $O(\log m)$ bits each for operands and targets. Thus for $5/3<K<2$ the order $\Theta_K(n)$ of the minimum code-bit cost is attained on those finite edit suites. This upper bound concerns correctness on the promised suites.

## Why the lift stops

The same explicit family also gives a uniform control experiment. A fixed RAM can reconstruct the expected header, seven public clauses, alignment and final suffix from $n$ and the width in $\operatorname{polylog}(n)$ time. It computes the two repeated-word values by appending bytes in registers and checks each physical body word against them in $O(1)$ steps. If every word matches, it accepts exactly when all were pristine. On any other valid file it invokes a complete SAT decider. This program is globally correct and takes $O(n/w+\operatorname{polylog}n)$ steps on the entire edit family. Thus the algebraic size lift proves a sub-two-steps-per-word exclusion for arbitrary fixed code. An unrestricted linear-time lower bound would have to beat **every** fixed multiple of $n$ encoded bits, or equivalently an unbounded multiple of $w$ steps per packed word. This family cannot accomplish that.

The endpoint induction adds the finite-control count to the address count. On a modified file layout, checking which actual word operations can create an input address raises the deadline above two by a uniform constant and gives an additive successor already at two. Both constructions apply to conjunctions of input edits. The eight-bit native census measures an executed deadline on a different finite selector encoding. [Above-two induction](addresses-without-raw-predecessors.md) · [Census on unrestricted program lengths](eight-bit-executed-clock.md)
