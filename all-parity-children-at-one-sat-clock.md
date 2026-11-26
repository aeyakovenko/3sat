# All parity children of one residual SAT instance at a linear deadline

Suppose proper explicit DIMACS 3-SAT has no deterministic $O(n^k)$ algorithm on the logarithmic-word RAM with unrestricted workspace. Fix a finite nonempty list of correct solvers and $C>0$. For arbitrarily large source lengths $n$, there is a satisfiable residual problem and a set of $d$ independent binary parameters of its ambient affine space such that **every listed solver takes more than $CN$ steps on both polarities of every nonzero linear test on those parameters**. All $2(2^d-1)$ test files have the same bit length $N=\Theta(n)$ and dense identifiers. The parameters are independent before imposing the source clauses.

| Excluded source clock | Dimension $d$ | Number of different directions |
| --- | --- | --- |
| $O(n^2)$ | $\log_2\log_2 n+O(1)$ | $\Theta(\log n)$ |
| $O(n^3)$ | $\log_2 n+\log_2\log_2 n+O(1)$ | $\Theta(n\log n)$ |

Each direction bit changes four specified ASCII low bits in the test file. The opposite polarities differ in just one ASCII low bit. The same positions work for every query at that residual. At least one polarity for each direction is SAT, since the residual is satisfiable. Both can be SAT. This is a necessary condition for the respective time lower bound. No unconditional time lower bound on these files follows. The earlier search proof used two children of one assignment prefix and several physical paddings. [One-bit hard pairs at consecutive lengths](one-bit-hard-pairs-at-consecutive-sat-lengths.md)

## A search with shared parity tables

Intern the variable names, sort signed triples and discard duplicate clauses. If $v$ distinct variables occur, $v\log(v+2)=O(n)$ since their distinct names occur in the input. The same counting argument bounds the number of distinct clauses by $O(n/\log(n+2))$. A digit trie and counting sorts on the interned identifiers take $O(n)$ word steps even for sparse original names. Keep the source clauses in terms of these variables.

Set $b=\lfloor\log_2\log_2 n\rfloor$ for the quadratic case and $b=\lfloor\log_2(n\log_2 n)\rfloor$ for the cubic case, up to harmless integer rounding for finite lengths. If $v\le b$, enumerate assignments. Otherwise maintain a set $R$ of $b$ free original variables, a set $U$ of untouched originals, and expressions for the other originals as affine forms of $R$ alone. Initially choose any $b$ originals for $R$. When $U$ is nonempty, pick $x\in U$. For every nonzero mask on $R\cup\{x\}$ try both answers to the corresponding parity equation. The file for one answer imposes the current affine expressions, the source clauses and that equation. Run each solver on it for at most $\lfloor CN\rfloor$ steps.

A timely YES commits the tested parity. A timely NO commits its opposite. When the current residual is satisfiable, either choice retains a satisfying completion. If the equation uses $x$, express $x$ as an affine form of $R$ and remove it from $U$. Otherwise solve for any reservoir coordinate with coefficient one, substitute its affine expression into all previous forms, and put $x$ in its old slot. The eliminated coordinate joins the list of expressed originals. The new $x$ has coefficient zero in every old substituted form. The representation still uses just $b$ free coordinates and the size of $U$ drops by one. A mask fits a constant number of words.

If no answer is timely, reject. Once $U$ is empty, try the $2^b$ assignments to $R$, evaluate every stored form and check the actual source clauses. The initial case $v\le b$ uses exactly the $2^v$ assignments to the original variables, including the empty assignment when $v=0$. It needs no fresh query coordinate. A negative input can never produce a checked witness. A positive input can fail only at an all-timeout residual that still contains a satisfying completion. If only finitely many input lengths had such errors, a fixed lookup table could handle them.

## Physical files and the clock

Split the $d=b+1$ free query coordinates into four fixed groups of size at most $h=\lceil d/4\rceil$. For each group make a table giving the XOR of every subset of its input bits. Force its empty entry false, use equality for singleton entries, and compute larger entries by removing one selected bit and using an XOR gate. Each table has $O(2^h)$ entries. Both equality and XOR have constant-size proper 3-CNF encodings. Unit and binary clauses can use the usual expansion over one or two distinct shared padding variables. Allocate table entries separately from every original and every intermediate gate.

Link each expressed original to the XOR of the four table entries specified by its current mask, taking account of its constant bit. Its coefficient at $x$ is zero. This costs a constant number of gates per expressed original even if its mask is dense. For the appended query use two XOR gates on the two pairs of selected entries followed by one XOR of their results. All previous clauses, including all four tables, are independent of the appended mask.

Number the entries of group $j=1,2,3,4$ by a decimal prefix $j$ followed by $h$ digits, each 0 or 1, encoding the subset with public zero padding. The number of names through the largest reserved number is $O(10^h)$. Give the remaining variables fresh IDs and, for any holes, add $(g\lor i\lor p)$ with two separate fresh names $g,p$ outside the holes. Setting $g=1$ satisfies these rows for any other assignment. Table names and gate inputs in each XOR are distinct; the input for a singleton table entry is an independently named original. The total number of serialized bits is

$$
 O\bigl((1+v+10^h+\#\text{ distinct source clauses})\log(n+2)\bigr)=O(n).
$$

Indeed $10^h=O((n\log n)^{(\log_2 10)/4})=o(n/\log n)$ in both cases. Tables and names can be enumerated directly within the same time, even if their reserving banks expand the printed lengths of the original identifiers. A changed direction bit affects exactly the four copies of its table input in the proper XOR clauses. Its decimal digit switches between ASCII 0 and 1, without changing length or another byte. To select the polarity, allocate adjacent decimal names ending in 2 and 3 for the query output and its complement, add fixed equations for these, force two distinct padding variables false, and select one name positively in the last clause with those padding variables. Any extra ID holes are covered as above. Pad by public whitespace to one sufficiently large fixed multiple of the original byte length. The selector affects one bit.

Each stage uses $O(2^b N)$ steps for construction and capped runs, including the fixed finite portfolio. Guest widths are fixed constant multiples of $\log N$ and can be simulated by choosing a sufficient fixed width or a constant number of limbs. Fresh memory between timed runs can be obtained by keeping a touched-address log and undoing the writes within the same bound. Updating all stored masks costs $O(v)$ steps. The terminal enumeration costs $O(2^b n)$, including $O(vb)$ bit operations per candidate for all the affine forms. Thus the whole search costs

$$
 O\bigl((v+1)2^b n\bigr).
$$

For $k=2$ this is $O(n^2)$, and for $k=3$ it is $O(n^3)$. An integer timeout multiplier larger than $C$ suffices for arbitrary real $C>0$. Sound replies are needed only on the generated proper files. Under a convention that rejects malformed source strings, first scan for well-formedness, checking clause counts, signs, distinct variables and the declared variable bound. Digit lengths and lexicographic comparisons suffice for large decimal header bounds. This costs $O(n)$, and malformed strings never reach a listed solver. It follows that absence of the asserted hard residuals would give the indicated deterministic SAT clock. If $S\subseteq\mathbb F_2^d$ denotes the projections of the residual's actual models, at exactly $2^{d-\dim(\operatorname{aff} S)}-1$ nonzero directions one of the slow polarities is UNSAT. These directions annihilate the span of all pairwise differences in $S$. In the extreme case with no opposite-verdict pair, the residual has at least $d+1$ affinely independent projected models.

## Limit of this clock accounting

At a sparse source with $v=\Theta(n/\log n)$, spending a full linear deadline on each of $B$ alternatives at each of $\Theta(v)$ rank steps costs $\Theta(vBn)$. A black-box promise of one timely response per menu can hide that response until the last trial. Its sign supplies at most one bit about a unique hidden assignment. This accounts for the logarithmic menu size at the quadratic deadline in this search. A larger menu would require a saving in the number of trials, the cost of trials or the amount of information needed. This accounting places no lower bound on arbitrary RAM procedures.

Lean verifies both affine eliminations as equalities of feasible relations for arbitrary source predicates, and verifies the use of a timely answer at a positive parent. The executable audit compares all 4,148 nodes in six finite search trees to their full assignment sets, checks 256 source families under four response policies, and checks the printed query suffixes at all masks and polarities through dimension nine. The asymptotic clock and the size of the complete DIMACS files have manuscript proofs above. [Lean proof](AffineReservoirUpdate.lean) · [Executable audit](affine_reservoir_audit.py)
