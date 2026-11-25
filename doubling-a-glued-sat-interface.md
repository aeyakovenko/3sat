# Doubling the information across a 3-SAT interface

Fix $k$ Boolean variables shared by two parts of a formula. Every pair of truth tables $S,T\subseteq\{0,1\}^k$ can be encoded in a **proper ASCII DIMACS 3-CNF of $\Theta(2^k)$ bits**, such that a boundary assignment extends to a satisfying assignment exactly when it belongs to both tables. Each individual table bit occupies the low bit of one fixed ASCII digit. The two parts share precisely the $k$ specified variables, and every integer variable identifier from 1 through the declared maximum occurs in the combined file.

Increasing $k$ by one doubles the minimum number of bits required to summarize one part for all possible other parts. A RAM that sees both parts can test the two tables a packed word at a time. These two costs can be computed on the same explicit inputs.

## Encoding one side

Let $m=2^k$. For all sufficiently large $k$, choose $b=2^{\lfloor\log_2(k/8)\rfloor}$, so $k/16<b\le k/8$. Use $\ell=\log_2 b$ low boundary bits to select one of $b$ positions in a block. The remaining $k-\ell$ bits select a block $i$ among $m/b$ blocks. Write $s_i\in\{0,1\}^b$ for the block of table bits at those positions.

For each part build two binary prefix trees of indicator variables, one on the low bits and one on the high bits. The root is forced true. For a child $v$ of parent $u$ with the next boundary literal $L$, impose $v\leftrightarrow (u\land L)$. The leaves $J_j$ of the low tree and $H_i$ of the high tree indicate the selected position $j$ and block $i$. Introduce a flag $F_s$ for each of the $2^b$ possible strings $s$ of length $b$. For every $s,j$ require that $J_j$ implies $F_s$ if $s_j=1$ and implies $\neg F_s$ if $s_j=0$. Given a boundary assignment these fixed clauses force $F_s=s_j$ for all $s$.

Let $f$ be a private variable forced false. The only clause that depends on block $i$ of the input table is
$$
                 (\neg H_i\lor F_{s_i}\lor f).
$$
At the selected high leaf this requires $s_{i,j}=1$. All other such clauses hold by their first literal. The prefix variables and flags have a satisfying extension whenever that table entry is one. Thus the existential relation of this part on the shared variables is exactly $S$.

Every clause has three distinct variables. In a prefix gate, pad the binary clauses $(\neg v\lor u)$ and $(\neg v\lor L)$ with $f$, and use $(v\lor\neg u\lor\neg L)$ for the remaining implication. Pad the binary flag clauses with the same $f$. Forcing a literal to hold is implemented by conjoining its four proper three-clauses with the four sign choices on two private guard variables. With the forced literal true, these guards remain free.

## A fixed layout in ordinary decimal DIMACS

On the left name $F_s$ with the decimal digit 1 followed by the $b$ bits of $s$ written as ASCII digits. On the right use the digit 2. The order within a name is fixed, most significant first in the audit. All names are less than $3\cdot 10^b$. Number the ports and the remaining private variables consecutively above this range. The two sides use disjoint private names. For each unused reserved identifier $v$, insert a harmless clause $(g\lor X_v\lor z)$ on the left, using two different left-side guards. Taking $g$ true satisfies every such clause without changing the relation. Every reserved identifier is now used, either as a flag on its own side or as a filler on the left. For a standalone dense encoding of one relation, use one bank of flags and fill the unused identifiers of its own reserved range in the same way.

The number of clauses and identifiers is
$$
              O\bigl(m/b+b+b2^b+10^b+k\bigr)=O(m/k).
$$
Indeed the two prefix trees have $O(m/b+b)$ vertices, every flag requires $b$ clauses, and $10^b\le 2^{(\log_2 10) k/8}$. The largest identifier has $O(k)$ digits. Right-align the signed literals in fixed-width decimal fields, with whitespace between tokens. Each clause occupies $O(k)$ bytes. The header, the clauses at every position, and the full length are determined by $k$ except for the $2m$ binary digits embedded in the names in the block clauses. An ASCII 0 and 1 differ in exactly their low bit. Thus each truth bit independently changes just one bit of the physical file. There are at least $2m$ such columns, so the total length is $\Theta(m)$ in bits. For the finitely many small arities any explicit truth-table encoding and a fixed increase of the constant suffice. The audit uses $b=2$ at $k=2,3,4$ to exercise both prefix trees on small examples.

The classical synthesis bound already gives $O(2^k/k)$ Boolean gates for an arbitrary function of $k$ inputs. Here a common layout additionally makes each truth-table entry a projection to a single bit in a dense decimal 3-CNF. Priority for this encoding refinement is unestablished. [Frandsen and Miltersen](https://tidsskrift.dk/brics/article/view/21875)

## The exact successor

Define $D_k(S,T)=1$ if the glued formula is unsatisfiable, equivalently if $S\cap T=\varnothing$. Give each table on $k+1$ variables the two restrictions $S_0,S_1$ for its new boundary bit. A common assignment exists if it exists on either bit value. Consequently
$$
      D_{k+1}((S_0,S_1),(T_0,T_1))
                  =D_k(S_0,T_0)D_k(S_1,T_1).
$$
As a matrix on all possible tables per side, $D_{k+1}=D_k\otimes D_k$ in the corresponding order. At $k=0$ the universe has one element and the matrix is $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$. Its determinant is $-1$. Since tensor products of invertible matrices are invertible, $D_k$ has rank $2^{2^k}$ over every field.

Suppose a summary of the left part permits the exact verdict for every right part. If $S\ne S'$, a singleton in their symmetric difference distinguishes them. There must be at least $2^m$ different summaries, and $m$ bits suffice by sending the table. The worst-case one-way communication is exactly $m$ bits when only the receiving party needs to answer.

For an interactive deterministic binary protocol in which both parties learn the verdict, each terminal transcript gives a monochromatic rectangle. All $2^m$ pairs $(S,\overline S)$ have $D_k=1$. If two different such pairs shared a rectangle, both crossed pairs would be disjoint, forcing both $S\subseteq S'$ and $S'\subseteq S$. The protocol needs at least $2^m$ distinct leaves for verdict one, plus a leaf for verdict zero. A binary tree of depth $m$ has at most $2^m$ leaves. Sending $S$ and returning one verdict bit attains the resulting lower bound of $m+1$. Hence the exact one-way summary size doubles at every successor for unrestricted ways of processing either side locally.

## The same files on a RAM

Under the promise, a RAM visits the two dynamic clause fields with the same $i$ and tests the $b$ designated ASCII digits for a common one. In each field the relevant $8b$ consecutive bits fit in $O(1)$ words of logarithmic width, including at unaligned offsets. After aligning the spans, AND both with the mask that selects the low bit of every byte. Any nonzero result certifies satisfiability. There are $m/b=\Theta(m/k)$ such tests. The row pitch, starting byte offsets and mask are public functions computable in $\operatorname{poly}(k)$ steps by the displayed tree, flag and filler counts. If a uniform rule recovering $k$ from file length is desired, pad the overall byte length to $A2^k$ with trailing whitespace for one sufficiently large fixed integer $A$. This preserves the projections and makes the promised scan take $O(n/\log n)$ steps for $n$ encoded bits.

This bound matches the order obtainable by a word-level communication simulation. Each party knows one table and every fixed bit of the format. They can maintain the same registers and mirror writable memory. At each read of a still-original input word the parties exchange at most $O(w)$ bits, even if variable columns from both sides occur in the word. Every executed instruction is then simulable with at most $O(w)$ communicated bits. The $m+1$ lower bound gives $\Omega(n/\log n)$ RAM steps on this family.

A single globally correct solver can also verify the format in $O(n)$ RAM steps on the family, then use the promised scan. Regenerate the public template, comparing all fixed bytes and requiring 0 or 1 in each designated digit column. The two full prefix trees can be enumerated in level order with simple running node numbers. The $O(m/k)$ rows cost $O(k)$ steps each to print and check their fields. In the smaller flag and filler portions, even $\operatorname{poly}(k)$ work per row or reserved identifier is $o(m)$ in total. Decimal output of an $O(k)$-bit name needs $O(k)$ fixed-word operations via repeated division by ten. On the separate-operation ISA the high half of a word product is computable by a constant number of half-word products and carries. With $Q=2^w$, the high half of $x\lfloor Q/10\rfloor$ underestimates $\lfloor x/10\rfloor$ by at most one. Checking the remainder gives division by ten with constant cost after $\operatorname{poly}(w)$ setup. On a mismatch invoke any complete SAT algorithm. Thus the summary induction coexists with a globally correct program having linear bit-length time on the entire exhibited family. An unrestricted lower bound would have to charge for work beyond comparing the two tables where the input already places them.

The [Lean file](GluedBoundaryTables.lean) proves disjointness under the successor, the crossed-complement argument and injectivity of exact summaries. The [PicoSAT audit](glued_boundary_tables_audit.py) checks the actual dense files, uniqueness of the changing digit columns, and the SAT answer with every boundary assignment pinned. It reproduced 310 proper files, 1,672 pinned decisions and 56 distinct projection columns. The asymptotic size and RAM analysis above are manuscript arguments.
