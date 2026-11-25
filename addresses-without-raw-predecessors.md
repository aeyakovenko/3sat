# A deadline above two executed instructions per DIMACS input word

Fix the [separate-operation RAM](five-instruction-loops-on-dimacs-sat.md) with little-endian words, a fixed finite instruction set, explicit operands and unrestricted writable memory. Write $n$ for the encoded bit length, $w=16\lceil D_0\log_2(n+2)/16\rceil$ for the word width with fixed $D_0\ge1$, and $L=\lceil n/w\rceil$. There is an instruction-set constant $\delta>0$ and, at each sufficiently large byte-aligned length, a proper ASCII 3-CNF formula with the following property. Every correct SAT program with at most $C$ stored instructions executes at least
$$
 (2+\delta)(L-O(1))-O(C+1)
$$
steps on this same formula. A common finite suite consisting of the formula and one edit per marked word also tests programs whose correctness is unknown. At deadline $(2+\delta/2)L$, adding a constant number of marked words compensates for one extra stored instruction, even if all instructions are rewritten.

## Which addresses a raw input word can produce

Use the [aligned repeated-word layout](executed-operands-on-homogeneous-sat-words.md), exchanging variables 2 and 3 in the repeated clauses. Seven public proper clauses force variables 1, 2 and 3 to be false. The byte sequence of each marked word now begins with ASCII `2 1 3 0` followed by a newline and ends with a minus sign. Fill the intervening bytes with spaces. A preceding minus sign begins the first marked clause, and a fixed suffix completes the last clause. Each marked minus begins a literal $-2$ in the following clause. Changing any one of them to a space makes that clause false on the forced assignment. The base is satisfiable and each edited file is unsatisfiable. There are $m=\lfloor n/w\rfloor-C_{D_0}$ marked words, so only $O(1)$ physical words are unmarked. The number of distinct initial memory word values, including the default zero, is bounded by a constant $h$.

Put $Q=2^w$ and $I=\{0,\ldots,L-1\}$. The common marked value $A$ has low byte 50 and high byte 45. In particular $A\bmod4=2$ and $Q/8<A<Q/4$. We call a marked address $p$ protected if no allowed numerical operation on $A$ and a partner $y\in I$ gives $p$ as a **new** value, in either operand order. Giving back $y=p$ cannot be a first production. Unary operations on $A$ have a bounded number of possible outputs, which we discard.

For large $n$ there are at least $m/16$ protected addresses. Start with the $L/8-O(1)$ marked integers $L/2\le p<L$ with $p\bmod4=3$. The two inputs to an operation can occur in either order.

* Addition and either subtraction land outside $I$, since $L=o(Q)$ and $Q/8<A<Q/4$. Multiplication by $A$ modulo $Q$ gives an even value. Comparisons give zero or one. Moves can only copy an available operand.
* For a bitwise binary truth table giving a result in $I$, the output must be zero on both bit pairs $(0,0)$ and $(1,0)$ in the orientation $(A,y)$. Both occur in the top byte, where $y$ has only zero bits and $A$ contains both bit values. The four remaining tables give zero, $y$, $y\mathbin{\&}A$ or $y\mathbin{\&}\mathord{\sim}A$. The last two each lack one of the two required low bits.
* Shifts or rotations of $A$ as data have $O(w)$ possible results. Shifting $y$ left by $A$ produces an even result or copies $y$. A nontrivial right shift of $y$ produces less than $L/2$. This includes logical and arithmetic right shifts because both inputs have their sign bit clear. Saturated and reduced-modulo-width shift counts are covered.
* Rotating $y$ by $A$ leaves at most $2\cdot2^{b-k}$ exceptional targets when the middle case below is nonempty. Here $b=\lceil\log_2 L\rceil$ and $k=w-b$. The distance $A\bmod w$ is fixed for this input length. If its shortest distance to zero on the cycle is $t\le k$, one of the two directions multiplies $y$ by $2^t$ without wrap. For $t>0$ that result is even. The opposite direction either wraps a one into the top $k$ bits or gives less than $L/2$. Distance zero just copies $y$. If the shortest distance exceeds $k$, the rotated block of $k$ top zero bits is disjoint from its old position, in either direction. A candidate $p<2^b$ must have another prescribed block of $k$ zero bits among its low $b$ bits. This leaves at most $2^{b-k}$ possible targets per direction.

Since $2^b<2L$, $Q\ge n$ and $L=\lceil n/w\rceil$, we have $k\to\infty$. The rotation exceptions occupy $o(L)$ positions. Also $w=O(\log n)=o(L)$. Subtracting these losses from $L/8-O(1)$ proves the claimed $m/16$ bound at all sufficiently large lengths. The [word-operation audit](ram_raw_predecessor_audit.py) enumerates both operand orders and all sixteen bitwise tables for finite examples, including literal byte layouts from this construction.

## Counting first productions on a single execution

Let $s=h+r+2C$, where $r$ bounds the initial register palette outside memory, and each stored instruction has at most two data literals. Count a number as initially available even if it occurs only in untouched input or untaken code. Apart from this stock, a numerical instruction must first produce each new numerical value. Loads and stores can only copy values. Take a program correct on the suite and follow its base run.

1. Choose one original-word LOAD for each marked address whose register definition has at least one later explicit operand use. Such a load is necessary, since changing just this word can alter the verdict only if a value read from it is used before being overwritten. An overwritten original can no longer report the change. The resulting $m$ selected instructions are distinct. None consumes a selected definition since its loading address is in $I$ and the value of each selected definition is $A\notin I$.
2. For every marked address absent from stock, designate the first numerical instruction producing it. Let $G$ be their number, so $G\le m\le G+s$. These instructions have distinct outputs. Let $R=T-m-G$ count all other executed instructions on the base. Among the $G$ designated producers, let $z$ have zero operands supplied by selected definitions. At most $J$ can have two such operands, where $J$ is the number of binary numerical opcodes. Their outputs would all have the form $f(A,A)$, and each output is designated at most once. Every selected definition needs at least one use. Hence
   $$
   m+z\le 2R+G+J.
   $$
3. Write $d$ for the number of protected addresses. Each is in stock or has a designated producer. If that producer consumes a selected definition, then it has input $A$. An in-range second operand cannot give a first production, by protection. Outside $I$ at most $s+R$ distinct values ever become available. The $G$ producers output only addresses in $I$, and selected loads supply the original value $A$ already in stock. Let $H$ bound the number of oriented numerical opcodes, counting either position for one selected operand and the unary forms. A dummy partner covers unary instructions. It follows that
   $$
   d\le s+z+H(s+R+1).
   $$

Eliminating $G,z,R$ gives
$$
  2(H+2)m+d\ \le\ (H+2)T+2(H+1)s+J+H.
$$
Taking $d\ge m/16$ gives the claimed $\delta=1/[16(H+2)]$. The gain is uniform over code sizes. The additive cost accounts for literals supplied by the program.

## An explicit successor for the clock

Set $D=16(H+2)$, $E(s)=16[2(H+1)s+J+H]$ and fix a constant $b_0$ with $L\le m+b_0$. The last bound gives $(2D+1)m\le DT+E(s)$. In particular, at every sufficiently large layout with
$$
 m>(4D+1)b_0+2E(s)
$$
the base run exceeds $(2+1/(2D))L$. A program failing the suite's correctness condition already has a counterexample. One more code slot raises $s$ by at most two. Increasing $m$ by $128(H+1)$ keeps the last inequality strict for **all** programs of size at most $C+1$. All sufficiently large integer values of $m$ occur for this width rule, as shown in the [original address-counting proof](address-production-and-a-program-size-lift.md). The [Lean file](NoRawPredecessor.lean) checks elimination of the counts and the exact successor arithmetic. The trace and opcode arguments above are manuscript proofs.

The entire suite is still recognizable in $O(L+\operatorname{polylog}n)$ executed steps by a fixed program. It reconstructs the header and the two possible words, checks their layout, and uses complete SAT search on other inputs. Its linear scan on the suite also explains why an induction at a fixed per-word deadline cannot yield superlinear time in the encoded bit length. Priority for the constant-factor statement is unestablished.
