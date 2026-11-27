# An executed-instruction lower bound on ordinary DIMACS words

On the separate-operation logarithmic-word RAM, for every sufficiently large byte-aligned length $n$ there is a satisfiable ordinary DIMACS file on which **every correct SAT program** executes at least

$$
\frac53\left\lceil \frac{n}{w}\right\rceil-O(1)
$$

instructions. Here $w$ is the number of bits per word. The program can have arbitrary length, immediate literals, registers, branches and writable workspace. The coefficient measures steps per physical input word. This bound is below linear time in the number of encoded bits. The same construction tests a conjunction of input edits, so the bound does not pass the project's SAT-specificity test. [Machine model](five-instruction-loops-on-dimacs-sat.md) · [Research criteria](../research-steering.md)

A LOAD reads at most one memory cell, using either an immediate or one register for its address. A STORE takes an address and a payload. A numerical instruction produces one register value from at most two explicit operands in the fixed instruction set. A branch compares at most two register or immediate operands using the usual signed or unsigned order or equality, with fixed targets. In particular, every two-register branch on $(A,A)$ has the same outcome on $(B,B)$. Operations have no hidden register updates, comparison flags, or indirect control transfers. Terminals give fixed verdicts. These requirements matter for the coefficient.

## Counting an actual accepting run

Consider a base input with $m$ marked word addresses. Each initially contains the same word $A$. Replacing the original word at any nonempty subset by a second common word $B$ changes the correct verdict. Assume $A$ is outside the set of marked addresses. Let $J$ be the number of binary numerical opcodes. Apart from word width and fixed machine conventions, a two-register operation with both inputs $A$ can produce at most $J$ different base values $f(A,A)$.

Fix the base run of a correct program, of length $T$. For each marked address choose an original-word LOAD whose resulting register definition is used as an explicit operand before being overwritten. Such a LOAD exists. Until an edit to that address makes a differing register value an operand, the base and edited traces take the same control path, request the same addresses and write the same values. The only differing memory can be the still unoverwritten original word. Distinct addresses select distinct LOADs. Calling a read *original* means that no prior STORE has overwritten that address, even if it wrote the same value.

Count uses of the $m$ selected definitions on the base. A use is one operand position referring to a live definition; two references by the same instruction count twice. No selected LOAD consumes a selected definition since its address would be $A$. Let $D$ be the total use count, and put

$$
 a=D-m,\quad b=2(T-m)-D,\quad e=a+b=2T-3m.
$$

Here $b$ counts free operand positions after booking two positions per nonselected instruction and placing all the selected uses. A LOAD has at most one actual operand, so its second position is always free. Let $r$ count other original reads at the marked addresses. A marked cell is *clean* when its original word is read just once and the resulting selected definition is used just once. At most $d\le a+r$ cells fail to be clean. Together these $d$ cells have at most $d+a$ selected uses.

At most $b$ clean cells can be consumed at instructions with fewer than two selected uses. At most $d+a$ further clean cells are combined with a nonclean selected use. All remaining clean cells arrive in pairs at one instruction. In such a pair the two operands arise from distinct marked addresses. Until that instruction any edit to the chosen cells only changes their original memory and the two registers carrying their words. After their one consumption, no later original read of either cell, or other use of those two definitions, can report the change. This gives three cases.

* If the instruction is a branch, flip both words. Its comparison still has equal operands and the same outcome. All subsequent observations agree. This contradicts correctness.
* If it is a STORE, the base writes $M[A]\gets A$. Flip only the cell supplying the payload. The destination stays $A$. There must be a later LOAD at $A$ before the next STORE there, since otherwise this altered write can never affect the verdict. This is a nonselected LOAD. Different such stores charge different LOADs, each to its always-free second operand position.
* If it is a numerical operation, its result must have a later operand use. Otherwise flipping a cell in this pair cannot affect the verdict. Charge one such use. At a nonselected instruction it occupies an actual operand position free of selected uses. At a selected LOAD it gives a marked address of the form $f(A,A)$. The latter can happen for at most $J$ pairs because the selected LOADs have distinct addresses.

Write $s$ for the number of paired STOREs and $j$ for paired numerical operations charged to nonselected instructions. Then $r+s+j\le b$. The $r$ extra original LOADs use dummy second positions at marked addresses. The $s$ store observers use dummy second positions at $A$, which is unmarked. The $j$ later uses charge actual operand positions with unique defining instructions. These charges are disjoint even if an observing LOAD uses a numerical result as its address. Counting all marked cells gives

$$
m\le d+(d+a)+b+2(s+j+J)\le3a+2r+b+2(s+j)+2J\le3e+2J.
$$

Consequently $T\ge (5m-J)/3$. The execution may use a different branch on each changed input. Only the indicated single edits and double edits in the comparison case are needed. [Lean bookkeeping](../lean/ExecutedOperandBound.lean)

## Ordinary files with an edit in essentially every word

Use seven proper clauses on variables 1, 2 and 3 forbidding all assignments except $(0,0,0)$. Let $W=w/8$ be the number of bytes per word. After the header and those clauses, pad with spaces and place a minus sign immediately before a word boundary. Repeat a full word consisting, in increasing address order, of the eight bytes `3 1 2 0\n` (with a real newline), enough spaces to fill the word up to its last byte, and a final minus. Append `3 1 2 0\n` once more. With $M$ repeated words the clause count in the header is $M+8$. Each minus starts the next occurrence of the literal $-3$. Replacing it by a space creates $(3\lor1\lor2)$, which is false under the forced assignment. Arbitrary subsets of edits are well formed.

For the width rule $w=16\lceil D\log_2(n+2)/16\rceil$ with fixed $D\ge1$, choose $M=\lfloor n/w\rfloor-C_D$ for a sufficiently large fixed integer $C_D$. The header's digit count is $O(\log n)$ bytes, and the other overhead plus alignment uses $O_D(1)$ words. Pad any remaining bytes with whitespace. The original repeated word $A$ has high byte 45 and hence exceeds every physical input address for large $n$. Thus $m=M$ satisfies the counting argument. This works at every sufficiently large byte-aligned length.

## An upper bound on the simultaneous-edit promise

The coefficient $5/3$ is attainable for these actual DIMACS words at infinitely many widths when the program can be specialized to the finite test. At $W=60+510t$ bytes the high bytes of $A^2,AB,B^2$ modulo $256^W$ are respectively $38,143,248$. The high bytes of $A,B$ are $45,32$. Therefore for $x,y,z\in\{A,B\}$,

$$
 (xy\bmod 256^W)<z\quad\Longleftrightarrow\quad x=y=z=A.
$$

Three immediate-address LOADs, a modular multiply, and an unsigned comparison branch check a triple in five executed steps. Unroll over triples and check the final at most two words separately. The resulting program decides the entire promised family, including combinations of edits, in $5m/3+O(1)$ steps. Its code may grow with the suite. An unrestricted total decider must additionally handle arbitrary files outside this promise.

For the high-byte identity, let $p$ be the little-endian integer of the eight-byte prefix of the repeated word, $U=255p-32\cdot256^8$, $V_A=255\cdot45+32$, $V_B=255\cdot32+32$. Then $255A=U+V_A256^{W-1}$ and similarly for $B$. In a product the high byte modulo $256^W$ is that of $U^2/255^2$ plus $U(V_x+V_y)/255^2$ modulo 256, interpreting the odd denominators by modular inversion. For $U^2<256^{W-1}$, choose $0\le t_W<255^2$ so $U^2+t_W256^W$ is divisible by $255^2$. The high byte of the first term is $\lfloor256t_W/255^2\rfloor$. It only depends on $256^W$ modulo $255^2$. Since $256=1+255$, a shift of 510 byte positions leaves this residue fixed. Direct integer arithmetic at $W=60$ supplies the three starting high bytes. Such even byte widths occur for infinitely many encoded lengths in the stated width rule. [Integer and SAT audit](../audits/homogeneous_ram_word_clock_audit.py)

The point at which this lift stops is quantitative. This family uses the same Boolean conjunction at every length, and the five-instruction test for three independent edits survives as further triples are added. It gives a uniform lower bound on the number of **executed** instructions of every correct program. Raising a constant number of instructions per word to an unbounded number per encoded bit requires a different family or a new constraint on those executions.
