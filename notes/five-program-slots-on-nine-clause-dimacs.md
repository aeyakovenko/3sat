# Five stored instructions are necessary and sufficient on five 95-byte SAT files

There is an explicit five-file promise of ordinary proper DIMACS 3-CNFs on which the least possible number of stored instructions in the separate-operation RAM is **exactly five**, allowing unlimited time, arbitrary immediate integers and all writable addresses. Every file has three variables, nine clauses and 95 bytes. The word width at this length is 16 bits. The proof against four slots permits arbitrary at-most-binary numerical register instructions and arbitrary two-operand branch comparisons, with separate LOAD and STORE. The input grammar permits repeated clauses and the final zero at EOF. A final newline throughout gives the same word addresses and proof at 96 bytes. [Machine model](five-instruction-loops-on-dimacs-sat.md)

## The five examples

Write $X=(1,2,3)$, $U=(-1,2,3)$ and $V=(1,-2,3)$ for signed clauses. Take one occurrence of every sign pattern on 1,2,3 other than $X$, with an extra copy of $U$ and one of $V$. Mark the negative sign on both $U$ rows and on one $V$ row. Replacing a marked minus by a space makes that clause $X$. On the center $X$ is missing, so the all-false assignment is a model. Any single edit supplies $X$ while an unchanged duplicate retains its old sign pattern. All eight patterns are then present, making the formula unsatisfiable. Editing both $U$ copies makes $U$ absent, restoring satisfiability. Test exactly the center, its three single edits and that double edit.

The physical center has this text with EOF immediately after the final zero.

```text
p cnf 3 9
1 2 -3 0
1 -2 -3 0
-1 2 -3 0
-1 -2 3 0
-1 2 3 0
1 -2 3 0
-1 2 3 0
-1 -2 -3 0
-2 1 3 0
```

The two $U$ marks are at zero-based word addresses 24 and 33, and the $V$ mark is at 43. Each of the three words contains a newline in its low byte and a minus in its high byte, changing from `0x2d0a` to `0x200a`. All original physical words on the center have numerical value greater than 43, including the final partially filled word of value 48. The three marked addresses are also different from the initial register values $0,n=760,w=16$.

The five-instruction program loads cells 24 and 33 into different registers and branches to NO if unequal. On equality it loads 43 and branches to YES exactly when the reply equals `0x2d0a`. It uses three direct LOADs and two binary branches. It gives the correct five answers in at most five executed instructions.

## Exhausting four slots at this single length

Any program correct on the suite must read all three marked *original* words on its center run. If it never reads one, its corresponding single edit follows the same execution. If the program overwrites the mark before reading it, that edit also becomes indistinguishable. The four examples leaving the third mark unchanged give exactly equality of the first two choices.

First consider an acyclic reachable control graph. A correct machine needs both verdicts and at least one branch. The center requires three LOADs, so in four slots there are precisely three LOADs and one branch, each used at most once on the center. The branch must receive the influence of all three marks. Once it has executed, the remaining fixed-successor instructions cannot change the chosen verdict. Consequently all three LOADs precede the branch on the center path. Each read uses a distinct marked address. It cannot obtain that address from any previous read or initial register, so it uses a direct immediate. These three LOADs take the same addresses on every file. The final comparison can depend on at most two of their replies. Flipping the third influential mark alone contradicts correctness.

If the reachable directed control graph contains a cycle, it requires at least two binary branch instructions. Indeed the connected underlying multigraph on $s$ reachable instructions and two reachable terminals has at most $s+b$ edges for $b$ binary branches. A cycle needs at least $s+2$ edges. At most two data operations therefore remain.

* With no LOAD the files are indistinguishable. With at least one LOAD and no numerical site, the only sources of register values are their initial values and memory replies. Neither the original memory nor the initial registers contain any of the three relevant address values. Each accessible private address must therefore be a direct LOAD immediate or a literal previously used as a STORE payload, possibly copied through later operations. An immediate STORE *address* does not place that value in a register or into memory. Thus the number of different private addresses that can be loaded is at most the number of LOAD and STORE sites, at most two. This contradicts the three required reads, regardless of loops.
* The only other allocation is one LOAD and one numerical site with no STORE. A fixed LOAD address misses marks. When the LOAD's mutable address and destination are distinct, the numerical site must write the address register. Only those two registers can vary. On the equality subsuite, a private probe fixes its address register and the LOAD overwrites its other register with the reply, with a fixed successor PC. Contract all steps until the next private probe, terminal or divergence. There is one query vertex per private sign. No such deterministic cyclic graph computes two-bit equality: from the first sign both answers must reach the second, forgetting the first, and a return to the first vertex then repeats on that input. The same contraction applies if only the self-addressed LOAD register varies. For a self-addressed LOAD with a distinct numerical destination, the address register is changed only by LOADs. Its first address is an initial value and every subsequent one is a raw reply, so it cannot reach the three required addresses. [Lean theorem for the contracted equality graph](../lean/TwoPrivateProbeSites.lean)

This exhausts every operand alias and control allocation of four or fewer sites. Every candidate faces these *same five files*, also when its immediates are specified as arbitrary residues at the test width. The five-slot concrete program solves this promise; the separate manuscript excludes a globally correct five-slot solver on ordinary DIMACS. [Global theorem and its verification scope](five-instructions-cannot-decide-dimacs-sat.md)

## Why nine clauses are necessary for this witness property

A proper three-variable clause over any set of Boolean variables excludes exactly one eighth of all assignments. A proper formula with fewer than eight clauses is satisfiable. If changing a single clause in an eight-clause file makes it unsatisfiable, the eight sets of excluded assignments **after** the edit have total measure one and cover everything. They must be pairwise disjoint. In particular the seven unchanged exclusion sets from the original are pairwise disjoint. If individually fatal edits are possible in three distinct clauses of a satisfiable center, any pair of original clauses is untouched by one of the three edits. All original exclusion sets would then be pairwise disjoint. Their measures already sum to one, contradicting satisfiability of the center. The argument also works if an edit changes which variable names occur, by counting assignments on the union of names. Nine is thus the minimum clause count for a satisfiable proper center with these three distinct fatal single-clause edits. The minimum byte length or number of examples for *every* possible four-slot obstruction is unestablished.

The [Lean checks](../lean/NineClauseSlotWitness.lean) verify the concrete bytes and changing word positions, truth labels, the final two-operand comparison obstruction, and the five-instruction decision expression. The [executable audit](../audits/four_slot_nine_clause_audit.py) independently parses and evaluates the serialized files and counts the instructions taken. The control and operand classification above is a manuscript argument. The lower bound is on stored code for a finite promise; a normal SAT solver can recognize these cases cheaply.
