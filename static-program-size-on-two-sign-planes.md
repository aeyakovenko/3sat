# Five static instructions are necessary on two sign-plane input cells

Let $P,N$ be two-bit words initially in RAM cells 0 and 1. Their bits indicate which positive and negative units on variables $a,b$ to add to the fixed clause $a\lor b$. A formula from this 16-input catalog is satisfiable precisely when $(P\mathbin{\&}N)=0$ and $N\ne3$. In particular its answer depends on $N$ when $P=0$, and on $P$ when $N=1$.

**The minimum static code size is five instructions, even without a deadline.** One code achieving it is

    0   r = LOAD [1]               go to 1
    1   if r == 3 return NO        else go to 2
    2   s = LOAD [0]               go to 3
    3   s = s AND r                go to 4
    4   if s == 0 return YES       else return NO

Code size counts occupied slots in one fixed program that works on all 16 inputs. Its jumps, operands and destinations are frozen through execution. Data instructions may jump to any fixed successor for free. A comparison may jump to either of two fixed successors, including the two free terminal verdicts. Loops, destructive register writes, indirect loads and stores, including writes to the input cells, are allowed. Other cells and registers start at zero. Word literals are 0 through 3. The arithmetic and comparison basis matches the unrestricted two-bit finite audit, including variable shifts, rotations, and signed or unsigned comparisons. Each load, store, branch or ALU operation costs one dynamic step. The code above uses five steps in the worst case. [Dynamic instruction audit](split_word_sat_adaptive_audit.py)

## From three static slots to four

Remove unreachable instructions. Both terminal verdicts must be reachable. A reachable subgraph with $s$ instruction slots, $b$ conditional branches and two terminal vertices has at most $s+b$ directed edges. Each data slot has one successor and each comparison branch has at most two. Any reachable cycle therefore requires at least two branch slots: the underlying connected multigraph with $s+2$ vertices would otherwise have at most $s+1$ edges. Acyclic programs using at most four instructions take at most four steps, and the independent dynamic audit rules all of them out.

For $s\le3$, a cyclic program has at most one nonbranch slot. It needs at least one load. If that load always reads a fixed cell it cannot decide this predicate. If it is self-addressed through its destination register, then on the entire row $P=0$ it repeatedly reads cell 0 and sees zero; $N$ never influences the run. A different register used as address stays zero. This proves the three-slot lower bound without a finite clock. The argument also excludes a four-slot program containing three or more branches.

Suppose that exactly four slots are useful and two contain branches. At least one of the two data slots is a load. Rename its destination register 0. The second data slot may load, store or compute, and may overwrite the same register or write register 1. All remaining registers forever equal zero. On four bits of register state the allowed branch tests give 32 distinct Boolean tables, including constant tests and complements. The ALU instructions give 119 distinct two-bit output tables on that register state. Loads and stores still inspect or update all four actual memory cells.

Such a graph has at most six edges on six reachable vertices, so its cycle is unique, allowing loops of length one and opposite directed edges between two slots. A branch with identical targets adds no useful edge. The components off the cycle are trees.

* If both branches lie on the cycle, their off-cycle continuations must go to opposite terminal verdicts. Each downstream data instruction on such an exit can be dropped since it cannot affect the verdict. The remaining graph consists of a straight prefix and a loop with two possible terminal exits.
* If one branch lies on the cycle and one comes after it, there is a straight prefix, a loop with one exit, a straight suffix and a final branching verdict. If the second branch is before the cycle, the branch entering the cycle leads to a single possible terminal under the assumed totality of the solver. The other continuation also leads to one fixed verdict. The useful computation is then acyclic.
* A reachable cycle with no branch on it would never terminate when entered. If it is never entered by any of the sixteen inputs, its slots can be removed.

Deleting unused slots produces a smaller program, already excluded. For the remaining two shapes, list the data slots and comparison slots in schedule order, allowing all permutations and all loop-start and loop-end positions consistent with their roles. This gives 60 schedules, with harmless duplicates. The checker allows either data slot to use registers 0 or 1 as a source, including before its first write.

## Checking every loop

For each schedule and choice of data instructions, follow the path that continues the loop, temporarily ignoring the tests. This determines all register and memory contents at each potential exit. Once the same program counter, two registers and four cells recur, all later observations repeat. In the two-exit case, any choice of branch tests returns the verdict of the one whose first true observation comes earlier. If neither becomes true the run diverges. In the one-exit case the first true observation fixes the registers and memory entering the suffix, after which the final comparison fixes the verdict. Intersect the allowed predicate pairs over all 16 inputs.

Choosing the address source of the first LOAD gives six options. The second instruction has $2(6+119)+6^2=286$ options, from the six sources, 119 ALU tables, two destinations, and the address/data choices of a store. The $6\cdot286\cdot60=102{,}960$ cases each represent a family of at most $32^2$ predicate pairs. Zero cases succeed. Two additional positive controls exercise both kinds of loop exit on nonconstant target functions. Imposing an eight-step deadline gives the same result independently of stopping on repeated states. For replication, compile with a C++17 compiler, run once without arguments and again with argument 8. [Complete cyclic checker](cyclic_sign_plane_programs.cpp)

## Six is the minimum number of tests even for unbounded loops

The following six inputs already rule out every four-slot program, allowing it to run without a deadline on the tested inputs. Positions outside the suite are unconstrained.

| $P$ | $N$ | SAT |
| ---: | ---: | --- |
| 1 | 0 | yes |
| 2 | 1 | yes |
| 3 | 1 | no |
| 0 | 2 | yes |
| 2 | 2 | no |
| 0 | 3 | no |

Replacing the first row by $(3,0)$ or $(0,1)$ gives two further certificates. With bit index $P+4N$, the three masks are 5570, 5576 and 5584. The cyclic checker with arguments `all 5570`, `all 5576` or `all 5584` rejects all 102,960 cyclic configurations for the chosen suite. Its positive controls still use their full sixteen inputs. For the discarded one-load class, the two rows with $P=0$ give opposite answers while a self-addressed LOAD sees only zero. The rows $(2,1)$ and $(3,1)$ likewise exclude a program observing only $N$. Both terminal verdicts must occur on each suite, so the same control-graph argument applies even to programs that diverge on untested inputs. The acyclic programs are excluded on these same six rows by the separate four-step audit. To show six is necessary for static programs as well, test a subclass that uses at most four slots on every input. Load both words directly. The two remaining slots can either compute one ALU result and compare it with a register or literal, or compute a conjunction of two register comparisons by short-circuiting. Reversing the two terminal labels is free. The checker obtains 1,162 distinct functions from this subclass. For each function mark the set of inputs on which it agrees with SAT and every subset thereof. Every one of the 6,885 suites of size at most five is marked. This establishes the static minimum cardinality without assuming every depth-four decision tree fits four static slots. The complete list of minimum-size *static* suites is unclassified here. [Six-row dynamic certificates](exact-clocks-for-two-word-sat-inputs.md)

This establishes a minimum for this four-bit catalog, its memory layout and its instruction basis. A longer program may reuse the same loop on larger inputs. The finite lower bound supplies no code-size or time growth law across input lengths and gives no unrestricted SAT time separation.
