# Eliminating two-load, one-ALU programs with five static slots

Use the dense 16-bit sign-plane catalog and its four four-bit input words P₀,P₁,M₀,M₁ at addresses 0,1,2,3. A static instruction has fixed operands, destination register and control targets even when it executes many times. The deadline is 16 instructions. In the binary-branch model, a looping five-slot program deciding a nonconstant language needs at least two static comparison branches. This leaves three data slots. Here take two LOADs and one ALU, with no STORE. The analysis allows arbitrary control flow and arbitrary register aliasing unless explicitly restricted. [Machine model and branch count](exact-clocks-for-two-word-sat-inputs.md).

**Finite lower bound.** No five-slot program consisting of two LOADs, one ALU instruction, and two binary comparison branches decides this sign-plane family within 16 steps. This includes loops, indirect reads, arbitrary register aliasing and arbitrary ALU feedback. Two preliminary tests eliminate the cases where the ALU cannot read its own result or its destination is private to that site. A control-graph census covers the remaining cases.

## Necessary addressing on sensitive inputs

Choose P₀=P₁=p and M₀=M₁=m with p and m nonzero four-bit words satisfying p AND m=0. There are 50 choices. Each input is SAT. Changing any one positive word to 15 or any one negative word to 15 introduces a conflict, giving UNSAT. Thus the execution on this particular positive input must read all four original cells before its final decision. After the last branch we may ignore instructions that do not affect the verdict.

If the single ALU site executes t≥1 times on that prefix, each pair of successive visits has an intervening branch. A repetition without such a branch would already be an unconditional cycle. The prefix also has a final branch after its last useful data instruction, so there are at least t branch executions, in addition to t ALU executions and at least four loads. Hence t≤6.

Two direct LOADs can access only two cells. If there is an indirect site, allow at most one direct input address d, using d=−1 to include all cases without such an address. Put V={0,p,m}. Other than the ALU destination register R, every register's value is in V. To include aliasing, initialize H₀=V as an overestimate of R's values. For j=1,…,6 enlarge Hⱼ₋₁ by all outputs of the ALU with a SELF source ranging over Hⱼ₋₁, an OTHER-register source ranging over V, and any immediate fixed to its actual value. Use the original Hⱼ₋₁ for both operands. The resulting H₆ contains every possible register address on the prefix. Necessarily

$$
\{0,1,2,3\}\subseteq H_6\cup\{d\}.
$$

The same instruction and d must satisfy the condition on all 50 positive inputs. The audit enumerates all 18 operand kinds (SELF, OTHER, and the 16 literals) in both positions for every operation, including both operand orders. It includes full modular add, subtract and multiply, bitwise operations, logical and arithmetic shifts with both count conventions, both rotations, and data comparisons and complements. Every survivor uses SELF in one operand and a fixed literal in the other. Deduplicating the resulting 16-entry unary maps gives 13 (map,d) pairs, comprising nine maps. This proves the first exclusion. The overestimate permits inconsistent values when two source operands alias, which can only leave extra candidates alive. [Executable finite audit](../audits/two_load_five_slot_audit.py).

## When R is not overwritten by a LOAD

Fix any surviving unary update f. If the LOADs never write R, the possible R values before the decision on each sensitive input lie in Q={0,f(0),…,f⁶(0)}. Each of the two branch sites includes at most one relevant literal (a comparison of two literals is constant). Allow an arbitrary unordered pair of these literals, duplicating one if necessary.

The audit finds two inputs (p,p,m,m) and (p′,p′,m′,m′) for every map and every literal pair. The first is one of the sensitive SAT inputs and p′ AND m′≠0 makes the other UNSAT. The pairs have the following properties.

- The map carrying p to p′ and m to m′, while fixing Q, zero, and the branch literals, preserves all equalities and both signed and unsigned order on these words.
- The address categories of p and p′ match, and so do the categories of m and m′. These categories are {0,1} (positive cells), {2,3} (negative cells), and {4,…,15} (zero scratch).

Induct along the positive execution. Direct LOADs give corresponding values, as do indirect LOADs through corresponding registers by the address categories. A LOAD using R sees the same address in the two runs. Executing the ALU moves the two identical R values to the same next orbit entry. Every branch comparison has the same outcome. Thus the two inputs reach the same verdict, a contradiction. The audit checks all 9·136=1,224 map/literal-pair cases. It does not assume the negative execution is short in order to couple it; it follows the positive execution instruction by instruction.

## When a LOAD can overwrite R

Name the ALU register R and name the other LOAD destination S if there is one. Every other register is constant zero. Each LOAD chooses its destination from R,S and its address from the four literal input addresses, one representative literal scratch address, R, or S. At least one LOAD writes R and at least one uses a register address. Order the two LOAD descriptions lexicographically; their slot names are interchangeable. For each of the remaining unary ALU maps, enumerate the resulting pairs of LOAD descriptions allowed by the preceding address test.

On a positive base input consider the data instructions of a run through the last comparison and write nᵢ for the execution count of its ith data site. The same repeated-site argument as above gives the necessary bound Σᵢnᵢ+maxᵢnᵢ≤16. With the branch choices entirely free, try every data sequence satisfying this bound, keeping its two registers and the set of original input addresses read. A data step that changes neither the registers nor the read set may be omitted in this relaxed test. For each positive base input the data sites must admit some sequence reading all four cells. Precisely 31 data palettes pass for all 50 inputs.

For each such palette the C++ census enumerates static control graphs. The three data sites have one successor each, and the two conditional sites have two. The comparison predicates include both orientations so the successor pairs can be sorted. The YES and NO terminals are different. A data site whose successor is a fixed terminal cannot affect the verdict and may be bypassed by redirecting its incoming control edges to that terminal, applying the same argument to a chain. Unused sites are permitted. Each remaining data-site successor may be any of the five instruction sites, which even permits nonstandard data-site fallthroughs. A conditional with equal successors is a fixed jump and cannot be one of the two effective conditional sites needed for a nonconstant looping program. Name the first conditional reached from entry site 3. Keep graphs that can reach both terminals and have a path to YES within 16 steps with at least four loads.

There are 1,584 such graphs before considering their data operations. On each positive base input some path to YES must actually visit all four addresses. Testing this with unrestricted branch outcomes leaves 579 graph/palette pairs. Each branch compares two registers/literals, and the ordered finite table on all (R,S) uses only 176 possible predicates including complements. All 579·176²=17,935,104 fully specified realizations are simulated for the actual 16-step deadline. None is correct on the following 251 inputs: each of the 50 positive bases and the four mutants setting a single cell to 15, together with (7,9,3,0), which is UNSAT. The choice of these particular fixtures only affects how many programs need to be tested before a disagreement is found. A timeout counts as failure.

Reproduce the whole proof computation with the following commands. The Python phase verifies the address and comparison certificates; its export mode generates the 31 surviving aliased palettes from those same tests. [Python finite certificates](../audits/two_load_five_slot_audit.py) · [Complete static control and predicate enumeration](../audits/two_load_five_slot_controls.cpp).

    python3 two_load_five_slot_audit.py
    c++ -O3 -std=c++17 two_load_five_slot_controls.cpp -o /tmp/two-load-controls
    python3 two_load_five_slot_audit.py --emit-palettes | /tmp/two-load-controls

The control-graph census covers this allocation only. A third comparison site can be handled by the separate argument below.

## Trading one LOAD for a third comparison site

The same address filter also eliminates every program with **one LOAD, one ALU and three binary comparison sites** at the 16-step deadline. A direct LOAD would always read only one cell, so require an indirect site. The case d=−1 leaves only R←R+1 modulo 16. The bound of six ALU executions depended on repeating that site, and still holds with a third comparison site.

If the ALU and LOAD destinations differ, R contains only a counter value from 0 through 6 on a positive prefix. Among {8,9},{10,11},{12,13},{14,15} choose a pair e,e+1 containing none of the at most three effective literals at the comparison sites. Set both positive words to 1 and both negative words to e or e+1. Only the first input is SAT. The adjacent negative signed words have identical orders relative to zero, 1, the counter and all branch literals; both also address scratch when used as pointers. Exactly the same comparison-and-load coupling applies.

If the LOAD writes R, then R is the only mutable register. Its address must be R, since any fixed or always-zero address fails to reach four cells. On the sensitive input (4,4,8,8), each informative LOAD leaves R equal to 4 or 8. Neither can reach 0,…,3 with at most six increments unless an intervening scratch LOAD sets R to zero. Thus visiting all four distinct input cells requires at least three extra scratch LOADs and at least 0+1+2+3=6 increments from zero to the four respective addresses. Reusing the sole LOAD site at least seven times also requires at least seven comparisons through the final verdict. This costs at least 20 steps. The remaining allocations with one meaningful load and two branch sites can use two ALUs, or one ALU and one STORE.
