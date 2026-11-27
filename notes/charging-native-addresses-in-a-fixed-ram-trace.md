# Charging the address constraints of an actual writable RAM execution

Let a correct deterministic word-RAM program halt after $T$ instructions on a base file. Select $m$ distinct physical input words. Assume replacing any nonempty subset of their base words by their respective alternative words changes the required verdict, without changing the file length or public metadata. All other initial memory and register values are fixed on this family. The conclusion below permits arbitrary workspace, arbitrary fixed-label code, register-indirect reads and writes, immediate operands, and program-dependent branches. Each memory instruction, binary word operation and binary comparison costs one. A comparison has fixed successor labels and no other output. A binary arithmetic predicate returning a register value is a word operation.

## Replay with concrete addresses

The base run must load each of the $m$ original words before first overwriting it. Otherwise a single change at that address leaves every register, observed value and instruction label the same up to the first write there, or up to termination. Mark the first such load for each address. The marked loads are distinct.

Make one input node for each changeable word and a literal node for each fixed word value used as data. Follow the actual base trace in static single assignment form. A word operation introduces one result node and one binary operation. For a load, use the symbolic contents of its **concrete base address** as the result. For a store, replace the symbolic contents of its concrete base destination by the symbolic source word. Copies and aliases do not introduce binary operations. In particular, a load after a write reads the most recent store to that address in the base trace, irrespective of how often that address has been read, changed, or restored.

Retain the outcome of every executed comparison. Retain an equality to the actual base address for **every** register-indirect memory access. A literal address is already fixed. Equalities for the $m$ marked first loads are free observations on the wires supplying their addresses. Every other dynamic-address equality is a binary comparison with a fixed literal, charged to that particular load or store. This charge applies at nonzero scratch addresses as well as at zero. There are at most $T-m$ charged factors in total.

**Replay lemma.** An assignment to the input nodes satisfying all these observations follows the same actual machine labels, reads and writes in the same order, and reaches the same terminal verdict. Induct along the base trace. The current registers and memory under the changed assignment equal the evaluations of the current symbolic values. Each address observation gives the same physical location, so a native read or write performs the stated symbolic update. Each branch observation selects the same fixed successor. [Lean proof of dynamic loads, writes, observed branches and complete replay](../lean/NativeTraceForestCharging.lean)

## Counting the connected components

Form an undirected bipartite multigraph of word-value nodes and charged-factor nodes. An arithmetic factor has three incidences, one for each operand and one for its new result. A comparison or charged address equality has two incidences. Repeated operands give two parallel edges. Free address observations decorate their value nodes and add no graph edges. Literal nodes remain distinct from variable nodes even when their base values agree. All source-free components may be left out of the lower-bound count.

A connected component with $s$ input nodes, $c$ literal nodes, $a$ arithmetic factors and $b$ comparison factors has $3a+2b$ edges and $s+c+2a+b$ vertices. Its number of independent cycles is therefore

$$
(a+b)-s-c+1.
$$

Consequently a component with a literal or a cycle costs at least $s$ factors. An acyclic component without a literal costs $s-1$. This count treats multiple comparisons in one component and arbitrary reuse of a register's value by different factors. If $p$ is the number of paid factors and $F$ the number of acyclic, literal-free components containing inputs, then

$$
T\ge m+p,\qquad m\le p+F.
$$

Changing sources inside just one of these components leaves all other components' evaluations and observations fixed. Any change there preserving both the branch observations and its free pins contradicts the replay lemma and the asserted verdict on every nonempty edit.

## A finite sufficient condition

Fix $h\ge1$. Assume every acyclic, literal-free component with at most $h$ sources admits some nonempty edit preserving its ordinary comparison outcomes, when its free pins are temporarily omitted. Let $E$ upper-bound the number of *distinct concrete marked addresses* that can be values of wires in any such small component on the base run. Each small component must contain a free pin, since without one its preserving edit survives. Choose one such pin per component. Distinct pins correspond to distinct mandatory original loads, and those loads have distinct concrete addresses. Thus the number $S$ of small components is at most $E$. If $L$ is the number of remaining acyclic, literal-free components, then $S+(h+1)L\le m$ and $F=S+L$. Hence

$$
(h+1)T+hE\ \ge\ (2h+1)m.
$$

The prior $h=2$ estimate is recovered whenever the only relevant binary test on two homogeneous source words has the same outcome on $(A,A)$ and $(B,B)$. For $h=3$ the coefficient is $7/4$. If every acyclic literal-free component admits a preserving edit even with its free pins in place, no such component can occur and $T\ge2m$.

For a homogeneous file all source words on the base have value $A$. Every live wire in an acyclic, literal-free component with at most $h$ sources is a constant-free term in $A$ with at most $h-1$ operation nodes. Its ancestor expansion is a formula. Repeated use of the same predecessor within that expansion would give two distinct paths to the result, hence a cycle in the incidence multigraph, including a parallel-edge cycle for repeated operands of one factor. Fanout to comparisons or operations elsewhere does not alter this ancestor formula. For $J$ binary word operations, one may take

$$
E\le\sum_{i=0}^{h-1}\mathrm{Catalan}(i)J^i.
$$

This bound counts ordered formula shapes. Numerical coincidences and addresses outside the set of marked input cells only decrease $E$. The proof also works if $E$ is bounded separately for a fixed template. [Original homogeneous DIMACS word family and earlier operand count](executed-operands-on-homogeneous-sat-words.md)

The Lean development checks the replay induction on abstract native word functions and the arithmetic from $(p,S,L,E)$ to the displayed clock bounds. The construction of the incidence multigraph from a finite machine execution and the tree perturbation hypotheses are supplied in the mathematical argument. [Formal statements](../lean/NativeTraceForestCharging.lean)
