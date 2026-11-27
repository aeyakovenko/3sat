# One-bit DIMACS pins for insert-only dynamic Disjointness

For each universe size $N\ge1$, three fixed-layout proper 3-CNFs encode a set system, inserted elements, and an active query. Up to the choice among the three templates, **all databases start from one blank ASCII file**. Changing an element, query, or graph membership flag takes exactly one physical bit flip. All models are unique when they exist. The encodings concern Ko's online setting, with a family $S_1,\ldots,S_N\subseteq[N]$ supplied at preprocessing, insertions into $X$, and queries whether $X\cap S_j=\varnothing$. The lower bound on amortized online operations is Ko's Theorem 1.1. This note supplies the explicit encodings. [Ko, *Amortized Cell-Probe Lower Bounds for Dynamic Boolean Problems*, Theorem 1.1 and §2.2](https://arxiv.org/abs/2611.11508)

## A pin occupies one mutable digit

For each Boolean flag $p$ create variables $p,\bar p$ with respective identifiers $10k+3,10k+2$, using a different positive $k$ for every flag. Two binary clauses enforce complementation, and a positive unit names the selected member of the pair. Initially the unit names $\bar p$. Switching its last identifier digit from ASCII 2 to 3 sets $p=1$. These bytes differ by one bit; reversing that bit clears the flag. The mutable occurrence appears once, in that unit, independently of the number of subsequent uses of $p$. Every bit position is known from the template before the database is loaded.

Use a fixed bank of distinct false variables to pad short clauses to proper ternaries. Pin three padding constants with the seven ternary clauses excluding every assignment to the triple except their prescribed values. Keep all flag and gate names outside the constant bank. Unused identifiers below the largest declared variable get individual padded negative units. Thus uniqueness includes all declared identifiers. This is the [same pin used for a two-edit butterfly query](two-bit-warm-repair-of-unique-3sat.md).

Write $X_i$ for inserted-element flags, $Y_j$ for active-query flags and $E_{ij}$ for the flag $i\in S_j$. During graph setup, start with $X=Y=E=0$ and turn on exactly the required $E_{ij}$ one at a time. Keep $Y=0$ during an insertion, and turn on $X_i$ in one edit. To issue a query activate $Y_j$, inspect the verdict, and clear $Y_j$ before the next operation. Query indices may repeat. For the distribution with distinct insertions each insertion changes one bit; repeated insertions can be treated as no-ops. Graph setup is a preprocessing step in the online model.

## Three verdicts on fixed flags

**Empty query satisfiable.** For every pair $(i,j)$ use exactly the clause
$$
     (\neg X_i\lor\neg Y_j\lor\neg E_{ij}).
$$
It forbids a collision. Without an active query all inserted and database configurations have a unique model consisting solely of the specified flag pairs, constants, and unused-name pins. With just $Y_j$ active the verdict is disjointness. *Any* one-pin change between two satisfiable files, including a graph-setup change, moves exactly the two coordinates $p,\bar p$ of the unique model.

The distance two is optimal for any one-edit encoding changing just a variable identifier, preserving the literal's sign and all other literals, when the two formulas have different unique models. Write the changed clauses $A\lor\ell_u$ and $A\lor\ell_v$. Each model fails the other formula's changed clause because otherwise it would be its unique model too. Thus $A$ is false at both models, and the two like-signed literals take opposite values in the old model and exchange those values in the new one. Both $u$ and $v$ must change. This argument allows either sign. In the DIMACS grammar that accepts carriage return as token whitespace, a separate sign-slot variant needs just one flag variable: start its padded unit with the variable's negative sign or a leading carriage return. ASCII minus (0x2d) and carriage return (0x0d) differ in one bit. This version changes one model coordinate on satisfiable neighbors. The digit-only files and the census below use the broadly accepted identifier construction. [Earlier sign-slot construction and grammar reference](one-edit-cubic-sat-reduction.md)

**Empty query unsatisfiable.** Compute $C_{ij}=(X_i\land Y_j)\land E_{ij}$, $H_j=\bigvee_i C_{ij}$, and require $\bigvee_j H_j=1$. Represent each binary gate by its full equivalence CNF. Consequently each fixed input has one gate valuation, and requiring its output gives a unique model exactly when a collision exists. While $Y=0$, every insert and every setup step connects two unsatisfiable versions. The canonical gate valuation violates exactly the single padded output unit there. Because the internal AND gates combine $X_i,Y_j$ first, every computed value remains zero during empty-query setup and insertion. The two canonical near-models differ only on the changed flag and its complement. At a query the negation of the verdict answers disjointness.

**Alternating empty-query verdict.** Use the same $H_j$. Define
$$
     D=\bigvee_j(Y_j\land\neg H_j),\qquad
     P=\left(\bigoplus_i X_i\right)\oplus
       \left(\bigoplus_{ij} E_{ij}\right)\oplus Z ,
$$
where $Z$ is one additional complementary pin. Require the output $P\oplus D$ to be one. For every fixed choice of flags there is a unique gate valuation. With $Y=0$ the verdict is $P$. It reverses at every setup edit to $E$ or $Z$, and at every insertion of a fresh $X_i$. Start the blank file with $Z=0$. At the end of graph setup flip $Z$ once precisely if the graph has odd edge count, so the graph parity cancels for all subsequent operations. With exactly $Y_j$ active, the SAT bit is then
$$
     (|X|\bmod 2)\oplus [X\cap S_j=\varnothing].
$$
The online decoder keeps the parity of the number of distinct insertions. For multiple active query flags, $D$ has the same explicit meaning, existence of at least one active disjoint set. Balanced XOR trees limit the number of parity-gate changes on an empty-query graph edit or insertion to $O(\log(N+2))$. Unique-to-unique witness distance two applies to the first template.

Each mode uses $O(N^2)$ rows and declared names after filling the identifier gaps, and has $O(N^2\log(N+2))$ encoded bits (also a matching lower order with these graph pins). OR and XOR trees use distinct input wires and fresh outputs; pairwise clauses for gate equivalence use false padding where needed. The public empty-selector valuation can be computed before any online operation; in the two negative cases the canonical valuation fails just the output pin when the output bit is false. A cold solver scans the pins and graph in $O(L)$ deterministic native time on any of the three templates, where $L$ is the bit length. The same bound allows checking the fixed layout before taking this specialized path on arbitrary SAT inputs. These facts leave the static unrestricted SAT time question open.

The executable audit writes and reparses actual proper DIMACS on every two-by-two database, every selector mask, and both parity-balancing settings. It checks all 1,024 complete-file model counts, all 4,352 pin edges physically, 532 unique-to-unique changes of distance two, 192 negative empty-query steps, and 448 opposite-verdict empty-query steps. The graph-setup edge counts with blank selectors are respectively 32, 32, and 80 across the three modes. [Standard-library native-file audit](../audits/one_bit_disjointness_pin_audit.py)

## Complete trace census for one program at two by two

A fixed, one-register, 42-instruction RAM program decides all 256 files of the direct no-collision template with $N=2$. The files have 1,119 bytes, or 8,952 input bits, packed little-endian into 16-bit words with the final word zero-padded. The eight public mutable bytes occur at offsets 149, 180, 211, 242, 273, 304, 335, and 366. For each of the two query flags in order, the program skips the set if its flag is clear. For each selected set it tests each of the two element flags and reads the corresponding edge pin when that element is active. A collision rejects immediately. Each pin test uses one word load from an immediate address, a shift, a mask and a branch. Accept and reject are explicit halt instructions.

A record contains the incoming program counter and register, instruction and operand, memory address and full word payload on a load, and outgoing program counter and register or terminal verdict. It has no external timestamp. Every program path advances strictly in program-counter order, so equal records in two executions occur in the same relative order. Consequently their longest common subsequence has exactly the size of their set intersection. The audit checks this exact expression against the insertion/deletion dynamic program on every edge.

There are 161 SAT files and 95 UNSAT files. Actual runs take 9–41 instructions. Each row of the table counts unordered pairs differing in one pin bit. Masks number pins from the low bit in the order $X_0,X_1,Y_0,Y_1,E_{00},E_{10},E_{01},E_{11}$. The last two columns give one pair attaining the maximum and the two execution lengths.

| Verdicts | Pairs | Distance zero | Minimum–maximum distance | Maximizing masks | Trace lengths |
|---|---:|---:|---:|---|---|
| SAT, SAT | 532 | 352 | 0–24 | 3, 7 | 9, 25 |
| UNSAT, UNSAT | 268 | 181 | 0–44 | 171, 175 | 25, 21 |
| Opposite | 224 | 0 | 10–46 | 43, 47 | 25, 21 |

For masks 43 and 47 the two executions have no full record in common, despite sharing the program and changing only one physical bit. The maximum-distance UNSAT pair has just one common record. These are exact distances for this particular program and promise. The census contains no exhaustion of alternative RAM programs and supplies no native-time lower bound. The executable also prints the full histogram for each verdict pair and checks each of the 256 answers against the parsed proper formula. [Complete one-program census](../audits/one_bit_disjointness_ram_trace_census.py)
