# Charging an actual RAM run for a quadratic check on each packed record

I found two families of proper ASCII 3-CNFs with the same encoded length, the same number of positive files, and the same inherited lower bound on the number of cycles in a semantic graph certificate. Both admit a globally correct SAT solver taking \(O(N/\log N)\) native instructions on the family. Their execution costs separate when the solver uses comparisons and simple arithmetic in place of data-dependent word lookups.

**On the quadratic family, every correct deterministic solver satisfies**
\[
3(T-H)+2wH\ \ge\ (3/16-o(1))N
\]
**on at least a \(1-2^{-k}\) fraction of the positive files**, where \(k\) is the number of records, \(T\) is the actual instruction count, and \(w=\Theta(\log N)\). Here \(H\) counts instructions outside the following class on the run: binary-affine word operations, loads and stores at public addresses, equality and signed or unsigned order comparisons, and addition or subtraction of a publicly specified signed power of two. Public addresses and constants may be determined by the fixed layout and preceding control history. A shift count or addend that happens to take one of these special values on the sampled input alone does not qualify. Workspace is unrestricted.

Thus a solver using \(o(N/w)\) other instructions needs at least \((1/16-o(1))N\) elapsed steps on those positive files. A solver finishing in \(o(N)\) steps needs at least \((3/32-o(1))N/w\) other instructions there. On the linear family, a globally correct solver handles every file in \(o(N)\) elapsed steps using public addresses and simple operations on the record data.

The unrestricted linear, quadratic, and cubic SAT time questions remain open. The obstruction here can be measured exactly: one native indirect load can perform \(m\) independent binary dimensions’ worth of algebraic processing, where \(m=\Theta(w)\), on every record.

## The two physical SAT families

Use the journal’s greedy code \(G\) on \(t=\max(4,\lfloor\log_2(k+1)/16\rfloor)\) bits. It takes words in numerical order, retaining each word at distance at least \(d\) from its predecessors, with \(d=\max(3,\lfloor\sqrt{t/\lceil\log_2(t+2)\rceil}\rfloor)\). Conway and Sloane proved that this binary lexicode is linear. If \(r=\dim G\), greedy covering gives
\[
2^r\sum_{j<d}\binom tj\ge 2^t,\qquad t-r=O(\sqrt{t\log t}).
\]
The journal’s repeated seven-bit Hamming code is also linear. On both original code families, restricting the records to their code spaces already fixes the verdict. Their graph-cycle bounds alone therefore supply no further affine processing charge on that restriction. [Conway and Sloane, Theorems 1 and 3](https://www2.kenyon.edu/Depts/Math/Aydin/Teach/Fall06/328/Lexicodes.pdf) · [Journal’s packed code construction and graph theorem](hamming-cycles-in-the-physical-sat-verdict.md)

Choose a basis of \(G\) in numerical order. Write its coordinates as \((x,y,z,v)\), where \(x,y\in\mathbb F_2^m\), \(m=\lfloor(r-1)/2\rfloor\), \(z\) is one bit, and \(v\) contains the possible leftover bit. Compare two allowed record sets:
\[
C_L=\{s\in G:z=0\},\qquad
C_Q=\{s\in G:z=x\cdot y\}.
\]
Each has \(2^{r-1}\) words and inherits minimum distance at least \(d\). The journal’s graph theorem therefore gives the same lower bound
\[
k(r-1)-k\left\lfloor\frac{t}{\lceil d/2\rceil}\right\rfloor=(1-o(1))kt
\]
on independent binary-wire cycles for either decision relation.

The physical file pins a flag \(F_s\) to the membership bit for each possible record \(s\). Anchors 1 and 2 are forced false. Each of the \(k\) data rows is the proper clause \((F_s,1,2)\), so the file is SAT exactly when all records are allowed. The decimal identifier for \(F_s\) is the character `1` followed by \(u=\lceil t/3\rceil\) octal digit characters. These characters put the \(t\) editable bits directly in the file.

Both tables have the same number of minus signs. Each data row, including its newline, costs exactly \(u+8\) bytes. More explicitly, let \(M\) be the largest flag identifier and \(P\) the prefix length in bytes. With the audit’s one-character mode tags,
\[
P=|\mathrm{header\ including\ comment}|+80+
\sum_{a=5}^{M}\bigl(8+\operatorname{digits}_{10}(a)\bigr)-2^{r-1}.
\]
The 80 bytes are the eight anchor clauses. A positive flag row is one byte shorter than the filler row counted for its identifier. Since \(M=O(10^u)\), \(P=o(k)\). Consequently both modes have exactly the same physical length
\[
N=8\bigl(P+k(u+8)\bigr),\qquad kt=(3/8-o(1))N.
\]

## Charging an actual execution

Start with a uniform input on \(G^k\). Every physical input bit is affine in its \(kr\) coordinates. Refine the inputs reaching each instruction into affine subspaces, called flats, on which the program counter is fixed and all register bits and fixed-address memory bits are affine. Each independent parity test used in a refinement costs one dimension. Conditional on reaching a flat, the input is uniform there.

Two kinds of cost suffice. Let \(D\) count deterministically budgeted parity tests. Let \(J\) count searches that inspect affine bits in order until the first exception, skipping tests whose answers are already forced. If one such search uses \(B\) independent tests, then
\[
\Pr(B\ge j\mid\text{incoming flat})\le 2^{1-j}\quad(j\ge1).
\]
Reaching the next independent test requires the continuation outcome of the preceding fair bit. This holds after adaptive branches and earlier writes.

| Native instruction | Sufficient refinement |
|---|---|
| XOR, fixed masks, fixed shifts or rotations, public-address access | No tests |
| Equality or disequality | One first-difference search on the XOR of the operands |
| Signed or unsigned order branch | One first-difference search from the high end, then at most one operand bit to determine the direction. Flipping both sign bits gives signed order |
| Add or subtract \(2^j\) modulo \(2^w\) | One search from bit \(j\) for the end of the carry or borrow. On each resulting flat the word changes by a fixed XOR mask |
| General word addition or subtraction | At most \(w-1\) tests. Fix the lower propagate bits. Each carry then either propagates or is an affine operand bit. Subtraction uses the complemented second operand and initial carry one |
| Word AND or OR, variable shift or rotation | At most \(w\) tests to fix one operand or the shift count |
| Indirect load or store | At most \(w\) tests to fix the address. The selected cell then has its actual latest contents, and a store installs its affine payload there |
| Other deterministic binary word arithmetic | At most \(2w\) tests to fix both operands, including for multiplication and signed or unsigned division with specified exceptional cases |

Signed truncating division illustrates why the arithmetic convention matters. For a positive representable divisor \(2^j\), unsigned division is a fixed shift. For signed division, fix the sign and test whether the low \(j\) bits are nonzero. Only a negative dividend with nonzero remainder needs an increment after arithmetic right shift. This gives one deterministic bit and at most two first-exception searches.

The earlier journal argument gave an expected cost below two for an equality search on a uniform flat. An expectation on \(G^k\) alone is insufficient here because the positive inputs have probability \(2^{-k}\). The following tail estimate pays for conditioning on precisely that event. [Earlier affine simulation and equality-guard bound](affine-guards-for-writable-memory.md)

For \(0<s<1\), put
\[
M_s=\frac{2^s}{2-2^s},\qquad b_s=\frac{\log_2 M_s}{s}=2+O(s).
\]
The geometric tail gives \(\mathbb E[2^{sB}\mid\text{incoming flat}]\le M_s\). If \(Q\) is the cumulative dimension loss, then \(2^{sQ-sD}M_s^{-J}\) has conditional expected multiplier at most one at each instruction. This applies through the actual halt. At fixed input length a total decider has finite maximum running time on the finite family.

On a positive terminal flat, the projection to each record lies in the graph \(z=x\cdot y\). Project that graph flat onto \((x,y,v)\). The projection is injective, and \(x\cdot y\) is affine on its image. The polar form on \((x,y)\) is nondegenerate of rank \(2m\), so an isotropic subspace there has dimension at most \(m\). Including \(v\), the record projection loses at least \(m+1\) dimensions from \(G\). Fixing \(x\) and imposing the resulting linear equation on \(z\) attains the bound. A joint flat has dimension at most the sum of its projection dimensions, even when it correlates different records. Hence every accepting terminal flat has
\[
Q\ge R=k(m+1).
\]

Markov’s inequality and the positive density \(2^{-k}\) now give the finite bound
\[
\Pr_{C_Q^k}\!\left[D+b_sJ\le R-a\right]\le 2^{k-sa}.
\]
Take \(s=t^{-1/2}\) and \(a=2k/s\). Except on a \(2^{-k}\) fraction of positives, the weighted cost \(W=D+2J\) is at least
\[
R-O(k\sqrt t)=(3/16-o(1))N.
\]
The instruction table gives \(W\le 3(T-H)+2wH\), proving the elapsed-time tradeoff. The coefficient \(3/16\) prices weighted operations per **encoded bit**. The corresponding elapsed coefficient when \(H=o(N/w)\) is \(1/16\).

## Where the unrestricted proof fails

On the linear family, \(t-r+1\) parity checks suffice per record. Each check is a fixed mask on the actual ASCII field followed by \(O(\log t)\) shifts and XORs to fold its parity. The prefix, basis, and masks can be constructed and verified in \(O(4^t\operatorname{poly}(t))=o(k)\) steps. Checking the fixed row syntax and all syndromes takes
\[
O\bigl(k[1+(t-r+1)\log t]\bigr)=o(N).
\]
A globally correct program validates the layout and sends other files to a general solver. On the quadratic family there is an \(O(N)\) path using the same simple instructions: for each set record bit, XOR its public column into a coordinate word, then evaluate the dot product with \(O(t)\) scalar operations. Thus the restricted linear order of growth is attained.

For the unrestricted scanner, build one dictionary on the \(8u\) raw suffix bits. Its \(O(2^{8u}\operatorname{poly}(t))=o(k)\) construction cost includes invalid spellings. Each record then takes a constant number of instructions to validate and look up. Both modes take \(O(k)=O(N/w)\) elapsed time, including setup.

On \(G\), one such lookup returns the bit \(1+z+x\cdot y\). **The exact minimum codimension needed to make that one returned bit affine is \(m\), through every address.** The polar rank gives the lower bound, and fixing \(x\) attains it. The same dictionary realizes this loss \(k\) times. This refutes a constant affine-loss bound per native step even after amortizing table construction. The simulation also identifies its oracle boundary: a query on an entire packed memory range can test all records in one operation, bypassing the bounded-operand refinement. [Journal’s oracle instruction model](relativized-clock.md)

## Checks

- At the legal scale \(t=800,\ k=2^{12800}-1\), exact integer arithmetic gives \(d=8\), covering-ball volume \(40{,}889{,}234{,}397{,}405{,}561\), \(r\ge745\), \(R\ge373k\), and \(2200k<N<2201k\). With \(2^s=17/16\), the integer inequality \(4(17/15)^{169}<(17/16)^{373}\) certifies \(\Pr[W\le338k]\le2^{-k}\). This already exceeds \(0.153N\) as a weighted threshold.
- The audit compared **768 serialized proper DIMACS files** against generic DPLL and record lookup, obtaining 144 positives. It checked 349,313 first-exception leaves on all 26,387 affine flats of six bits, 81,920 signed and unsigned power-of-two division cases, and a two-store indirect trace on all 4,096 inputs. The small physical fixtures use \(t=7\) so their complete flag tables can be tested.
- On the local 16-selector-bit census, **every one of the 6,560 positive inputs lies on an accepting flat of maximum dimension eight**. Each positive/negative unit-bit pair projects into the three-point disjointness triangle, so its affine projection has dimension at most one. Equality in all eight coordinates forces a product of lines. Exactly \(3^8-2^8=6{,}305\) such products exclude the all-negative mask. Exhaustion confirmed their union is exactly the positive set. Thus this local affine dimension is identical on positive inputs with different native clocks. I replayed the nine-step program on all 65,536 files and checked archived receipt coverage. The nine-step lower bound and the 28-of-64 cohort bound use the earlier census. [Finite clock proof](exact-nine-step-clock-for-four-sat-words.md) · [Round 4 cohort result](which-four-word-sat-targets-finish-in-seven-steps.md)

Reproduce with `OPENBLAS_NUM_THREADS=1 python3 -B conditional_affine_run_cost_audit.py`. The positive-run tail bound and the comparison of the two native algorithms are manuscript arguments. Priority for this formulation is unverified. [Round 5 audit](../audits/conditional_affine_run_cost_audit.py)
