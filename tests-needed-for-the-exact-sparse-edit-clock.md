# How many SAT files can certify the exact sparse-edit clock?

Fix the finite family with $m$ marked packed words of common value $A$ and at most $k$ changes, $1\le k\le m$. A change replaces $A$ by $A+e\Delta$ for $e\in\{-2,-1,1,2\}$. The original file is satisfiable and every changed file is unsatisfiable. The [exact clock theorem](exact-executed-clocks-for-sparse-word-edits.md) gives the minimum worst-case instruction count
$$
T_*=2m-\lfloor m/(k+1)\rfloor
$$
even with arbitrary code text, literals and workspace. It gives this lower bound on the center run itself. The [dense, sorted, duplicate-free construction](dense-sorted-cores-for-ram-exhaustion.md#an-exact-executed-step-seed-inside-the-restricted-files) obeys the same word conditions on infinitely many lengths.

How many labeled examples from this promise are needed to witness that exact bound? Call a suite sufficient if every program correct on its files takes at least $T_*$ instructions on the center. Include the center in all suites; counts below refer only to negative files. A **homogeneous edit** changes the words on a specified nonempty support to the same one of the four noncenter values. An example containing several different edited values cannot stand in for a required homogeneous edit.

## Programs one instruction below the optimal clock

Put $q=\lfloor m/(k+1)\rfloor+1$. Select $q$ disjoint nonempty blocks of sites; individually check every remaining site against its center literal. Within each block LOAD its first word and require every other loaded word to equal that first word, using one branch per equality. This uses exactly $m$ LOADs and $m-q$ comparisons on the center, for a total $2m-q=T_*-1$. The program accepts precisely if each block is constant and every individually checked word is central. Its code can be fully unrolled with immediate addresses. The same construction also works with more blocks and an earlier deadline. One may pad each early rejection path using fixed moves so that all inputs actually run for exactly $T_*-1$ steps, including the rejecting ones.

Write $m=a(k+1)+r$, $0\le r\le k$. For every nonempty $S\subseteq[m]$ of size at most $r$, take $S$ as one unchecked block, make $a$ more unchecked blocks of size $k+1$ from its complement, and check the leftover sites individually. On the promise the only false accepts are the four homogeneous edits with support *exactly* $S$. Consequently every sufficient suite has a homogeneous edit for every such support. In particular:

* For $k=m$ the suite needs at least $2^m-1$ negative files. Even omitting one support lets a different unrolled program pass every remaining test one instruction below the claimed threshold.
* For $m=2k+1$ it needs at least $2^{m-1}-1$ negative files. Here only changes of at most half the marked words are permitted.
* For any residue $r$ it needs at least $\sum_{i=1}^r\binom mi$ homogeneous edits on distinct supports. This particular estimate is zero at $r=0$.

There is an effective lower bound even at residue zero. Let $b=k+1-r$ and suppose $q\ge b$. Choose $b$ disjoint blocks of size $k$. The remaining sites split into $q-b$ blocks of size $k+1$ because $bk+(q-b)(k+1)=m$. The only false accepts are the homogeneous edits on the $b$ small blocks: the promised support cannot contain two of them or any larger block. Let $H_k$ be the $k$-supports represented by a homogeneous edit in the suite. The complement of $H_k$ therefore contains no $b$ pairwise disjoint members. A maximal disjoint family in this complement meets every missing support. Its union has at most $k(b-1)$ sites. Every $k$-set outside that union must belong to $H_k$, giving
$$
 |H_k|\ge \binom{m-k(b-1)}{k}.
$$
For each fixed $k$, as $m$ grows this is $(1-O_k(1/m))\binom mk$ at **every** residue. More generally the same fraction tends to one for $k^3=o(m)$. The matching-number problem for uniform set families is classical. Its elementary cover bound suffices here. [Frankl and Kupavskii, *Families with no matchings of size s*](https://kupavskii.com/wp-content/uploads/2017/10/Frankl-Kupavskii_Matchings.pdf)

For this equality-block subclass the matching criterion is exact when $q\ge b$ and the suite already contains a fixed common digit on every support of size less than $k$, with its remaining tests using that same digit on selected $k$-supports. If an unchecked block is smaller than $k$, its test catches the program. Otherwise there must be at least $b$ unchecked blocks of size $k$, since the total size is at most $m=q(k+1)-b$. A matching obstruction as above consequently catches it. Conversely a matching of $b$ missing supports constructs a program that passes every test. More than $q$ unchecked blocks only strengthens the counting condition.

## Black-box detection and the role of observing a trace

In the $b$-block construction, choose the partition uniformly after a random permutation of the sites. Every fixed $k$-set is a small block with probability $b/\binom mk$. Thus any single test catches this random program with probability at most $b/\binom mk$. The bound is attained against *each* program in the family by choosing a uniform $k$-set and changing it homogeneously. This is an exact one-test minimax probability for these candidates. Up to the first error all replies, including the padded elapsed times, follow the unique correct-answer transcript. For a deterministic adaptive tester, its first $u$ tests on that transcript catch the random program with probability at most $ub/\binom mk$. Averaging over a tester's private coins preserves the bound. When $k=m$, the same reasoning with an unchecked block chosen uniformly among all $2^m-1$ nonempty subsets gives one-test probability $1/(2^m-1)$.

For all $m>k$, even when $q<b$, one can use a uniform partition into $q$ blocks with sizes differing by at most one. Any two of these blocks together exceed $k$. When $q=2$ their combined size is $m>k$. For $q\ge3$, the smaller size is at least $\lfloor 2(k+1)/3\rfloor>k/2$ (also for $k=1,2$). If there are $q_j$ blocks of size $j\le k$, the exact one-test probability becomes $\max_{j:q_j>0,\,j\le k} q_j/\binom mj$, by choosing a homogeneous test at a maximizing size. At least one size is eligible since $m<q(k+1)$. This takes exponentially many black-box tests for constant worst-case detection probability whenever $k/m$ is bounded below and $m>k$ grows. The bound concerns testing with only the verdict and elapsed time. A code-aware examiner inspecting one of these unrolled programs can read its blocks and name a failing input directly. No lower bound on proof length follows.

## All supports in one fixed digit can still miss a native program

Take the dense, sorted family, $k=m$, and private center word $A$ consisting entirely of ASCII 5s, so $255A=53(Q-1)$ for $Q=2^w$. Use the digit-7 edit $B=A+2\Delta$, a bitwise supermask of $A$. At infinitely many dense-core lengths the order of $2\Delta$ modulo $Q$ exceeds 255. Indeed the widths of those cores run through every sufficiently large multiple of 16: increasing the decimal-name length by one multiplies the file length by a factor tending to 10, so consecutive logarithms differ by less than 16. Choose widths divisible by 48. Their odd part is divisible by three, so the chosen base-256 repunit length $\ell$ is a multiple of three as $256\equiv1\pmod 3$. Since the repunit is odd, the additive order of $2\Delta$ is $2^{8\ell-1}$.

Choose 510 marked words, pairing them into 255 disjoint pairs. On the left, sum the bitwise ORs of 202 pairs. On the right, sum the bitwise NORs of the other 53 pairs. Compare the two sums for equality. Check all remaining marked words individually against $A$. The test uses one native binary bitwise truth table for each NOR, as allowed in the journal ISA. At the center the two sums coincide modulo $Q$, since their difference is
$$
 202A-53(-1-A)=255A+53=0\pmod Q .
$$
On any pattern of $B$ changes among the 510 sites, the difference increases by exactly $2\Delta$ times the number of touched pairs. Its coefficient is between 1 and 255 on a nonempty pattern, and the modular order prevents wrap to zero. Changes outside the 510 sites are rejected individually. Hence the program answers correctly on all $2^m-1$ nonempty supports when each is tested only with digit 7. It nevertheless accepts a file with a single digit-4 edit in an OR pair: this word is a submask of its unchanged partner, so their OR stays $A$.

The center run uses 510 LOADs on the paired sites, 255 bitwise instructions, $201+52$ additions and one branch, totaling $2\cdot510-1$ steps there. Each other site costs two. The result is a genuine $2m-1$ instruction counterexample to this proposed test suite at $T_*=2m$, without any space or code-size restriction. The construction uses one globally fixed digit for all supports, and does not settle the optimum over choices of different digits for different supports. A machine offering separate OR and NOT but no binary NOR would need its own cost analysis.

## Even all four homogeneous digits can miss one data-dependent LOAD

A second construction works using only addition, multiplication, ordinary comparison, and LOAD. It uses a different proper DIMACS serialization with $m=\Theta(n/\log n)$ marked words. At $k=m$, test **every nonempty support with each of the four digits**, together with the satisfiable center. There is an actual program that passes all those tests and accepts the center in $2m-1$ instructions. A file with just two changed words and opposite deviations defeats it.

Take arbitrarily large $w=16\cdot3^j$, $Q=2^w$, $W=w/8$, and $n=w\lfloor Q/(2w)\rfloor$. The standard width at this input length really is $w$. Use $\ell=3^j=W/2$: the repunit $S_\ell=(256^\ell-1)/255$ is divisible by $3^j$, since $S_{3t}=S_t(1+256^t+256^{2t})$ and the second factor is divisible by 3. Here
$$
 \Delta=(Q-\sqrt Q)/255=256^{W-\ell}S_\ell.
$$
It has the shift-count and square-zero properties of the sparse-edit theorem. A marked word is a full $W$-digit variable name with first $W-\ell$ digits 5 and remaining $\ell$ digits all set to one common digit from 3 through 7. Pin the center name true, the other four names false, and names 1 and 2 false by four proper clauses per pin using dummies 8 and 9. Then each test record is the positive clause on the marked name, 1, and 2. Its satisfiability condition is the same center-only test as before. The header declares the largest used name and the correct clause count.

The fixed header and pins occupy a bounded number of words at the beginning, fewer than 256 at large sizes. Align 510 test names at addresses $256+3i$ for $0\le i<510$, plus one at $b=2809$. Finish each of these clauses in the following word, and use whitespace between complete records. Place the remaining whole marked words three addresses apart inside the third quarter of the file. Fill the gap from the low records to this quarter with space bytes. This leaves $m$ a positive fraction of all physical words. Every field and its suffix fits, unused names are permitted, and changing digits inside the marked word preserves its byte length and its clause boundaries. The $2m$ lower bound for the full edit promise applies by the same five values and forest proof. This particular construction allows repeated clauses and ordinary whitespace.

Individually check every marked site except the 511 low ones. On the first 255 of the 510 sites, sum their raw words; do the same on the second 255 sites. Multiply the two sums modulo $Q$, LOAD at the computed address and accept exactly if the reply equals $A$. On the center both sums are $255A=-53\pmod Q$. The product is $b$, so its LOAD returns the last compulsory marked word. Any earlier edited words of a common deviation $d\Delta$, $d\in\{-2,-1,1,2\}$, give the address
$$
 b-53dt\Delta\pmod Q,
$$
where $1\le t\le510$ is their total count across the two sums. This follows by expanding their product and using $\Delta^2=0$.

Write $C=53dt$. If $255$ does not divide $C$, the computed address differs from a nonzero multiple of $Q/255$ by $O(\sqrt Q)$ in circular distance. Its address is outside the file for large $w$, since the file has $O(Q/w)$ words. If $C=255u$, the address is $b+u\sqrt Q$ modulo $Q$, with $u$ a nonzero integer of bounded magnitude. It is either outside the file or in the all-space gap between the low records and the third quarter. Every such LOAD therefore returns a word different from $A$. With no edit on the first 510 sites, an edit at $b$ is seen directly. Any edit elsewhere already fails its individual check. All four homogeneous suites are passed. In contrast, edit two sites in the first sum by $+\Delta$ and $-\Delta$. The original address and verdict are preserved, although the resulting formula is unsatisfiable.

The 511 low sites cost 510 initial LOADs, 508 additions, one multiplication, one indirect LOAD, and one final comparison, totaling 1,021 steps instead of 1,022. This one-instruction saving is shared by all the examples. No fixed-address equality-block model detects it. The physical analysis works for every integer $C=53s$ with $0<|s|\le1020$, including both signs. Thus one can move the 510 sum operands to **any** chosen 510 marked sites $G$ excluding $b$, checking all other sites except $b$ individually. If the changes in $G$ sum to $s$ in deviation units, the computed address is $b-53s\Delta$, by the same product expansion. On a nonzero sum its destination remains off-file or in the public space gap, disjoint from *all* marked sites, so no simultaneous edits can change the word read there. The only false accepts have a nonempty support contained in $G$, zero sum, and an unchanged word at $b$.

Write $v=m-1$. The suite must therefore contain a zero-sum edit supported in each 510-set of the $v$ sites. Each such edit is mixed and uses at least two sites. Pick any pair from each of its supports, omitting tests involving $b$ or nonzero sums. The chosen pairs form a graph with independence number at most 509, since every 510-set contains one entire tested support. Partition the $v$ sites into 509 classes of sizes $p_i$ differing by at most one. The necessary number of additional mixed tests is at least
$$
 E=\sum_i\binom{p_i}{2}=\frac{v^2}{2\cdot509}-O(v).
$$
This is sharp against just the shifted choices of $G$: put opposite unit deviations on every pair in one class, testing every within-class pair. Each 510-set contains such a pair. The same physical suite still needs at least $2^m-1$ *homogeneous* tests against the other programs above. Hence $2^m-1+E$ negative tests are necessary for the full instruction set on this family.

For completeness the graph estimate follows by averaging. In a uniform random ordering select each vertex earlier than every neighbor. The selected set is independent and its expected size is $\sum_i 1/(1+d_i)$ for degrees $d_i$. With $t=\lfloor v/509\rfloor$, the affine line through $(t-1,1/t)$ and $(t,1/(t+1))$ lies below $1/(1+d)$ at every nonnegative integer $d$, by convexity and the adjacency of these two integers. On the disjoint union of the balanced cliques the degrees are exactly $t-1,t$ and the sum of reciprocals is 509. For fewer than $E$ edges the degree sum is smaller, so the sum of that decreasing affine bound is strictly greater than 509. This contradicts the independence bound. It is the complement form of Turán's graph theorem.


## A smaller suite that works for the full instruction set

The following sufficient suite permits a single absolute edit magnitude on each tested file. For every nonempty support of size $j\le k$, test all sign patterns with magnitudes all 1 or magnitudes all 2. The number of negative files is
$$
 2\sum_{j=1}^k 2^j\binom mj.
$$
The full original promise has $\sum_{j=1}^k4^j\binom mj$ negative files. The smaller suite still forces $T_*$ against all allowed branches, arithmetic, shifts, rotations, and writable-memory operations, and the same matching upper program still attains the clock.

To prove this, a program passing every single edit must have read all $m$ marked originals on the center before any destructive overwrite or verdict. Use the [instruction replay argument](exact-executed-clocks-for-sparse-word-edits.md#counting-constraints-on-a-single-accepting-ram-execution). If the center took less than $T_*$, its graph of raw-operand constraints would have at least $q$ tree components without unary constraints. Some such tree has at most $k$ sites. It suffices to perturb just that tree, keeping every numerical result, address, and branch on the original center trace.

Write its raw value at vertex $i$ as $A+d_i\Delta$. The elementary opcode check from the replay theorem gives the following stronger selection of permitted pairs on its edges:

* On a rigid edge, either $d_j=d_i$ always works or $d_j=-d_i$ always works. Subtraction, comparisons and bitwise operations constant on the diagonal accept equal choices. Addition and multiplication accept opposite choices using $\Delta^2=0$ modulo the word modulus.
* On a directed edge, keeping one specified endpoint central allows every change on the other side. Use this conservative rule for projections and their complements, and for shifts/rotations with the data operand kept central, since the effective count is unchanged.
* On each remaining edge either endpoint alone can change by a prescribed deviation. For AND and its complement use $+2$, the supermask of center. For OR and its complement use $-1$, the submask.

Contract each connected rigid subtree. Its values can be assigned as consistent signed copies of an arbitrary root deviation, since it has no cycle. Suppose the resulting tree has $h$ edges of the third kind and $d$ directed edges, hence $d+h+1$ contracted vertices. Mark the side which must be kept central on each directed edge. At most $d$ vertices are marked, leaving at least $h+1$ unmarked vertices. Only $2h$ incidences of the third kind exist. Some unmarked vertex is incident to at most one edge of this kind. Change only its rigid subtree. With no prescribed incident deviation choose a nonzero value for its root freely. With one prescription choose the root to give the required deviation at that edge's actual endpoint. Every rigid edge now satisfies its rule, every boundary succeeds against a central neighbor, and all nonzero deviations have the same absolute value. This produces one of the tested files, on which the original run still accepts.

The one-instruction deficit is essential to the test-size results. They concern this exact finite native clock, which is proportional to input *words*. They give no unconditional superlinear time lower bound in encoded bits. For fixed $k$ the suite sizes for the full instruction set are now $\Theta_k(m^k)$ as $m$ grows; the exact number for all opcodes and growing $k$ remains unresolved. [Lean count and block semantics](SparseEditTestSuites.lean) · [Finite opcode and partition audit](sparse_edit_test_suite_audit.py)
