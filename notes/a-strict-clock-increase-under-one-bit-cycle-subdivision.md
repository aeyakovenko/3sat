# Exact RAM instruction counts on sixteen cyclic selector files as their lengths increase

Pack a cyclic selector mask low bit first into words of width $w=\lceil\log_2 L\rceil$ at physical selector length $L$. The catalog is SAT if some adjacent bits are both zero, including the wraparound. A *cover* is the opposite verdict. Each result below concerns the minimum, over all programs correct on the indicated domain, of their worst-case number of executed instructions. The native instruction set has separate loads, stores, 24 binary numerical operations, and two-operand comparisons with fixed successor labels. Scratch is initially zero and every address representable by the word is writable. Programs may use arbitrary text, register destinations, dynamic addresses and embedded word literals. The fixed cyclic clause template realizes these verdicts as satisfiability. The measured input length counts the selectors. [Catalog, physical encoding and opcodes](a-shared-nine-step-obstruction-and-the-next-native-width.md)

Three injective, verdict-preserving Boolean polynomial maps on their full source cubes carry the same sixteen four-bit inputs through lengths five, six, and seven. At these four lengths the exact worst-case instruction counts are **4, 6, 6, and 7**. On the complete seven-bit catalog, indirect loads and comparisons suffice for seven instructions, while direct loads and comparisons require eight. The last increase can be attained by inserting the XOR of two neighboring bits. There is also a sixteen-input example on which every globally affine extension takes at most six instructions on its image, while inserting OR gives seven.

The four-bit catalog has exact clock **4**. Insert the XOR of two adjacent bits, keeping all four original bits, and consider just the sixteen resulting masks. The exact clock becomes **5** for three of the four insertion positions. The fourth position retains clock **4**. The full catalog of all 32 five-bit masks has exact clock **6**. Thus a depth-five program fails on a valid five-bit mask, and the restriction to one sixteen-mask image makes a measurable difference.

| Gap after old bit, numbered from the low bit | 0 | 1 | 2 | 3 (wrap) |
| --- | ---: | ---: | ---: | ---: |
| Exact worst-case clock on its five-bit XOR image | 5 | 4 | 5 | 5 |

Each old edge with both incident bits zero gives two such edges after the insertion, and each old edge without such a pair gives none at that position. This proves verdict preservation at every length. Here we compare the optimal clocks on both sides, including every possible program specialized to the new image. For any depth below one of the stated optimum clocks, any correct program exceeds that depth on both a satisfiable and an unsatisfiable member of the indicated domain: otherwise truncate all still-running paths at that depth to the opposite verdict.

## Direct upper programs

On four bits let $a,b,c,d$ denote bits in increasing order. A cover has $(a\land c)\lor(b\land d)$. The two words are $a+2b$ and $c+2d$. Two loads, bitwise AND, and a nonzero branch decide the catalog.

For gap zero write $x=a+2(a\oplus b)+4b$ and $y=c+2d$ for the new three-bit words. The low two bits of $-x$ are exactly $a+2b$ for every $a,b$. Two loads, a modular subtraction from zero, bitwise AND, and a nonzero branch therefore suffice. On this image the new instruction recovers the old pairing from the repacked bits.

The other short programs below return the cover bit. Each starts with the two loads. Comparisons with literals in a return are paid branches. Division is unsigned and returns zero when the divisor is zero.

| Domain | Program after loading $x,y$ |
| --- | --- |
| XOR gap 1 | Return $(x\mathbin{\&}y)\ne0$. |
| XOR gap 2 | Form $s=x^2\bmod 8$. If $s<x$ in signed order, return $y\ge2$. Otherwise return $x\ge5$. |
| XOR gap 3 | If $x<y$, return $x=2$. Otherwise form $x/y$ and return whether it exceeds 1. |
| All five-bit masks | If $x=y$, return $x>2$. Otherwise, if $y<2$, form $x\mathbin{\&}y$ and return whether it is nonzero. Otherwise, if $x<y$, return $x=2$, and in the remaining case return $x\ge5$. |

With a fixed three-bit word width at *both* physical lengths, the complete clocks are 5 on four bits and 6 on five bits. The four-bit upper at width three forms $s=x^2\bmod8$ after its two loads, returns $y\ne0$ if $s<x$ in signed order, and returns $x\ge5$ otherwise. This checks the change of word-width convention separately from the change of domain. At canonical width the smaller complete cycles of lengths two and three have clocks 3 and 4 respectively, counting the length-two cycle with the same wraparound rule.

## Degree two is necessary and sufficient to attain six on the image

There is an injective polynomial map $Q:\mathbb F_2^4\to\mathbb F_2^5$ of degree two whose image has exact clock **6** and which preserves the verdict of every source mask. Write a five-bit coefficient as a decimal word whose low bit is coordinate zero. For a monomial indexed by a subset mask $s$, use the following coefficient word, in order $s=0,\ldots,15$.

```
 9 14 26 30 16 10 6 0 7 12 3 0 12 0 0 0
```

Evaluate $Q(v)$ by XORing the coefficients with $s\mathbin{\&}v=s$. All terms of degree three or higher vanish. Its sixteen outputs in input order are

```
 9 7 19 3 25 29 5 31 14 12 23 11 18 26 13 27
```

They are distinct, and direct evaluation of cyclic adjacency gives the same verdict as before on every row. Exhausting the native instructions on just these rows excludes five steps. The six-step full-catalog program above supplies the matching upper bound. This map may change the old coordinates. It increases physical length by one bit.

No injective affine map preserving the four-bit verdict can achieve six steps on its image. Its image must be an affine hyperplane of the five-dimensional bit space. The source has seven covers, and their XOR is $15$, itself a cover. Since seven is odd, an affine map takes this XOR to the XOR of the image covers. Testing those two necessary conditions on all 62 affine hyperplanes leaves exactly the five zero-offset hyperplanes with normal masks $7,14,19,25,28$. They specify the vanishing parity of three consecutive cyclic coordinates. A program of at most five steps exists on each of the five planes; the search includes the plane with normal 19, whose deleted position is the low bit and so was absent from the four fixed-origin gaps. The attainable clocks are exactly 4 and 5 for degree one. For each exact degree 2, 3 and 4, every clock from 2 to 6 occurs. Two instructions are necessary because both verdicts occur and the machine must both load and branch. The full-catalog program caps every image at six. The degree and clock checks supply examples at all intermediate values. [Degree spectra](../upstream-checks/cycle-clock/CycleEncodingDegrees.lean) · [Quadratic witnesses](../upstream-checks/cycle-clock/QuadraticDefs.lean)

The lower degree limit follows by covering every affine candidate. It does not rely on a random search for good affine maps.

## Preserving that increase on the same sixteen files

Write $H$ for the sixteen five-bit outputs of $Q$. There is an injective degree-two map $R$ on **all 32** five-bit inputs that preserves every verdict and takes $H$ to a six-bit suite with the same exact clock six. With the same subset convention its six-bit coefficient words are

```
60 48 50 34 44 47 6 0 46 52 51 0 10 0 0 0
31 25 51  0 55  0 0 0 21  0  0 0  0 0 0 0
```

The sorted composite image is $\{5,15,21,22,25,27,28,31,34,41,42,45,51,52,53,59\}$. Enumerating five native instructions on these specific rows rules out a decider. The six-step upper for all six-bit inputs applies. The resulting sequence on the same sixteen ancestors is **4, 6, 6**. Lean verifies the second map on its entire domain, including injectivity and the image computation. [Second quadratic witness](../lean/QuadraticFiveToSixWitness.lean)

Every affine verdict-preserving map from five bits to six loses this six-step bound on $H$. There are precisely sixty such maps; each of their sixty images admits a five-step program. The all-length classification identifies these choices with XOR insertion and the dihedral symmetries of the cycle. Thus changing the degree of the second map is essential for this particular inheritance. [Classification, proof and replay](affine-successors-of-cycle-cover-selectors.md)

## Exhaustion of all small executions

One column of word values, with a row for every allowed input, describes a live register. One column per address describes all writable memory. Start with the actual packed input in memory and all word literals available. The search handles a comparison by partitioning the remaining rows, checking the two successors independently. An ALU instruction or load appends its result column. A store changes one addressed entry on each input row. Equal register columns can be merged. Old register values are retained because programs may assign fresh destinations. Conversely a successful finite tree in this semantics can use fresh registers and receive its own finite code labels. This establishes the connection between the enumeration and arbitrary bounded-time programs, including loops unrolled through the deadline.

At mixed-verdict nodes the last instruction must be a comparison. A store is relevant only if there is time for a later load and comparison. An instruction producing an already available column, a non-splitting comparison or a store which changes no memory can be deleted. When an opposite-verdict pair agrees in all current registers, an instruction reading memory is necessary before the next distinguishing comparison. At depth two this leaves only a load followed by a comparison. These observations give the smaller Python enumeration. A separate Lean computation checks the four-bit lower bound and the four XOR-image depth-four decisions. Its finite lower checks use native evaluation. The identification of executions with row-state trees is the manuscript argument above. [Sixteen-row Lean checker](../lean/CycleImageClock.lean) The four-bit and five-bit calculations were independently replayed with a second implementation; the five-bit depth-five impossibility was also replayed with the opposite-verdict shortcut disabled. [Reproducible search and upper-program checks](../audits/small_cyclic_selector_clock.py)

## What happens at the next insertion

Starting from the sixteen **original four-bit masks**, there are twenty ordered ways to choose two successive XOR insertion gaps, four at the first step and five at the second. A five-instruction program exists on **every one** of the twenty six-bit images. Thus no choice of a second gap gives another strict increase from an image whose clock was five. The audit computes all twenty independently. Thirteen images need five steps and seven need four. If instead all 32 five-bit masks are retained as the source, XOR insertion at gap zero already requires six on the new image. A six-step program on all 64 masks exists, so the complete six-bit clock stays at six. [Upper programs](../lean/SmallCycleUpperPrograms.lean)

Starting instead with **all 64** six-bit selectors, the six possible XOR insertions give exact seven-bit image clocks $(7,7,7,7,6,6)$ in gap order. Replacing XOR by OR gives $(7,7,7,7,7,6)$. At gap four the choice of algebraic operation changes the optimal clock. The complete seven-bit clock is exactly seven, as the following indirect-load program shows. The small-word C++ recurrence excludes the lower deadlines on all rows of each promise. Lean replays twelve explicit trees, charging each load and branch and checking that each operand has been loaded. Its original eight-step tree also covers all 128 seven-bit inputs. [Complete lower-bound replay](../audits/small_cycle_word_ram_census.cpp) · [Upper programs with instruction counts](../lean/SevenCycleWordPrograms.lean)

### Seven steps on every seven-bit file

At word width three let $x,y,z$ be the contents of addresses $0,1,2$, with $z\in\{0,1\}$. All other words are initially zero. A three-bit block has no two adjacent zeroes internally exactly when its value belongs to $\{2,3,5,6,7\}$. Read $x$ and branch on $x<5$. The following table gives the two continuations. Every read and comparison, including a comparison used to return a Boolean, costs one step. A terminal label is free.

| Known condition | Continuation |
| --- | --- |
| $x\ge5$ | Read $y$. If $y>4$, accept immediately for $x\ne6$, and otherwise read $z$ and accept iff $z\ne0$. If $y\le4$, reject when the three-bit *signed* value of $y$ is below $2$; otherwise read $z$ and accept iff $z\ne0$. |
| $x<5$, then $x=3$ | Read $y$. For $y=3$ read $z$ and accept iff $z\ne0$. Otherwise test $y>4$ and, only if true, test $y\ne6$. |
| $x<5$, then $x\ne3$ | Read $r=\mathrm{mem}[x]$ and $s=\mathrm{mem}[r]$. If $s>4$, accept iff $s\ne6$. Otherwise accept iff $s=3$. |

The two indirect loads are what make the last branch fit. Here $x\in\{0,1,2,4\}$. If $x=2$ and $z=1$, they return $s=y$; if $x=2$ and $z=0$, they return $s=x=2$. For $x=0$ or $4$, they return $s=0$ or $4$. For $x=1$ the second address is $y$ and the result is at most one. Thus $s\in\{3,5,7\}$ exactly in the desired case. The other rows test the two internal segments and their incident edges to $z$ directly.

Lean runs this program from empty registers on every one of the 128 masks and checks both its verdict and its seven-instruction budget. The lower bound for all programs in the original model, including every one of the 24 arithmetic operations and writes to any address, follows from the six-step exclusion on the 64 gap-zero XOR outputs: any faster full-catalog solver would decide that subfamily within six steps. An independent Lean replay now reduces that exclusion to eighteen of its inputs, as detailed below. [Seven-step native interpreter and theorem](../lean/CompleteSevenCycleClock.lean) · [Six-step lower replay](../audits/small_cycle_word_ram_census.cpp)

### Native enumeration on 18 inputs

The six covers among the 18 inputs below are 53, 85, 86, 93, 123, and 126. All 18 satisfy the gap-zero image equation, bit 1 = bit 0 XOR bit 2.

```text
22 29 35 48 53 54 62 70 77 80 83 85 86 93 115 120 123 126
```

[SevenImageDefs.lean](../upstream-checks/cycle-clock/SevenImageDefs.lean) places each seven-bit selector, low word first, into cells 0, 1, and 2 of an eight-cell RAM. All eight cells are writable, cells 3 through 7 start at zero, and each of the eight literal words is available as an operand. Each of three UInt64 bit planes holds 21 input lanes. The last three lanes repeat input 22. The checker imports all 24 word operations from CycleImageClock. It allows arbitrary extra registers and independent continuations after a guard. It identifies register and memory columns agreeing on the active branch and replaces constant columns with the corresponding literals.

The Load pruning uses a path-local witness. At remaining depth 3, suppose there is a fixed input row such that, for every choice of one current cell, some opposite-label rival agrees on that cell and the current registers. The rival may depend on the cell. At depth 4 require this for every pair of current cells. In both cases a correct continuation on that row needs at least two or three more loads, respectively. To see this, follow its path and list the addressed cells whose *old* values were read. An opposite-label row agreeing on those cells and registers has the same path, by induction. Writes preceding a read agree in address and value on the two rows, so an overwritten location reveals no additional old value. With one fewer load than required the observations still admit an opposite verdict. Apply this reasoning up to the last guard on the witness path. The remaining straight-line suffix has a fixed terminal verdict. Hence at least two or three loads, respectively, must occur *before* that last guard. If a non-load were first, at most one or two loads respectively would remain before that guard. An initial guard is covered by the same argument, since it has the same outcome on the witness and every rival agreeing on its current registers. Thus only initial loads can help in a saturated state.

On a bichromatic domain with two ticks left, the final information-bearing instruction must be a guard. A first load followed by a guard, two successive guards, and one arithmetic instruction followed by a guard cover all possibilities. A first store has no observable effect before the final guard. If opposite labels share the current register tuple then only a first load can distinguish that pair within two ticks. Operand order and either verdict assignment to each guard are allowed. Recursion caches use complete search states, while the derived caches of operation results and possible cuts depend only on their operands for this fixed word width.

[SevenImageVerify.lean](../upstream-checks/cycle-clock/SevenImageVerify.lean) proves `SevenImageSearch.exclude_six : atDepth 6 = false` using `native_decide`. The 18 gap-zero image memberships are checked by `decide +kernel`. The formal statement concerns the encoded enumerator. The preceding completeness arguments and the translation from bounded-clock arbitrary-text programs into branching trees use ordinary mathematical proofs. Each program path unwinds for six ticks, fresh registers preserve intermediate values, and every terminal verdict is constant on the rows reaching that leaf. Thus an arbitrary program correct on the entire seven-bit catalog must take at least seven ticks on some listed row. This supplies no asymptotic lower bound on ordinary SAT.

From `upstream-checks/cycle-clock`, run `lake build SevenImageVerify` under the repository's pinned Lean 4.19.0 toolchain, or `lake build` to rebuild the other finite-clock targets as well. The native check uses Lean's compiler in its trusted computation path.

[NativeClockSaturation.lean](../lean/NativeClockSaturation.lean) gives a kernel proof of the abstract load-pruning implication. In its unrolled tree model, memory addresses and values have arbitrary types and pure register updates and branch predicates are arbitrary deterministic functions. Its theorem `saturated_forces_load` proves that every correct tree of height at most k + 2 begins with a load when some witness row has an opposite-label rival after each list of at most k old-cell probes. The formal proof records only the loads preceding the last guard on the witness path. It proves this record remains valid through arbitrary intervening stores and that a non-load root requires at least two more tree levels than the number of recorded loads. The interpretation of bit-plane tests as this abstract hypothesis remains part of the manuscript argument.

[SevenImageCompact.lean](../upstream-checks/cycle-clock/SevenImageCompact.lean) independently invokes the same census on 22, 29, 35, 53, 54, 59, 62, 70, 77, 83, 85, 86, 93, 123, 124, and 126. It proves the same six-tick exclusion. Seven masks are covers, and 124 is the sole row outside the gap-zero XOR image. This smaller suite has the same label counts as the full four-bit catalog and gives a 16-point candidate image for a verdict-preserving embedding.

The role of the address calculation can also be isolated. If a program uses only direct loads and the same comparisons, eight steps are necessary and sufficient on the 128 masks. Direct loads may be adaptive and program text is unrestricted. Twenty input masks already exclude seven, while every deletion from that set admits seven in this restricted model. Lean proves the lower bound for all typed direct-load trees and checks a concrete eight-step tree. Allowing register-indirect addresses, with no stores or arithmetic instructions, reduces the optimum to seven. [Direct-load lower and upper proofs](../lean/DirectComparisonSevenCycle.lean)

### A second increase on the original sixteen files

There is a degree-three map on **all 64** six-bit selectors that preserves the cycle verdict and is injective. On the sixteen actual descendants of the first two quadratic maps it gives exactly
$$
    \{22,29,35,53,54,59,62,70,77,83,85,86,93,123,124,126\}.
$$
A six-step program cannot classify these sixteen rows even with all writable cells and all word operations. The full seven-step program classifies them. The exact worst-case clocks on the **same sixteen ancestors** are therefore $4,6,6,7$ at four, five, six and seven input bits. The three successive maps have degrees two, two and three. All are defined on their full source cubes. This cubic construction leaves the first two previously published maps unchanged. The next construction does so with a quadratic final map and characterizes what happens under repetition.

To find the last map, prescribe the allowed seven-bit outputs at the sixteen special rows and require distinct equal-verdict outputs everywhere. In the Boolean polynomial representation, degree at most three is equivalent to 22 vector-valued XOR equations: for every monomial mask of weight greater than three, the XOR of the table entries on its submasks is zero. Gaussian elimination chose 22 independent columns outside the fixed suite, all belonging to noncovers. For a proposed permutation of the special outputs and choices for the free rows, the pivot outputs follow by XOR. Keeping two free words as parameters allowed the output-label and distinctness tests to reject choices before specializing both parameters. The surviving table's coefficient at mask 7 is nonzero. Every coefficient of degree greater than three vanishes. [Full coefficient list, injectivity and verdict checks](../lean/CompleteSevenCycleClock.lean)

Lean also checks that the composed image is literally the same list given to the six-step census. This prevents a bound on a larger set from being used as a bound on its subset. The result still concerns a bounded word width and a fixed-size suite. [Composition and failed six-step census](../upstream-checks/cycle-clock/SevenImageCompact.lean)

### A quadratic replacement valid inside loops of arbitrary length

Keep **both** original maps. There is now an exact-degree-two continuation on the historical sixteen six-bit inputs. Its image is
$$
\{21,27,38,42,51,53,59,63,82,85,86,91,92,99,105,106\}.
$$
Every one of the 84 globally verdict-preserving affine maps admits six instructions on the image of this same six-bit source suite. The new quadratic image excludes six and has an explicit seven-step classifier. This proves degree two is the minimum needed on the original suite. In the subset-indexed coefficient notation of the first map, the twelve nonzero mask/coefficient pairs are
$$
(0,7),(1,29),(2,14),(3,6),(4,1),(8,3),(12,5),(16,46),(24,4),(32,96),(33,43),(48,43).
$$
Equivalently take affine map 54 in the [enumeration](../upstream-checks/cycle-clock/QuadraticOrSeparation.lean) and XOR the respective offsets $6,0,5,4,43,43$ for every uncovered old edge, in increasing cyclic order starting with edge $(0,1)$.

This very map extends to every cycle length $n\ge6$. Read six consecutive source bits as a path in physical-index order $(2,3,4,5,0,1)$ of the six-bit example, and its seven outputs in order $(2,1,0,6,5,4,3)$ of the seven-bit example. Over every one of the 64 blocks the internal edges of the first path are all covered exactly when the internal edges of the second path are all covered. When these conditions hold the ordered endpoint values agree. Therefore joining any exterior path gives the same verdict, including an empty exterior where the closing edge joins the two endpoints directly. Keeping the exterior unchanged preserves injectivity. The path order specifies the serialization for this all-length statement. The six- and seven-instruction counts refer to the original packed masks in the displayed finite suites. The construction changes a six-bit block by the same quadratic rule at every length. [Map, finite deadlines and boundary proof](../upstream-checks/cycle-clock/HistoricalQuadraticContinuation.lean)

There is an exact test of the simplest proposed induction. Repeatedly replace the leftmost six bits in this path order. If $T(s)$ is the first six output bits and $e(s)$ the seventh, a step prepends $e(s)$ to the old exterior. All 64 states satisfy $T^{21}s=T^{15}s$ and $e(T^{17}s)=e(T^{15}s)$. Applying the latter identity to later states makes the emitted sequence periodic with period dividing two after 15 steps, for every initial state. Initial path word 32 witnesses $e(T^{16}s)\ne e(T^{14}s)$, so no smaller uniform onset works. The newly added bits eventually repeat even as the file length grows without bound. This explains why iterating this particular local replacement does not propagate the measured clock increase.

### An XOR succeeds on one suite and every affine map fails to raise another

Keep the first map fixed in all three constructions. The replacement middle maps below are quadratic and preserve the verdict on the entire five-bit cube. Each row of the table gives the sorted image of the same sixteen original inputs.

| Six-bit descendants, each suite of exact clock six | Last map | Seven-bit descendants, each suite of exact clock seven |
| --- | --- | --- |
| 10, 15, 21, 26, 27, 30, 31, 33, 34, 42, 47, 50, 56, 58, 60, 62 | Insert XOR between bits 1 and 2 | 22, 27, 45, 54, 55, 58, 59, 65, 70, 86, 91, 102, 112, 118, 122, 124 |
| 15, 18, 19, 20, 23, 26, 27, 31, 39, 42, 44, 47, 50, 55, 56, 58 | Insert OR between bits 3 and 4 | 31, 50, 51, 52, 55, 58, 59, 63, 71, 90, 92, 95, 114, 119, 120, 122 |

Bits are numbered from zero. On the first suite, the exact clocks for XOR insertion in gap order are **6, 7, 6, 6, 5, 5**. Thus moving the same XOR around the same cyclic family can raise, preserve, or lower the optimal clock. A globally quadratic correction to the successful XOR gives the same rows pointwise on this suite. The Lean module includes the coefficient tables, full-domain injectivity and verdict checks, and five- and six-instruction exclusion replays on the two actual images. [First suite and its maps](../upstream-checks/cycle-clock/QuadraticFixedChain.lean)

On the second suite, *every* affine map from six to seven bits that preserves the verdict on the full cube has a six-instruction classifier on its image. There are 84 such maps by the earlier affine classification, including permutations of the old positions. Lean checks that the 84 tabulated maps are globally valid and distinct, and replays the six-instruction search on the image under each map. The OR insertion still gives an exact seven-instruction clock. Thus degree two is the minimum possible for this particular transition even when all nonsystematic affine alternatives are allowed. Combining the two quadratic maps before it with OR gives exact clocks **4, 6, 6, 7** through three genuinely quadratic maps. [Second suite and affine checks](../upstream-checks/cycle-clock/QuadraticOrSeparation.lean) · [Classification of all affine one-bit maps](affine-successors-of-cycle-cover-selectors.md)

For any fixed gap in a cycle of length $n\ge5$, the full set of preserving quadratic-or-lower insertion rules has size $2^{n+3}$. All rules in higher degrees have an explicit monomial basis after an affine change of coordinates. These classifications apply to the whole source cube at every length. They do not force a clock increase on a chosen suite. [All-degree rule classification for cycles and arbitrary edges](polynomial-rules-for-subdividing-a-vertex-cover-edge.md)

In particular the entire six-bit catalog of clock six has both an affine XOR extension and a genuinely quadratic OR extension at gap zero with image clock seven. These statements concern the 64 actual images, not just the larger ambient catalog. The same cycle predicate still has a uniform constant-work-per-word scan.

In fact every chain of systematic insertions starting with $k$ bits admits a clock of at most $3k$ on its image at every length, when the program may be chosen separately for each length. The $k$ original coordinates remain available. Hardwire their positions, load the containing word, mask the desired bit with an immediate, and branch on the result. After at most $k$ tests the original verdict is a leaf label. The same bound applies to any injective binary *linear* encoding of the $k$ bits: choose $k$ independent coordinate forms, then label the leaves by the inverse map. Neither decoder assumes a fast algorithm for SAT. Its literals and code may depend on the length and the encoding. Even an arbitrary nonlinear encoding of a fixed mixed-verdict suite of $m$ rows has a clock of at most $2(m-1)$ at any length. Choose two rows of opposite verdict, load a word at an address where they differ, and branch on equality with the word in the first row. Each child contains fewer rows. Induction gives height at most $m-1$ and two instructions per test. Thus 30 steps is an absolute upper bound for any verdict-preserving recoding of the same sixteen files, at any length. [Finite decision-tree construction](../lean/FiniteRowDecisionTree.lean)

This proves a limitation of growing just the sixteen original files. Adding independent selector choices changes the domain, as the complete five-bit catalog already demonstrates.

The full cyclic predicate itself has a uniform constant-work-per-word scan. Its strict increase is a finite RAM result. It leaves superlinear time for ordinary explicit SAT with unrestricted workspace open.

## Reproducing the finite calculations

The C++ checker also accepts a suite explicitly. These invocations should both return `feasible=false` for the OR construction.

```sh
/tmp/small-cycle 6 3 5 rows 15 18 19 20 23 26 27 31 39 42 44 47 50 55 56 58
/tmp/small-cycle 7 3 6 rows 31 50 51 52 55 58 59 63 71 90 92 95 114 119 120 122
```

Run `python3 audits/small_cyclic_selector_clock.py` for the independent register-column search. Compile the bit-parallel check with `c++ -O3 -std=c++20 audits/small_cycle_word_ram_census.cpp -o /tmp/small-cycle`. For example, `/tmp/small-cycle 7 3 6 xor 0` excludes six instructions on the 64-mask gap-zero image. For each gap and operation in the seven-bit table, supply one less than its stated clock to reproduce the corresponding lower bound. The upper programs, the cubic-map check, the direct-load comparison theorem and the finite decision-tree ceiling run as standalone Lean 4.19 files. The independent depth-five calculation on the quadratic five-bit image uses native evaluation. From the repository root run `cd upstream-checks/cycle-clock && lake build`. [Depth-five Lean theorem](../upstream-checks/cycle-clock/QuadraticVerify.lean)
