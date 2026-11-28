# A one-bit extension raises the clock from four to five with XOR and to six with a quadratic map

Pack a cyclic selector mask low bit first into words of width $w=\lceil\log_2 L\rceil$ at physical selector length $L$. The catalog is SAT if some adjacent bits are both zero, including the wraparound. A *cover* is the opposite verdict. Each result below concerns the minimum, over all programs correct on the indicated domain, of their worst-case number of executed instructions. The native instruction set has separate loads, stores, 24 binary numerical operations, and two-operand comparisons with fixed successor labels. Scratch is initially zero and every address representable by the word is writable. Programs may use arbitrary text, register destinations, dynamic addresses and embedded word literals. The fixed cyclic clause template realizes these verdicts as satisfiability. The measured input length counts the selectors. [Catalog, physical encoding and opcodes](a-shared-nine-step-obstruction-and-the-next-native-width.md)

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

Starting instead with **all 64** six-bit selectors, the six possible XOR insertions give exact seven-bit image clocks $(7,7,7,7,6,6)$ in gap order. Replacing XOR by OR gives $(7,7,7,7,7,6)$. At gap four the choice of algebraic operation changes the optimal clock. The complete seven-bit clock lies between seven and eight. The small-word C++ recurrence excludes the lower deadlines on all rows of each promise. Lean replays twelve explicit trees, charging each load and branch and checking that each operand has been loaded. Its additional eight-step tree covers all 128 seven-bit inputs. [Complete lower-bound replay](../audits/small_cycle_word_ram_census.cpp) · [Upper programs with instruction counts](../lean/SevenCycleWordPrograms.lean)

In fact every chain of systematic insertions starting with $k$ bits admits a clock of at most $3k$ on its image at every length, when the program may be chosen separately for each length. The $k$ original coordinates remain available. Hardwire their positions, load the containing word, mask the desired bit with an immediate, and branch on the result. After at most $k$ tests the original verdict is a leaf label. The same bound applies to any injective binary *linear* encoding of the $k$ bits: choose $k$ independent coordinate forms, then label the leaves by the inverse map. Neither decoder assumes a fast algorithm for SAT. Its literals and code may depend on the length and the encoding. Even an arbitrary nonlinear encoding of a fixed mixed-verdict suite of $m$ rows has a clock of at most $2(m-1)$ at any length. Choose two rows of opposite verdict, load a word at an address where they differ, and branch on equality with the word in the first row. Each child contains fewer rows. Induction gives height at most $m-1$ and two instructions per test. Thus 30 steps is an absolute upper bound for any verdict-preserving recoding of the same sixteen files, at any length. [Finite decision-tree construction](../lean/FiniteRowDecisionTree.lean)

This proves a limitation of growing just the sixteen original files. Adding independent selector choices changes the domain, as the complete five-bit catalog already demonstrates.

The full cyclic predicate itself has a uniform constant-work-per-word scan. Its strict increase is a finite RAM result. It leaves superlinear time for ordinary explicit SAT with unrestricted workspace open.

## Reproducing the finite calculations

Run `python3 audits/small_cyclic_selector_clock.py` for the independent register-column search. Compile the bit-parallel check with `c++ -O3 -std=c++20 audits/small_cycle_word_ram_census.cpp -o /tmp/small-cycle`. For example, `/tmp/small-cycle 7 3 6 xor 0` excludes six instructions on the 64-mask gap-zero image. For each gap and operation in the seven-bit table, supply one less than its stated clock to reproduce the corresponding lower bound. The upper programs, the sixteen-row depth-four check, the second map and the finite decision-tree ceiling run as standalone Lean 4.19 files. The independent depth-five calculation on the quadratic five-bit image uses native evaluation. From the repository root run `cd upstream-checks/cycle-clock && lake build`. [Depth-five Lean theorem](../upstream-checks/cycle-clock/QuadraticVerify.lean)
