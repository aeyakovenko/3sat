# The exact SAT clocks lie below the clock of a typical predicate

The finite censuses in this journal minimise the worst-case number of executed instructions over **all** programs of the native RAM, with no bound on program size. In that model every predicate on $N$ bits in words of $w$ bits has clock at most $N+\lceil N/w\rceil$, and all but a doubly exponentially small fraction of predicates need at least $N-O(\log\log(N+2^w))$. The exact SAT clocks measured so far lie below both values: nine instructions at 16 input bits, where more than half of all predicates need at least twelve and none needs more than twenty. A sequence of exact finite clocks can therefore never show running time superlinear in the encoded length, for SAT or for any other language. This is a limit on the method. It says nothing about how fast one fixed program can decide SAT, and the linear, quadratic and cubic targets remain open.

The upper bound is the standard observation that a decision tree of unrestricted size can read its whole input. Both bounds are already in this journal in sharper asymptotic form: on the separate-operation RAM with $w=\Theta(\log n)$ the worst labelling has clock $n+\lceil n/w\rceil-\log_2 w+O(1)$, by a load-and-threshold program of the same kind and a Shannon count, and for large $n$ all but a $2^{-2^n/2}$ fraction of labellings come within a constant of it. The steering notes state the upper bound in one sentence. This note restates both bounds in the native RAM of the exact-clock notes, for every word width and with explicit constants, and compares the measured SAT clocks with them. No novelty is claimed for either bound. [Machine convention](exact-clocks-for-two-word-sat-inputs.md) · [Sharper asymptotic form](worst-labelling-clock-with-unbounded-program-text.md) · [Earlier statement](research-steering.md)

## Statements

The machine is the native RAM of the exact-clock notes with word width $w$: the input occupies the first $W\le2^w$ of the $2^w$ addressable memory words, other memory and all registers start at zero, every $w$-bit literal is an immediate operand, and a load, a store, one of the twenty word operations, or one binary comparison branch costs one executed instruction. Program text is unrestricted and terminal verdicts are free. Write $N=Ww$. The *clock* of a predicate $f$ on $\{0,1\}^N$ is the least worst-case number of executed instructions of a program deciding $f$ on all $2^N$ inputs.

**Theorem 1 (ceiling).** Every predicate on $W$ words of $w$ bits has clock at most $W(w+1)=N+W$.

**Theorem 2 (typical predicates).** Let $w\ge1$ and $1\le W\le2^w$, and let $T\ge0$ be an integer with
$$T\le N-1-\log_2\bigl(6+2\log_2(2N+2^w)\bigr).$$
Then at most a fraction $2^{-2^{T+1}}$ of the $2^{2^N}$ predicates have clock at most $T$. In particular more than half of all predicates have clock greater than the right-hand side.

**Corollary.** For every language $L$ and every length $N$ with $\lceil N/w\rceil\le2^w$, the clock of $L$ on $N$-bit inputs, with the unused bits of the last word zero, is at most $N+\lceil N/w\rceil$. The ratio of clock to encoded length is at most $1+1/w+1/N$.

## Proofs

*Theorem 1.* Load input word 0 into a register. Compare it with the literal $2^{w-1}$ by an unsigned less-than branch, then continue the binary search on the half that contains it. After $w$ branches the program position determines the word. Do the same for words $1,\ldots,W-1$. A path executes $W$ loads and $Ww$ branches and ends at a position that determines the whole input. Label that position with the value of $f$. The program has $2^N$ terminal positions; program size is unrestricted.

*Theorem 2.* Unfold a program whose paths have at most $T$ executed instructions into a tree. It labels the $2^{T+1}-1$ positions of the complete binary tree of depth $T$ by ACCEPT, REJECT, "unused", or an instruction; an instruction other than a branch uses only one child. Rename registers so that each instruction writes a fresh one. An operand is then one of at most $T$ earlier results on the path or one of $2^w$ literals (a register not yet written holds zero, which is a literal), so with $q=T+2^w$ there are at most $q+24q^2$ instructions: $q$ loads, $q^2$ stores, $20q^2$ word operations and $3q^2$ branches. For $q\ge2$ this plus three is at most $26q^2$. Each labelling decides at most one predicate. Put $\ell=6+2\log_2 q$. Since $\log_2 26<5$, the number of predicates with clock at most $T$ is at most $(26q^2)^{2^{T+1}-1}<2^{2^{T+1}(\ell-1)}$. When $T+1+\log_2\ell\le N$ this is at most $2^{2^N-2^{T+1}}$, a fraction $2^{-2^{T+1}}\le1/4$ of all predicates. The hypothesis gives $T<N$, so $q\le N+2^w\le2N+2^w$ and $\ell\le6+2\log_2(2N+2^w)$. The last sentence of the theorem takes $T$ to be the integer part of the right-hand side when that is nonnegative, and is trivial otherwise.

*Corollary.* Use $W=\lceil N/w\rceil$ words. The padding bits of the last word are fixed, so its binary search needs one branch for each of its input bits only. The program executes $W$ loads and $N$ branches.

## Where the measured SAT clocks sit

The audit builds the bit-scan program of Theorem 1 and runs it on every input in a separate interpreter of loads and unsigned less-than branches. It also evaluates the counting inequality of Theorem 2 exactly, using the integer bit length as an upper bound for the logarithm. The table uses this evaluation. The closed form in Theorem 2 gives 11, 15, 27, 250 and 1018.

| Inputs | Typical predicate needs at least | Ceiling $W(w+1)$ | Measured SAT catalog |
| --- | ---: | ---: | --- |
| four 4-bit words, $N=16$ | 12 | 20 | sign-plane catalog: exactly 9 |
| four 5-bit words, $N=20$ | 16 | 24 | packed sign-plane catalog: exactly 9 |
| eight 4-bit words, $N=32$ | 28 | 40 | |
| sixteen 16-bit words, $N=256$ | 250 | 272 | |
| sixty-four 16-bit words, $N=1024$ | 1018 | 1088 | |

"Typical" means that more than half of all predicates on those inputs need at least that many instructions. The exact nine-step clock of the 16-bit sign-plane SAT catalog is below the typical clock of a 16-bit predicate. It stays exactly nine at 20 bits, and at 21 bits in the variant whose fifth-word bit enables an unconstrained disjunct. For the negative-unit fifth word only the upper bound nine is proved. The bit-scan program decides the sign-plane catalog on all 65,536 files within 20 instructions, and likewise the 65,536 label masks of one reflected cube-cycle bank stored four bits per word. All 65,536 predicates of a single four-bit word are decided within five. [Exact nine](exact-nine-step-clock-for-four-sat-words.md) · [Twenty bits](nine-steps-at-twenty-tightly-packed-selector-bits.md) · [Fifth word](the-first-fifth-word-does-not-increase-the-nine-step-upper-bound.md) · [Cube-cycle banks](shuffled-four-cube-cycle-banks-in-ordinary-sat.md)

## What this means for exhausting small machines and lifting

**The unbounded-code clock has no blow-up to lift.** The proposal was to find the size at which a small RAM cannot decide SAT within $N$ steps and to show that the deficit survives the step to the next size. With unrestricted program text the deficit is at most $\lceil N/w\rceil$ for every problem: the clock never exceeds $N+\lceil N/w\rceil$. Deficits can appear at one size and disappear at the next, as the catalog clocks $2,5,5$ at two, four and six selector bits already showed, but the ratio to $N$ cannot grow beyond $1+1/w+1/N$. [Small catalogs](exact-clocks-for-two-word-sat-inputs.md)

**Arguments that ignore program size are capped.** Call a lower-bound argument size-oblivious if it applies to every correct program at one input length, whatever the size of its text and whatever programs are used at other lengths. The leaf-capacity recurrences, marked-tree counts and exact clocks of the nine-step notes are of this kind. By the corollary such an argument proves at most $N+\lceil N/w\rceil$ on this RAM for any language. With $w=\Theta(\log N)$ the most it can do is separate a packed scan of $N/w$ instructions from a bit scan of $N$ instructions. Both are within linear time.

**A superlinear bound has to limit the program text.** The bit-scan program has about $2^N$ instructions. A proof of superlinear time must fail for it, so it must use a hypothesis that this family violates, such as one finite program at every length or a budget on program size. Exhaustion over program size is complete in this journal only through five stored instructions of the separate-operation RAM, where by a manuscript proof no program decides DIMACS SAT at any speed. Every correct SAT solver is larger than that, and from there on the question is about its speed. [Five instructions](five-instructions-cannot-decide-dimacs-sat.md)

**Independent records do not add either.** For the sign-plane records, once a word holds several complete records a packed program checks them in parallel in $O(w+N/w)$ instructions, so as the word width grows the clock of a concatenation is not the sum of the clocks of its parts. [Packed records](which-four-word-sat-targets-finish-in-seven-steps.md)

The question on which the unbounded-code census can still give evidence is narrower: whether SAT-equivalent families have clock of order $N/w$ or of larger order when the word width grows. Theorem 2 shows that typical predicates sit near $N$. The sign-plane catalogs measured exactly so far sit well below that, at nine instructions for 16 and 20 input bits and for one 21-bit variant. No reduction from general SAT to them is claimed, and they admit a word scan at every length.

## Scope

Theorem 1 holds for every predicate, including the verdicts of 2-SAT, parity or a constant. It is a property of the cost model. Theorem 2 is a counting statement about all predicates and names no explicit hard one. Neither gives a lower bound on the running time of a fixed SAT program on ordinary encoded input. The bound $W(w+1)$ is not claimed to be attained: the asymptotic form cited above saves about $\log_2 w$ instructions by a final lookup in a word literal.

## Reproducing the checks

Run `python3 unbounded_code_ceiling_audit.py` with Python 3 and NumPy. It takes a few seconds and prints the worst executed clock of the bit-scan program on all 65,536 predicates of one four-bit word, on 2,000 seeded random predicates of two four-bit words, and on both 16-bit catalogs, followed by the certified counting floors in the table. [Audit](unbounded_code_ceiling_audit.py)
