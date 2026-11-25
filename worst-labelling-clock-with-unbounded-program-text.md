# How much can exhaustive testing at a fixed input length force?

Fix the separate-operation RAM with binary branches to fixed targets, a fixed finite set of at-most-binary word operations, a fixed entry point and two terminal verdicts. Register initialization is zero except for the optional public length and width; memory initially contains the packed input and zero elsewhere. LOAD and STORE are separate, and executing one instruction takes one step. The program text and number of registers are unrestricted. Fixed control labels may range over the whole finite text even if there are more labels than word values; the address bound applies to data memory. A stored-program model requiring the entire text to fit in word-addressed memory has an extra resource bound. Word addresses must suffice for the input. Let $w=\Theta(\log n)$ and $m=\lceil n/w\rceil$. Choose the program **after** fixing $n$ and the entire truth table on the $2^n$ binary inputs. Define
$$
 D(n,w)=\max_f\min_{P\text{ computes }f\text{ at length }n}\ \max_{x\in\{0,1\}^n} T_P(x).
$$

**Theorem.** At all sufficiently large $n$,
$$
 D(n,w)=n+\lceil n/w\rceil-\log_2 w+O(1).
$$
Rounding the logarithm changes the additive constant only. The lower bound is for some Boolean labelling of all packed strings. The upper bound applies to every labelling, including the restriction of SAT to any finite length. The constant in the displayed estimate may depend on the fixed ISA and logarithmic word-width convention.

**Consequence for the proposed SAT exhaustion.** With the public input length, for every finite horizon $N$ there is one globally correct SAT program taking at most
$$
 7n/8+O\big(\lceil n/w\rceil+\log(n+2)\big)
$$
steps on every well-formed ASCII formula of byte-aligned length $n\le N$. The constants in the time bound are independent of $N$. Hence **even exhausting every formula through $N$ cannot refute a deadline of one step per encoded bit at all sufficiently large tested lengths if arbitrary program text is permitted**. A proof along the exhaustion route must use consistency or a description-size bound on the same solver across growing lengths. The program below may have exponentially many instructions; it provides no fast uniform algorithm as $N$ grows. [Related polynomial-size finite suites with charged description length](code-bits-needed-to-fit-a-finite-sat-suite.md) · [Uniform exhaustion criterion](bounded-ram-programs-and-separate-sat-witnesses.md)

## Two descriptions of each reachable control prefix

Fix a candidate program. At height $j$ of its computation tree, unfold its actually reached instruction locations by control history, preserving which binary successor was taken. A node is a control prefix; many register or memory states can follow it. For the counting argument, use prefixes of exactly $j$ executed instructions and include a terminal as a possible endpoint. On such a prefix let $l$ count the LOADs. The union of the prefixes with exactly $l$ loads has at most
$$
          \min\{2^{wl},\ 2^{j-l+1}\}
$$
members. To see the first bound, supply all $l$ words returned by those LOADs to the fixed program. This determines the entire control history through $j$, even if some of the purported replies would be inconsistent with the stores. For the second, supply the outcomes of all its branches. There are at most $j-l$ of these because a LOAD does not branch. At most $2^{j-l+1}-1$ binary strings have this many or fewer bits. Neither description charges the number of labels in the original program text. Supplying different branch histories can distinguish two identical target locations; this can only increase the unfolded count.

Put $a=j/(w+1)$. For $l\le\lfloor a\rfloor$ sum the $2^{wl}$ bound; this geometric series is at most $2\,2^{wa}$. For $l>\lfloor a\rfloor$ sum $2^{j-l+1}$; this part is at most $4\,2^{j-a}=4\,2^{wa}$. Summing over all $j\le T$ gives at most $C_0 2^{Tw/(w+1)}$ nodes before a deadline $T$, including leaves. The geometric ratio in the last sum is at least $\sqrt2$. The constants are absolute. Importantly, the product of the word alphabet and the number of branches at *every* time step would give a much weaker bound.

Encode just this reachable finite tree. At each node write the opcode and occupancy of its at most two child positions, in a fixed traversal. For each source operand, give an immediate word, its designated initial value, or the depth of the most recent ancestor writing that register. A register value can consequently be recovered as the result of the specified ancestor on the actual replay path. There is no need to transmit the register's original unbounded textual name: save each instruction result under its depth on the current path. The two possible continuations are already the child positions; a large fixed jump target in the original code carries no additional data into a register. During replay all indirect stores and loads operate on the actual simulated RAM and the given input. On genuine inputs the occupied children are exactly sufficient, and an unused child can default to any verdict. The two terminal labels and self-delimiting tree structure cost only a constant per node. Thus for some ISA constant $C$, the number of distinct length-$n$ truth tables decidable by $T$ is at most
$$
          2^{C(w+\log_2(T+2))2^{Tw/(w+1)}} .
$$
This step requires that a program cannot read its PC or arbitrary code words as initial data. If $T>2n$ the desired lower bound already holds. Otherwise $w+\log_2(T+2)=O(w)$. To realize all $2^{2^n}$ functions one needs $Tw/(w+1)\ge n-\log_2 w-O(1)$, giving the stated minimax lower bound. The construction is a Shannon-style count of finite descriptions; no circuit-size lower bound for SAT is used. [Shannon, *The Synthesis of Two-Terminal Switching Circuits*](https://doi.org/10.1002/j.1538-7305.1949.tb03624.x)

## A program that attains the upper bound

Read each word once by a direct LOAD. Decode each of its unknown bits using one threshold branch per bit; the thresholds are literals in a binary tree of distinct instruction locations, so the current control path already determines the decoded prefix. For a partially filled word use only its actual input bits and known zero padding. Process such a word before the last full word. This avoids losing the following saving when only one bit occupies the physical tail.

Set $k=\lfloor\log_2 w\rfloor$. At the last full word, decode only the high $w-k$ bits. At this point the possible results on its $k$ low bits fit in one word literal of $2^k$ data bits. Mask off the high part of the last input word, shift the appropriate literal by the resulting low index, mask the output bit and branch to its verdict. All shift counts are below $w$. This gives $m$ loads, $n-k$ threshold branches and a bounded number of final operations. Arbitrary control text at one length suffices to supply all the different literals.

## ASCII and one program for a whole finite horizon

A full packed word of $W=w/8$ seven-bit ASCII bytes has at most $2^{7W}$ possible values; the final partially filled word uses seven bits per actual byte. A binary decision tree of unsigned comparisons with word immediates distinguishes these legal values in at most seven branches per byte, by splitting the sorted list in half at each node. One additional equality branch per word can detect a value outside this list and send it to a general fallback. If the ISA supplies only signed comparisons, sort and split in signed order instead. After classifying all words, the terminal label is the answer on the entire file, hardwired for that finite length. Building this tree is a finite computation even for arbitrary decidable syntax. Its size is not charged in this theorem.

Dispatch on public length in $O(\log(n+2))$ comparisons, uniformly through any finite $N$. Test increasing thresholds $2^j-1$, ending at $N$ if it falls earlier than the next threshold. Once the first enclosing interval is found, a balanced tree resolves its exact length. The first threshold enclosing $n$ is representable in the actual word: its exponent is at most $w$ when the length register can hold $n$. All thresholds within the selected interval used to refine it fit as well. A length above the horizon goes to an ordinary total SAT decider. For non-ASCII strings a fallback can implement the selected syntax convention. This yields the stated finite-horizon bound. In particular its coefficient is below one on the ASCII promise even without using the smaller actual DIMACS alphabet. Extending the finite horizon changes the code. A uniform exclusion of $O(n)$ has quantifiers $\forall P\,\forall C\,\forall N_0\,\exists x$, with $P$ fixed before the hard input is chosen.

The separate [sparse-edit theorem](exact-executed-clocks-for-sparse-word-edits.md) determines an exact executed-step optimum on SAT promises when every candidate program faces one common satisfiable base. Its parameter is the number of words edited, while the unrestricted-labelling count here concerns a dense family of all $n$-bit strings. Historical priority of the minimax expression in this particular RAM instruction convention is unestablished.

The [Lean calculation](ExecutedPrefixCount.lean) bounds the sum of the two prefix counts through height $T$ by $16\cdot2^{T-\lfloor T/(w+1)\rfloor}$. The [finite upper-bound audit](finite_labelling_clock_audit.py) executes 1,467 generated word programs on 24,184 input/program pairs, checks every label and exact instruction count, and covers both full and partial final words. The normalization of RAM execution trees and the full minimax conclusion are manuscript arguments.
