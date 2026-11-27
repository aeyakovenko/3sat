# A repair at the next instruction can be expensive to locate from the read

I tested the step from “every conflicting write has an easy repair” to “every read has an easily searchable set of repairing writes.” **That step fails on an explicit family of proper DIMACS files.** One fixed SAT program repairs every conflict at exactly the next instruction. Yet, for every fixed decoder with \(o(M)\) bits of file-dependent advice, recovering the required repairing stores for all \(M\) reads takes at least
\[
\left(\tfrac12-o(1)\right)M^2
=\left(\tfrac12-o(1)\right)\left(\frac Nw-10\right)
\]
original-word probes on almost every file in the family. One advice bit attains the leading coefficient \(1/2\) on every file.

The charge is for recovering the stores. The SAT program itself finishes in \((10+o(1))N/w\) instructions. Its execution identifies exactly where a proposed amplification to a SAT time lower bound fails. The unrestricted linear, quadratic, and cubic questions remain open.

## What Round 7’s interval test implies

Round 7 supplies a relation \(A(c,u)\) offering stores for a read at time \(c\) with claimed value \(b\). Every offer before \(c\) must be a matching store. Every earlier same-address store of a different value must have an offer strictly between it and \(c\). Initialization at time \(-1\) counts as a conflict when \(b\ne0\). [Round 7](certifying-a-read-after-the-last-conflict.md)

If offer existence can be tested on **arbitrary** open intervals, the read has a single recoverable repair. First test whether there is an offer before \(c\). If so, binary-search the lower endpoint to find the latest offer. This takes at most \(1+\lceil\log_2(t+1)\rceil\) interval tests on a clock of \(t\) instructions. The latest offer lies after every conflict. Conversely, a circuit returning one such store or an empty marker gives a rank-zero singleton piece in Round 7. Thus allowing many offers saves at most a logarithmic number of interval evaluations over extracting one store, when arbitrary endpoints are available.

There is a weaker certificate. Give a circuit \(\rho(c,j)\) the time \(j\) of the **challenged conflict**. Require its answer \(u\) to satisfy \(j<u<c\) and to name a store of \(b\) to the read address. A defect formula guesses \(c,j\), checks that \(j\) is a conflict in the proposed history, and tests the returned \(u\). A wrong read always has a defeating challenge. Its last same-address store wrote a different value, or initialization disagreed and there was no store. Together with the ordinary CPU and input checks, chronological induction authenticates the run even when both guessed circuits are malicious.

## A genuine SAT execution with \(\rho(c,j)=j+1\)

Take \(R=B=M=2^\ell\). Arrange \(RB\) private clause words into \(R\) rows of \(B\) slots. Seven proper clauses force variables \(1,2,3\) false. Two more, \((4,1,2)\) and \((5,1,2)\), force variables \(4,5\) true. Each private word contains one of those last two clauses. In each row independently, put the clause beginning with `5` at one uniformly chosen position \(z_x\), and put the clause beginning with `4` elsewhere.

Each record, including the header, occupies one aligned ASCII word padded with spaces before its newline. The exact dimensions are
\[
D_0=RB+10,\qquad
h=\min\{a\ge1:2^a\ge32aD_0+2\},\qquad
w=32h,\qquad N=wD_0.
\]
Minimality gives \(h=\lceil\log_2(N+2)\rceil\). The header and every clause fit in \(4h\) bytes. All files are satisfiable. Replacing any private word by the same-width clause \((3,1,2)\) makes the file unsatisfiable. Every correct solver on this aligned RAM must therefore load all \(RB\) original private words before overwriting them.

Use separate input and work memory, with work address 1 for the reads and address 0 as a dummy. The program’s first instruction stores one at address 1. It checks the public layout and uses a complete solver on a failed check. For each row it executes the following sweep.

| Part | Executed instructions |
|---|---:|
| Store one at address 1 and clear the slot counter | 2 |
| Load the private word, compare against both legal words, OR the comparison bits, and branch on invalid syntax | 5 per slot |
| Store zero and then one at the address given by the `5` comparison bit | 2 per slot |
| Advance the input pointer and slot counter, then test the loop bound | 3 per slot |
| Load address 1, check its value, advance the row counter, and test the row bound | 4 |

The sweep takes **exactly \(R(10B+6)\) instructions** on every planted file. A fixed program can derive the square dimensions from the public length and width and construct the ten expected public words in \(\operatorname{polylog}N\) steps. Successful validation proves SAT for any arrangement of the two legal private words.

Every work read returns one. Every explicit conflict is immediately followed by a store of one to the same address. The initialization conflict is repaired at instruction zero. Hence the single rule \(\rho(c,j)=j+1\) works throughout.

Let \(r\) be the start of a row. Its read occurs at \(c=r+2+10B\). The unique conflicting store in that row occurs at \(r+7+10z_x\). **The only matching store between that conflict and the read is \(r+8+10z_x\).** Every passing Round 7 relation must offer it. For every candidate slot \(y\), the interval
\[
(r+7+10y,\ c)
\]
therefore contains an offer exactly when \(z_x\ge y\). Earlier optional offers cannot change the answer. This is where arbitrary interval queries acquire information that checking \(j+1\) never needs.

## The cost of recovering the stores

Give a deterministic decoder unrestricted computation, adaptive probes anywhere in the original file, shared scratch across all rows, and \(D\) bits of file-dependent advice. Let \(Q\) be its total number of distinct private words probed while recovering all \(R\) positions. Fix the decoder before drawing the file.

For a fixed advice string, append probes of the decoder’s predicted positions, then complete the probe order in any deterministic fashion. Cache repeated probes. Let \(U_x\) count the distinct misses in row \(x\) before its mark is first found. The \(U_x\) are independent uniforms on \(\{0,\ldots,B-1\}\), even when probes to different rows are interleaved adaptively. To see this, prescribe one rank per row, answer “unmarked” until that row reaches its prescribed rank, and then answer “marked.” Completing the order gives a bijection between rank vectors and physical mark placements.

On a successful decoding, every appended prediction is correct. All misses before discovery therefore occurred within the original \(Q\) probes. Taking a union over advice strings gives the finite bound
\[
\Pr[\text{some advice recovers all positions within }Q]
\le \frac{2^D}{B^R}
\#\left\{u\in\{0,\ldots,B-1\}^R:\sum_xu_x\le Q\right\}.
\]
At \(Q\le(1/2-\eta)R(B-1)\), this is at most \(2^D e^{-2\eta^2R}\). Taking \(D=o(R)\) and \(\eta\to0\) with \(\eta^2R\gg D+1\) proves the claimed half-scan lower bound. The concentration inequality is classical. [Hoeffding, Theorem 2](https://www.cs.rpi.edu/academics/courses/spring06/random/hoefding.pdf)

For the matching upper bound, one advice bit chooses forward or reverse order for all rows. Stop each row on its mark or infer the sole remaining position. For each row the two directional costs sum to at most \(B+1\). The cheaper common direction costs at most \(\lfloor R(B+1)/2\rfloor\) original loads on **every** placement. This matches the probe coefficient. Native address arithmetic and loop instructions still contribute to elapsed time.

There is also a useful small-budget check. A successful fixed-advice probe transcript, padded to \(Q\) bits, has at most \(R\) marked replies and determines its output. Covering all placements requires
\[
2^D\sum_{i=0}^{\min(R,Q)}\binom Qi\ \ge\ B^R.
\]
At \(R=B=256\) and \(Q=3R\), exact integer arithmetic gives **\(D\ge1{,}347\) bits**. Storing the high six position bits per row uses 1,536 bits and leaves at most three probes per row. The actual serialized file at this scale occupied **54,534,272 bits**, with \(w=832\), and the interpreter executed **656,896 sweep instructions**.

## Consequence for the proposed amplification

Write \(t=\Theta(M^2)\) for the native clock. Suppose a Round 7 description had charge \(t^\gamma\) for fixed \(\gamma<1/2\). Its encoding would take \(t^\gamma\operatorname{polylog}t=o(M)\) advice bits. Even granting the evaluator direct probes to the physical input, its interval algorithm followed by binary search would use at most \(t^\gamma\operatorname{polylog}t=o(M)\) probes per row. The half-scan theorem excludes this combination on almost every planted file. Hardwiring the \(M\) marked positions supplies a singleton description of size \(M\operatorname{polylog}t\), so the square-root exponent is sharp up to logarithms here.

The separation concerns the **repair information given access to the chronological events**. On these files the true controller at a specified sweep time needs at most two neighboring private-word probes to obtain current or still-live register values. If the entire controller must instead be hardwired, its destination bits already distinguish all \(M^M\) placements. Also, every mark passes through a register during the solver’s compulsory input scan. Adding the recovery lower bound to that scan would charge the same observations twice.

For the journal’s fixed unary hierarchy source with \(t=Cn^2\), the conflict-dependent verifier still gives a precise target. If all sufficiently large positive inputs had a controller and response circuit of total size \(t^\gamma\), the locally available unary input would allow one physical defect formula of \(t^\gamma\operatorname{polylog}t\) bits. An \(O(N^k)\) SAT solver would verify the guessed accepting run in \(O(n+t^{k\gamma}\operatorname{polylog}t)=o(t)\) for \(\gamma<1/k\). Establishing those circuits on that source remains open. The planted files here have independent physical data. Their contribution is an unconditional counterexample to converting easy conflict responses into cheap read-indexed interval search on arbitrary fast SAT executions. [Unary source and native hierarchy argument](a-fixed-unary-ram-source-for-physical-sat-compilers.md)

## Executable checks

Run `OPENBLAS_NUM_THREADS=1 python3 -B next_instruction_repair_audit.py`. [Round 8 audit](../audits/next_instruction_repair_audit.py)

- The small native sweeps covered 344 positive files, 1,384 actual row reads, and 12,320 interval tests. Assignment enumeration confirmed all 1,060 tested single-word negative edits. The 256-square file was serialized and executed separately.
- All 156,250 tested combinations of short histories, claimed replies, and challenge maps obeyed the soundness criterion. Z3 independently decided 500 serialized proper DIMACS defect queries, finding 303 satisfiable and 197 unsatisfiable.
- Composing the actual Round 7 quadratic interval circuits recovered the latest offer or the empty marker in all 5,120 tests across 288 maps. Exact adaptive decision-tree optimization agreed with both counting bounds at 345 finite parameter settings.
- The 16-bit census illustrates the layout dependence. On its 256 files with four one-hot nibbles, the original truth table gives 144 positives. There one four-bit load reveals a whole row’s marked position. The probe proof above uses one candidate slot per physical word. [Four-word native census](exact-nine-step-clock-for-four-sat-words.md)
