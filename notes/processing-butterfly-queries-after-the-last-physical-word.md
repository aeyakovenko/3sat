# Processing butterfly queries after the last physical SAT word

**Result.** On the journal’s aligned, separate-operation RAM with one writable data memory, aligned full-word loads and $w=1024\lceil\log_2(N+2)\rceil$ bits per word, there are proper DIMACS files on which a near-linear-time SAT solver must execute
\[
\Omega\!\left(\frac{\log N}{\log\log N}\right)
\]
instructions **after it has read every physical input word**, even when every subsequent `LOAD`, including a data-dependent pointer chase, receives zero charge. The bound holds on both members of a SAT/UNSAT pair differing in one bit. It allows unrestricted workspace.

The charge counts stores and arithmetic or comparison instructions that consume a load result. The proof uses the native semantics of `LOAD` and `STORE` to simulate a suffix with few such instructions. The same family has a globally correct solver taking \(O(N)\) time on its members, and a different program gets a constant elapsed suffix with modestly more preprocessing. The unrestricted linear, quadratic and cubic SAT questions remain open.

## Falsification on the sign-plane catalogs

On the four-selector-bit catalog, **two is the exact optimum worst-case elapsed time after the second original word has been loaded**, allowing unlimited preprocessing before that load. Whichever of \(P,M\) the program first inspects, give it value 1. As the other word \(x\) ranges over \(0,1,2,3\), the verdicts are YES, NO, YES, NO. All earlier registers and scratch are fixed when \(x\) arrives.

A single binary comparison can separate at most one of the pairs \((0,1)\) and \((2,3)\). This holds for equality and for thresholds in both signed and unsigned order. Comparing \(x\) with itself gives a constant. Thus some one-bit opposite pair needs a second instruction on **both** runs. A data instruction as the first suffix step also leaves a comparison necessary. The matching program reads \(M\), rejects 3, reads \(P\), computes \(P\mathbin{\&}M\), and tests zero. Its total worst-case clock is five. [Catalog and instruction conventions](exact-clocks-for-two-word-sat-inputs.md)

The exact two-step tail survives at **sixteen selector bits**. Use base `1122` in \(P_0,P_1,M_0,M_1\) order. Every word is essential there. If a positive word is last, vary it over \(0,2,4,6\). If a negative word is last, vary it over \(0,1,2,3\). In either case the labels alternate and the two disjoint pairs each differ in one bit. The same comparison proof applies. I replayed the journal’s nine-step upper program on all 65,536 files against assignment enumeration. It accepted 6,560, read all four words on 20,720, and spent exactly two more instructions on every such run. The independent census subsequently found a seven-step accepting path for base `4488` and checked it against the entire catalog. [Nine-step program](seven-tests-for-six-native-steps.md) · [Census checkpoint](https://github.com/aeyakovenko/3sat/blob/ram-campaign-20261127/campaign-progress.md)

These tests expose the obstacle to induction. A solver can do almost all its work before its last load. On a layout with a known padding word it can even simulate the decision using the expected padding, then load that word and check it before returning. The construction below puts a possible query in **every** physical word, including the header word.

## Which instructions have to execute

Start immediately after delivery of the last new word. Treat the cut registers and that reply as known. Mark every register definition produced by a subsequent `LOAD`. A register copy carries its source mark, and an arithmetic result starts unmarked. Count one instruction for each `STORE`, and one for each noncopy numerical instruction or comparison branch with a marked operand. Call the count \(r\). Pointer-following loads, copies, and loop arithmetic on unmarked counters can all run for free in this accounting.

**Simulation lemma.** If the cut memory has \(S\) nonzero cells, a static index of \(O_P((S+1)\log(S+2))\) words can replay a suffix of a fixed program \(P\) with \(O_P(r+1)\) cell probes. Local computation in the replay is free. The native machine has a fixed finite controller, explicit register operands, and fixed terminal verdicts.

Write \(f(a)\) for the word at address \(a\) at the cut, setting the undisclosed query cell to zero and installing its actual reply as an initial correction. The support of \(f\), its image, and zero give at most \(2S+1\) relevant vertices. Every outside address points to zero. The functional graph consists of cycles with rooted trees feeding them.

Give each vertex its tree depth, DFS interval, cycle identifier, cycle entry and position. From the labels of \(u,v\) alone one can test \(f^j(u)=v\). Before reaching the cycle, test ancestry and depth difference. On the cycle, test position modulo its length. Retrieving the *value* \(f^j(u)\) takes \(O(1)\) probes using a level-ancestor index and an array per cycle. A static sparse dictionary locates the labels, including the default case. [Bender and Farach-Colton, Theorem 8](https://www3.cs.stonybrook.edu/~bender/newpub/2004-level.pdf) · [Fredman, Komlós and Szemerédi](https://www.cs.princeton.edu/courses/archive/fall09/cos521/Handouts/storingasparse.pdf)

Keep the constant-size program controller and the last slot address in the index as well. The main issue is an intervening store. Keep a deferred register as a known origin followed by the **times** of its dependent loads. At each store, resolve its address and payload and fetch their labels once. To resolve a deferred register later, walk its recorded load times locally. If its current symbolic address is \(f^j(u)\), the label test finds the latest matching store preceding that particular load. A match resets the origin to the stored payload. A miss increments \(j\). This uses the labels already fetched for the stores, however many times the walk hits them. Only the starting label and final orbit value need additional probes. Each charged instruction resolves at most two operands.

Keeping the load times is necessary. With old memory \(0\mapsto1\mapsto2\), load through 0, store \(M[0]\gets0\), then load through the retained result. The answer is 2. Evaluating both loads against the newest memory gives 0. The lemma uses one address-to-word map throughout. On machines with separate input and work banks, the same proof also charges a dependent load that switches banks.

## Making the last word the solver’s choice

Take a degree-\(B\), depth-\(d\) butterfly, with \(U=B^d\) vertices per layer, \(V=dU\) nonsinks and \(E=BV\) edges. Give vertex \(j\) two state variables with decimal identifiers \(4+2j\) and \(5+2j\). For a potential edge \(u\to v\) with presence bit \(p\), its packet asserts
\[
u_0\Rightarrow v_{1-p},\qquad u_1\Rightarrow v_1.
\]
A query packet asserts \(s_0\) and \(\neg t_b\). On the unique underlying path from \(s\) to \(t\), state 1 records that an edge was missing. Exactly one sink state is reachable. Setting precisely the reachable states true proves that the file is SAT iff the reachability bit equals \(b\). Switching \(b\) changes one ASCII bit because the two identifiers are consecutive with an even last digit first.

Seven fixed proper clauses force anchors 1, 2 and 3 false. Use them to pad implications and units to three distinct variables. Include a satisfied row \((z,-1,2)\) for every state name \(z\), distributing the two rows for vertex \(j\) into physical slot \(j\). There are \((d+1)U\le E\) vertices. Put the header and anchor clauses in slot zero. **Every one of the \(E+1\) slots also contains one movable packet.**

The encoded bit length is exactly
\[
N=1024\ell(E+1),\qquad w=1024\ell,\qquad
\ell=\min\{j\ge1:2^j\ge1024j(E+1)+2\}.
\]
Minimality gives \(\ell=\lceil\log_2(N+2)\rceil\). Each native word has two halves of \(64\ell\) bytes. The public text and first packet clause fit in the first half, the second clause in the other, with whitespace before each final newline. Even in slot zero the first half uses at most \(109+11\ell\) bytes before padding. There is no partial word or public-only trailing word. The coefficient 1024 is a sufficient fixed choice for this ASCII layout. The claim concerns aligned whole-word loads.

For a fixed graph, install the next edge packet whenever the solver first requests a new slot, until one slot remains. Before that last request it cannot halt. It also cannot overwrite an unread slot: place opposite query tags there and complete all the other slots identically, and the write would erase the sole difference before inspection. Freeze the prefix at the last load address. Every query completion now replays that prefix on an ordinary file supplied in full at entry. This adapts the journal’s last-*data*-word argument to the last physical word. [Earlier butterfly construction](work-after-the-last-unseen-sat-word.md)

Fix a prefix budget \(C N\log^K N\) for constants \(C>0,K\ge0\). Either some shared prefix already exceeds it, or all the resulting static indices use \(S'=O_P(N\,\mathrm{polylog}\,N)\) cells. Interleave the two terminating tag simulations one static cell probe at a time. Between probes each simulator runs its free local calculation until its next request or halt. The first halt gives the reachability bit, so the query takes \(O_P(1+\min(r_0,r_1))\) probes. This minimum is what forces the charge on both files.

Set \(B=2^{\lceil4\log_2(d+2)\rceil}\). Pătraşcu’s butterfly bound gives either
\[
(q/d)\log_2(S'd/V)=\Omega(\log B)
\quad\text{or}\quad
(q/d)O(w)=\Omega(\sqrt B).
\]
Here \(\log(S'd/V)=O_K(\log B)\), \(w=\Theta(d\log d)\), and \(\sqrt B\ge(d+2)^2\). Thus \(q=\Omega(d)\) and \(d=\Theta(\log N/\log\log N)\). On the resulting pair each actual clock includes at least \(N/w\) original loads **plus** \(\Omega(d)\) charged suffix instructions. The butterfly theorem supplies the static lower bound. The time-stamped simulation is the step that ties it to particular executed instructions. Counting cycles in a semantic graph certificate would supply no such step. [Pătraşcu, §5](https://arxiv.org/pdf/1010.3783)

## Where the elapsed-time argument stops

A globally correct program can validate the canonical slots in a forward scan, build an edge array, and follow the selected path in \(O(d)\) instructions. Before the last word, either it knows the query and the one missing edge key, or it has every edge. In the first case it computes the verdict for both possible last packets in advance. In the second, the scanning program knows the one remaining physical slot and its public text. Before the last read, enumerate its $O(U)$ possible first query halves and $O(U)$ possible second query halves separately. Store the decoded endpoint and tag with a presence flag using the literal half-word as the low address bits of two disjoint, initially zero work banks. Each key has only $w/2$ bits, so the bank tags fit in the native address space. Choosing high bank tags avoids the original physical file. Only $O(U)$ entries are written; there is no array-initialization pass over the sparse address universe. Generating the prescribed bytes and packing each half costs $O(\log N)$ steps, for a total of $O(N)$ over this table. On receipt, two actual RAM reads both validate and decode the two query halves in constant time. Invalid layouts transfer to a general SAT solver. The scan, including validation and dictionary construction, takes \(O(N)\) time on this family. This attains the post-load order of growth.

There is also a concrete escape at the stronger deadlines. For fixed \(h\ge1\), split the path into \(h\) consecutive pieces. For a piece of length \(a\), tabulate its answer for each starting vertex and each of the \(B^a\) possible destination-digit strings. The source and sink determine all \(h\) lookup keys directly. Construction by walking each listed piece takes
\[
O_h\!\left(N+dU B^{\lceil d/h\rceil}\right)
 = O_h(N+E U^{1/h})
 = O_h(N^{1+1/h}).
\]
The elapsed suffix is then \(O_h(1)\), including final-word validation. Thus even a hypothesis allowing \(O(N^{1+\epsilon})\) time on these files suffices for a constant suffix, for each fixed \(\epsilon>0\). The obstruction is reuse of the precomputed path pieces. The proof charges one suffix on one pair and supplies no sum of such charges on a single run.

**Checks.** The local audit compared deferred and direct execution on 786,432 two-store histories over every four-word memory map, 2,000 longer sparse histories, and 256 native instruction traces with data-dependent stores and branches. It checked both verdicts by generic DPLL on 384 physical one-bit pairs, including runs with the header word last, and replayed 34,944 tagged segment-table queries. A further bound charges the distinct words used by unmarked stores and has matching one-address and one-payload counterexamples. [Sharper store accounting and its limits](one-overwritten-address-after-the-last-sat-word.md)

The asymptotic simulation and reduction are manuscript arguments. Priority for their combination is unverified. Reproduce from the clone with `python3 -B last_physical_word_pointer_audit.py`. [Audit code](../audits/last_physical_word_pointer_audit.py)
