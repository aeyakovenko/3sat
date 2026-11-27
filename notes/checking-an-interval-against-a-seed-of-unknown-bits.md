# Checking an interval against a seed of unknown bits, and the memory a seed cannot shorten

**The construction in this note is correct, and it gives no elapsed-time bound for SAT.** A block of RAM instructions can be checked against a description of its entry memory as polynomials of degree at most \(d\) in arbitrarily many unknown bits. A failed check always has a witness that sets at most \(d(q+1)+a\) of those bits, where \(q\) counts the entry bits the block reads and \(a\) counts the unknown bits read by the bookkeeping that accompanies it. The bound is attained for every \(d\ge1\), \(q\), \(a\) by a machine block, and for every \(d,q,a\) at a fixed leaf. It holds with indirect loads and stores.

The description does not shorten memory that the rest of the run verifies. On the \(m!\) permutation files of an explicit family of proper DIMACS files of \(N=\Theta(m\log m)\) bits, one correct SAT program, modelled at loop level and using \(O(N)\) word operations on the family, holds a table of at least \(m/2\) words through \(m/2\) consecutive loop iterations, and every sound description of this kind must reproduce those words exactly, whatever its degree and however many unknown bits it uses. The interrupted session's earlier family does the same on rejecting runs. A second program decides the files of the main family, also in \(O(N)\) time, and on a satisfiable file one satisfying assignment describes its whole run. The cost belongs to the first program. All three standard tests come out against a time consequence. The alternation speedup stops at a statement the journal already lists as missing. The unrestricted \(O(N)\), \(O(N^2)\) and \(O(N^3)\) questions remain open.

## What was recovered

An earlier session of this project was interrupted after its audit script ran and before it wrote a note. Its log has two messages from that session and no reasoning between commands. The second message says that an interval whose entry memory depends on arbitrarily many unknown bits can be checked, that a failed check needs only a sparse setting of those bits even with indirect reads and writes, and that the session would test the exact sparsity bound and whether a fast SAT execution must admit such descriptions. **The definitions, statements and proofs below are my reconstruction from the script.** The script's first version used a different family, with \(4m+7\) clauses, satisfiable exactly when some name is missing from the image of a map. The final version replaced it by the \(2m+7\)-clause family of Section 3. I rebuilt the first family from the log and use it in Section 3 for rejecting runs.

Four ingredients are already in the journal, and I opened each of them.

- The sparse witness is the generator-form counterpart of the journal's sparse-state lemma. That lemma bounds the weight of a counterexample *state* against polynomial *equations* on the state. Here unknown bits parametrize the memory, and a read costs the degree of what it reads. Both use the same low-weight fact. [Sparse-state induction](sparse-state-induction.md)
- Untransmitted unknowns already occur in two formats. Shared-label rows make each cell a bijective image of one unknown word per class of cells. The relational entry uses a hidden tag constrained by affine equations. A seed row lets one cell depend on several unknown bits through a polynomial, and it needs a routine to carry the unknowns across a block. [Shared labels](cumulative-verdict-products.md) · [Hidden tags](relational-memory-induction.md)
- The advice count of Corollary 6 is the count of two earlier entries: the same targets, verifying lookup and union over fewer than \(2^{s+1}\) strings. The product-row entry also has the forcing step, that a verified word needs a singleton domain; Theorem 3(i) is that step for seed rows. New here are the weight bound of Theorem 3(ii), which turns a seed row into a decoder, explicit constants, and files whose verdict depends on the permutation. [Inverse snapshot frontier](inverse-snapshot-frontier.md) · [Product rows](cumulative-verdict-products.md)
- The conditional transfer in Section 5 is the journal's recurrence. I did not re-derive it. [Signed windows](signed-snapshot-windows.md)

My greps of the journal for rows that parametrize memory by polynomials in a seed found none. I take the exact bound with equality, the weight bound of Theorem 3(ii), and the files whose verdict depends on the permutation data to be this note's content. Priority outside the journal is unverified. I opened no external paper for this note.

## 1. Seed rows and the exact sparse check

**Setting.** Fix a deterministic machine and an input. A configuration is a bit vector indexed by a set \(C\) of coordinates: every bit of the program counter and registers, and every bit of every writable memory word. A block is the map from the configuration at one instruction time to the configuration at a later one. I use one property of the machine. A block reads bits of its entry configuration, each address and each branch depends only on bits already read, and each store writes a value determined by bits already read. Input reads return fixed constants. This covers the journal's logarithmic-word RAM with indirect addressing and unrestricted workspace.

A **seed row** of degree \(d\) on \(n\) seed bits gives each coordinate \(c\) a multilinear polynomial \(p_c\in\mathbb F_2[s_1,\dots,s_n]\) of degree at most \(d\). It describes the configurations \(G(s)=(p_c(s))_{c\in C}\) for \(s\in\{0,1\}^n\). A row may also carry seed equations \(P_1=\dots=P_h=0\); then only seeds satisfying them count. A seed is admissible for a row if it satisfies the row's equations. The seed length \(n\) enters no bound below, except through the length \(\nu=\lceil\log_2 n\rceil\) of a seed-bit name.

A **seed routine** runs beside the block and sees what the block has read. It may read seed bits, and it may overwrite seed bits with values computed from what has been read. The position of each seed bit it reads or overwrites is also a function of the readings so far. Block and routine together form one decision tree. Theorem 1 is proved for this joint tree in the wider case where a stored value may also depend on seed bits the routine has read. A machine block is the special case where it does not, and Lemma 2 and Theorem 3 use only that case. A leaf \(\lambda\) fixes four things: the set \(Q_\lambda\) of entry coordinates read before the block stored to them, the set \(A_\lambda\) of seed bits read before the routine overwrote them, every stored value, and every overwritten seed value. Write \(s^\lambda\) for the seed \(s\) after the overwrites of \(\lambda\).

Rows \((p,P)\) and \((p',P')\) satisfy the **interval identity** across the block if, for every seed \(s\) with \(P(s)=0\) and its leaf \(\lambda\), the exit configuration equals \(G'(s^\lambda)\) and \(P'(s^\lambda)=0\).

**Theorem 1.** Suppose the identity fails at a seed \(s\) with \(P(s)=0\), at leaf \(\lambda\), either at a coordinate \(c\) or at an equation \(P'_j\). Then it fails at the same leaf and the same place for a seed \(\tilde s\le s\) coordinatewise, with \(P(\tilde s)=0\) and
\[
|\tilde s|\ \le\ \sum_{b\in Q_\lambda}\deg p_b\;+\;|A_\lambda|\;+\;\sum_i\deg P_i\;+\;\Delta .
\]
Here \(\Delta=\deg P'_j\) for an equation. For a coordinate, \(\Delta=\deg p'_c\) if the block read or stored \(c\) on \(\lambda\), and \(\Delta=\max(\deg p_c,\deg p'_c)\) otherwise. With no seed equations and all degrees at most \(d\), the bound is at most \(d(|Q_\lambda|+1)+|A_\lambda|\).

*Proof.* Fix \(\lambda\) and the place. Let \(v_b\) and \(u_j\) be the values the leaf expects at \(b\in Q_\lambda\) and \(j\in A_\lambda\). A seed reaches \(\lambda\) exactly when all these readings occur, because every address and branch on the way depends only on earlier readings. The exit bit \(e_c\) is the stored constant if \(c\) was stored, it is \(v_c\) if \(c\) was read and not stored, and it is \(p_c(s)\) otherwise. The seed \(s^\lambda\) is \(s\) with constants substituted at the overwritten positions. So the failing seeds at this leaf and place are the support of
\[
F=\prod_{b\in Q_\lambda}(p_b+v_b+1)\ \prod_{j\in A_\lambda}(s_j+u_j+1)\ \prod_i(P_i+1)\cdot\Phi ,
\]
where \(\Phi=e_c+p'_c(s^\lambda)\) or \(\Phi=P'_j(s^\lambda)\). Substituting constants and reducing \(s_j^2=s_j\) never raise degree. The multilinear form of \(F\) therefore has degree at most the stated bound \(D\). Set to zero every variable outside the support of the failing seed \(s\). The result is nonzero at \(s\), so it has a monomial, the constant term counting as the empty monomial; if it is present, \(\mu\) is empty and \(\tilde s=0\). Take one, \(\mu\), with no proper submonomial present. At the indicator vector of \(\mu\) every other monomial vanishes, so \(F=1\) there. That vector lies below \(s\) and has weight \(|\mu|\le D\). ∎

The last step is the journal's low-weight lemma applied to a restriction. The journal's Lean file for that lemma compiles under Lean 4.19 (command in Section 7). The product and degree accounting is a manuscript proof. It is audited by computing the algebraic normal form of every failure indicator in the experiments. [Existing Lean lemma](../lean/LowWeightPolynomial.lean)

**Sharpness.** Take \(q+1\) coordinates whose polynomials are disjoint monomials of degree \(d\), and \(a\) further seed bits. The block reads the first \(q\) coordinates and the routine reads the \(a\) bits. If all readings are one, the block stores 0 in the last coordinate. Both rows are the same. The only failing seed is all ones, of weight \(d(q+1)+a\), and the bound is \(dq+a+d\). The original script's variant leaves the memory alone and lets the routine clear one seed bit of the last monomial. The store variant uses the wider case. The original script's variant is a machine block and needs \(d\ge1\). So no triple admits a smaller bound for joint trees, and none with \(d\ge1\) for machine blocks. At \(d=0\) a machine block fails at every seed or at none, and the bound \(a\) is attained only at the leaf whose \(a\) readings are all one.

**Lemma 2 (charts).** A chart for a run consists of instruction times \(0=\tau_0<\dots<\tau_B\), a row for each, and a routine for each gap. Suppose the true initial configuration is \(G_0(s_0)\) for some admissible \(s_0\), every interval identity holds, and the verdict coordinate of the last row equals \(v\) at every admissible seed. Then the run has verdict \(v\) at time \(\tau_B\). Induct on the gaps with \(s_k=s_{k-1}^{\lambda}\). Halted states idle.

**What is charged.** Let the rows be given by a coefficient evaluator. It takes a row index, a coordinate and a monomial of at most \(d\) seed-bit names, and returns one bit within \(E\) steps, with random access to the input and to the chart's advice. The degree cap is then syntactic. Seed equations use the same format, and their number \(h\) and degrees are read off the chart. The checker runs the routine itself and cuts it off after \(a\) seed reads, so every leaf has \(|A_\lambda|\le a\). A gap of \(\ell\) instructions on a machine that reads at most \(\kappa\) words of \(w\) bits per instruction and has \(\rho\) register words, the program counter among them, reads \(q\le(\kappa\ell+\rho)w\) entry bits. By Theorem 1 a defective gap has a witness seed of weight at most
\[
W=d(q+1)+a+\textstyle\sum_i\deg P_i .
\]
A nondeterministic defect check guesses the gap, at most \(W\) names, and one coordinate or equation. It replays the gap with a private overlay of stores. It evaluates a polynomial at the guessed seed by summing the coefficients of the monomials inside the seed's support, which takes \(K_d(W')=\sum_{j\le d}\binom{W'}{j}\) evaluator calls, where \(W'\) is \(W\) plus the number of seed overwrites. With equations of degree at most \(d\), its time is at most a constant times
\[
R=(q+h+1)\,K_d(W')\,E+(\ell+T_r)\,\mathrm{polylog}\,N+W'\lceil\nu/w\rceil ,
\]
where \(T_r\) caps the routine's own steps and is enforced by the checker like \(a\). The checked format fixes the starting seed \(s_0=0\). The initial condition of Lemma 2 is then a universal challenge of one coordinate or equation: the constant term of row 0 there must be the true initial bit, or zero for an equation. The terminal condition is a sparse check of the same kind as a gap. This is the sense in which the advice for an interval is sublinear. The universally quantified data of one check are \(W\nu+O(\log N)\) bits, however many unknown bits the entry memory depends on. The whole verification is one existential chart followed by one universal check, and the memory of the machine is not restricted. Soundness against a malicious chart uses only these syntactic caps and Lemma 2.

## 2. A seed cannot shorten forced memory

Fix a chart satisfying Lemma 2 with the true verdict \(v\), a cut \(\tau_k\), and the true controller \(\gamma\) there, meaning the program counter and all register bits. Call a memory coordinate \(c\) **forced** if every configuration with controller \(\gamma\) from which the machine still reaches verdict \(v\) at \(\tau_B\) has the same bit \(b_c\) at \(c\).

**Theorem 3.** (i) Every admissible seed \(s\) of row \(k\) whose configuration \(G_k(s)\) has controller \(\gamma\) satisfies \(p_{k,c}(s)=b_c\) at every forced \(c\). (ii) There is such a seed \(s^*\) of weight at most \(D^*=d\rho w+\sum_i\deg P_{k,i}\). Hence each forced bit is the sum of at most \(K_d(D^*)\) coefficients of row \(k\), read off from \(s^*\).

*Proof.* (i) By the interval identities after cut \(k\), the machine started in \(G_k(s)\) reaches a configuration of the last row, whose verdict is \(v\). (ii) The indicator of "admissible with controller \(\gamma\)" is a product of \(\rho w\) factors \(p_b+\gamma_b+1\) and the factors \(P_i+1\). It is nonzero at the true seed and has degree at most \(D^*\). Apply the low-weight lemma. ∎

If the controller polynomials are constants and there are no seed equations, then \(s^*=0\) and the forced bit is the constant term of \(p_{k,c}\). In every case the row, together with at most \(D^*\) seed-bit names, determines every forced bit. However long the seed is, the forced part of memory has to be supplied by the row itself.

## 3. Ordinary files on which a table is forced, and a second program whose forced memory is one model

**The files.** Let \(m\) be even and \(f:\{0,\dots,m-1\}\to\{0,\dots,m-1\}\). Variables 1, 2, 3 are anchors and \(x_j\) is variable \(4+j\). The file has seven clauses forcing the anchors false, \(m\) clauses \((\neg 1\lor x_j\lor 2)\) that are true on the anchors, and \(m\) unit rows. Row \(i\) is \((x_{f(i)}\lor 1\lor 2)\) for \(i<m/2\) and \((\neg x_{f(i)}\lor 1\lor 2)\) for \(i\ge m/2\). Every literal is right-justified in a field of \(D+1\) characters, where \(D\) is the number of decimal digits of \(m+3\). With the header the file has exactly
\[
N=8\bigl(8+D+\mathrm{digits}_{10}(2m+7)+(2m+7)(3D+8)\bigr)
\]
bits. This gives 1,408 bits at \(m=4\), 70,696 at \(m=256\) and 1,311,968 at \(m=4096\). The ratio \(N/(m\log_2m)\) tends to \(48/\log_210=14.449\ldots\); at \(m=4096\) it is still 26.69. The file is satisfiable exactly when \(f(\{0,\dots,m/2-1\})\) and \(f(\{m/2,\dots,m-1\})\) are disjoint.

**Program P.** After a layout check, which sends every other input to a complete SAT procedure, P runs two loops over a work array \(B\) of \(m\) zero words.

```
phase 1   for i = 0..m-1:   a = f(i);  v = B[a]
                            if v != 0 and (v-1 < m/2) == (i < m/2):  decide by the mark pass below
                            B[a] = i+1
phase 2   for y = 0..m-1:   v = B[y]
                            if v == 0 or v > m or f(v-1) != y:  reject
          accept
```

If phase 1 finishes, both halves of \(f\) are injective, and the halves are disjoint exactly when every name has a writer. So P is correct. It uses at most \(2m\) loop iterations on every file of this layout. With digit-by-digit parsing of a \(D\)-digit field per iteration this is \(O(mD)=O(N)\) word operations, and the layout check is one scan. On a genuine run the test \(f(v-1)\ne y\) never fires when \(v\ne0\). It is redundant for the verdict. It is the instruction that makes the table matter.

**Proposition 4.** Let \(f\) be a permutation. At the head of phase-2 iteration \(y\), with the true registers, the run from a memory \(B'\) accepts if and only if \(B'[y']=f^{-1}(y')+1\) for all \(y'\ge y\). So all bits of these \(m-y\) words are forced. For \(y\le m/2\) there are at least \(m/2\) forced words.

This is immediate from the loop, since \(f(v-1)=y'\) has the single solution \(v=f^{-1}(y')+1\). The statement is false in phase 1. There a wrong value in a written cell can be masked by a value in an unwritten cell that triggers the fallback. At \(m=4\) this happens for 59,760 of the 155,520 combinations of permutation, loop head and memory.

**Proposition 5 (exposure law, already in the journal).** Let \(\pi\) be a uniform permutation of \(m\) points. A deterministic adaptive strategy that queries \(\ell\) distinct positions receives a uniformly distributed injective sequence of values. For a fixed set \(Y\) of \(t\) values, the probability that all of \(Y\) is received is \(\binom{\ell}{t}/\binom{m}{t}\le(\ell/m)^t\). Each new position holds a uniform unused value whatever was seen before.

**Corollary 6 (advice count; the journal's count applied to seed rows).** Fix the format before \(f\) is chosen: the degree \(d\), the controller size \(\rho w\), a cap on the total degree of a row's seed equations, hence \(D^*\), and a coefficient evaluator that makes at most \(E\) probes to words of the file per call. The evaluator's computation and its reads of advice are free. Suppose one file word meets at most \(C_0\) unit rows. Put \(w'=\lceil\log_2(m+1)\rceil\) and \(Q=C_0\,E\,w'\,K_d(D^*)\). Count as advice at a cut one binary string from which everything the evaluator depends on besides the file can be parsed: the row's own string, any bank shared by all rows, the cut index, and the names in \(s^*\), with the length fields the parsing needs. Let \(y\le m/2\).

1. If for every permutation \(f\) the run of P has a chart as in Lemma 2 whose last time is at or after the accepting halt, with verdict accept, and with a cut at the head of phase-2 iteration \(y\) and at most \(s\) advice bits there, then \(2^{s+1}\binom{t(Q+1)}{t}\ge\binom{m}{t}\) for every \(t\le m/2\). Taking \(t=\lfloor m/(2(Q+1))\rfloor\) gives \((s+2)(Q+1)>m/2\).
2. For \(t=\lfloor m/(4(Q+1))\rfloor\), all but an \(m\,2^{1-t}\) fraction of the \(m!\) permutation files need more than \(t\) advice bits at every phase-2 loop head \(y\le m/2\) simultaneously.

*Proof.* By Theorem 3 and Proposition 4, evaluating the \(w'\) low bits of cell \(a\) at \(s^*\) returns \(f^{-1}(a)+1\) for every \(a\ge y\). That costs at most \(w'K_d(D^*)\) evaluator calls, hence at most \(Q\) values of \(f\). Fix one advice string and the targets \(Y=\{m-t,\dots,m-1\}\). Decode each target and then look up \(f\) at the returned position. This is one adaptive strategy with at most \(t(Q+1)\) queries, and on success it has received every target. By Proposition 5 it succeeds on at most a \(\binom{t(Q+1)}{t}/\binom{m}{t}\) fraction of the permutations. Sum over the fewer than \(2^{s+1}\) strings, and for part 2 over the loop heads. ∎

At \(m=4096\), where \(N=1{,}311{,}968\), the first inequality with exact binomials gives \(s\ge1317.3\) bits for a decoder that uses \(Q=1\) value of \(f\) per word, \(s\ge137.6\) at \(Q=15\) and \(s\ge7.5\) at \(Q=255\), each maximized over \(t\). With polylogarithmic \(E\) and fixed \(d\) the count forces \(m/\mathrm{polylog}\,m=N/\mathrm{polylog}\,N\) advice bits. The whole table has \(\log_2m!\) bits, which is 3.3% of \(N\) at \(m=4096\).

**Which descriptions this excludes, and which it does not.** Consider charts that cut at loop heads. If every row carries its own advice and cuts are at most \(g\) iterations apart, at least \(\lfloor m/(2g)\rfloor\) rows pay the count. On all but an \(m\,2^{1-t}\) fraction of the permutation files, with \(t=\lfloor m/(4(Q+1))\rfloor\), the total, with the cut index and the names in \(s^*\) counted in each row, is at least \(\lfloor m/(2g)\rfloor\lfloor m/(4(Q+1))\rfloor\) bits. This is quadratic in \(m\) unless the gap or the probe count is a power of \(m\). **One bank shared by all rows escapes.** The journal's cycle-landmark decoder inverts a permutation with \(O((m/h)\log m)\) bits and \(O(h)\) queries for any \(h\). With \(h=g=\lceil m^{1/3}\rceil\) it would yield a degree-0 chart for this run with \(m^{2/3}\mathrm{polylog}\,m\) bits and the same order of defect time, against \(\Theta(m)\) loop iterations. In the loop-level model the cut controllers need no advice because P's loops have fixed length. This is a sketch: I did not write the chart out, no script checks it, and I did not re-audit that decoder. So this run defeats per-cut advice and polylogarithmic decoders. It does not defeat a seed chart, or a plain snapshot chart, with a shared bank and slow decoding. [Landmark decoder](inverse-snapshot-frontier.md)

**Rejecting runs.** The interrupted session's first family puts the table on rejecting runs. Its files have \(4m+7\) clauses and \(2m+3\) variables. An OR chain requires some \(x_j\) to be true, and row \(i\) is \((\neg x_{f(i)}\lor1\lor2)\). The file is satisfiable exactly when some name is missing from the image of \(f\). I rebuilt the generator from the log. It reproduces the logged lengths of 2,672, 140,336 and 2,622,696 bits at \(m=4,256,4096\). A program that stores \(i+1\) in \(B[f(i)]\) for every row and then runs phase 2 above, with the accepting exit now meaning UNSAT, is correct on this layout with no fallback. It signals UNSAT exactly on permutations. For a permutation the signal is reached, from a phase-1 loop head, exactly from the memories whose already written words are true, and from the head of phase-2 iteration \(y\), exactly from those whose words \(y'\ge y\) are true. Corollary 6 holds for this program at the same loop heads with the same proof. After the anchors are propagated these files are dual-Horn.

**A second program.** The mark pass, on the main family, keeps two bits per name. On a unit row with name \(a\) it rejects if \(a\) carries the opposite mark, and otherwise sets the mark for the row's sign. It decides every file of the layout in \(m\) iterations. Let \(\sigma\) assign a sign to each name. Give name \(a\) the seed bit \(s_a\). Describe its two mark bits as \((s_a,0)\) if \(\sigma(a)\) is positive and \((0,s_a)\) otherwise, and let the routine set \(s_a=1\) when the pass marks \(a\). This degree-1 chart satisfies every interval identity on every seed exactly when \(\sigma\) agrees with all unit rows, that is, when \(\sigma\) is a model. For a positive row on name \(a\): if \(\sigma(a)\) is positive, the marks \((s_a,0)\) become \((1,0)\), the row at \(s_a=1\); if not, the marks \((0,s_a)\) give a conflict at \(s_a=1\), and at \(s_a=0\) the exit \((1,0)\) differs from the claimed \((0,1)\). Negative rows are symmetric. On a satisfiable file its only advice is \(\sigma\), which is \(m\) bits shared by all cuts. This agrees with Theorem 3. On a permutation file the forced bits of the mark pass at a loop head are the opposite-sign bits of the names not yet processed, and they are zero. I did not write out a chart for its rejecting runs. The row is the product row \(\{0,\sigma(a)\}\) of the journal's earlier format, so this is not a case of seeds beating that format. It shows that the cost in Corollary 6 is a property of P. The semantic content of a satisfiable file is one model. P's table additionally records the order of the rows. At eight names, the 40,320 permutation files have 70 distinct pairs of sign sets, each shared by 576 files.

## 4. The three standard tests

**(a) Does the hard family have a fast globally correct solver? Yes.** P itself, and the mark pass behind the same layout check, decide every pinned file in \(O(N)\) word operations: at most \(2m\) and \(m\) loop iterations. Corollary 6 is a bound on what a description of P's memory must contain. It cannot be a superlinear time bound, because the program it describes runs in linear time.

**(b) Does the same argument prove the same bound for a trivially linear language? Yes.** Deleting the false anchors leaves a conjunction of unit literals. The pinned files are 1-CNF instances in width-three dress, and Corollary 6 holds on them verbatim. The same proof applies to any program that scatters an inverse table and later verifies each entry against its input, whatever language the program decides. Theorem 1 and Theorem 3 mention no language at all. The bound measures the description of one program's table. It is not a bound on reading the input and not a bound on SAT.

**(c) Does the argument survive the oracle of the relativized-clock entry? Yes.** Theorem 1 holds for any instruction set once an oracle query on a \(k\)-bit string counts as reading those \(k\) bits. Lemma 2 and Theorem 3 use only determinism. Proposition 5 and Corollary 6 are counting statements about \(f\), with free computation. Every statement of this note is therefore true in the world where explicit SAT has an \(O(n)\) oracle algorithm, and none can separate. The claim of Section 5 is false in that world for a specific reason. That solver ends with one query on a padded string of \(\Theta(n\log n)\) bits, which it wrote in \(O(n)\) steps. A gap containing the query reads at entry every query bit it did not itself write, so \(q+O(\ell w)=\Omega(n\log n)\) and \(R\ge q+\ell=\Omega(n)\) for every chart. A proof of the missing lemma must therefore use that one instruction reads \(O(w)\) bits. Theorem 1 uses this only through \(q\le(\kappa\ell+\rho)w\), and nothing else here depends on it. [Oracle model](relativized-clock.md)

## 5. Where the speedup stops

**Claim L (not proved).** There are an integer \(d\ge0\) and reals \(u<1\), \(v<1\) with the following property. Let M be any deterministic logarithmic-word RAM with unrestricted workspace that signals UNSAT soundly, within \(N^{1+o(1)}\) steps, on every unsatisfiable 3-CNF of \(N\) encoded bits. Then there are a coefficient evaluator and a routine interpreter, fixed programs that may depend on M but not on the formula, such that on every sufficiently long unsatisfiable formula the run of M up to its signal has a seed chart of degree at most \(d\) in that format whose whole description has at most \(N^{u+o(1)}\) bits and whose defect time \(R\) of Section 1 is at most \(N^{v+o(1)}\). The description includes cut times, controllers, row advice, any shared bank and the routine's parameters. The cited theorem assumes its premise on every sufficiently large unsatisfiable formula. Its proof charts only the locally generated formulas of the machines in the recurrence, so Claim L on those formulas should suffice. I did not check this restriction.

**If Claim L held, the journal's recurrence would exclude deterministic time \(N^{1+o(1)}\) for explicit SAT. Given that recurrence, Claim L is true exactly when no such M exists, so it restates the exclusion and is not a smaller target.** I take the step from the journal. In the negative-signal recurrence of the signed-window entry, a guessed chart of \(H^{u+o(1)}\) bits with a defect machine of horizon \(H^{v+o(1)}\) turns a nonacceptance certifier of exponent \(q\) into one of exponent \(\max\{ru,vq\}\). Here \(r=1\) and \(q_0=1\), so one step gives \(\max\{u,v\}<1\), which contradicts the bounded complementary diagonal. The only change is the defect machine. Lemma 2 and Theorem 1 give its soundness for every guessed chart, honest or not, given the syntactic caps. I did not re-derive the recurrence, its packed input accounting or the diagonal. For \(N^k\) time with \(k\ge2\), an explicit list of cut controllers already exceeds the budget \(ru<1\). A succinct schedule would be needed, and this note has nothing to say about it. [Recurrence](signed-snapshot-windows.md) · [Diagonal family](solver-snapshot-descriptions.md)

**Why this note does not supply Claim L.** Theorem 1 pays for unknown bits. It makes a check cost \(W\nu\) universal bits and \(K_d(W')E\) per read, whatever \(n\) is. Theorem 3 says the forced part of memory is not unknown. At every cut the chart must contain an exact, evaluator-readable description of every forced word. For degree 0, Claim L is the statement that the signed-window entry already records as missing, an unconditional upper bound on describing the states of every fast solver. For \(d\ge1\) it is weaker only where memory is unforced. So Claim L splits into two obligations, and this note constructs neither beyond the two examples of Section 3.

1. A low-degree parametrization of the unforced memory at each cut, with routines that read few seed bits.
2. One bank of \(N^{u+o(1)}\) bits and an evaluator of time \(N^{\delta+o(1)}\), with \((d+1)b+\delta<1\) for gaps of length \(N^b\), that returns every forced word at every cut.

The two generic ways to meet obligation 2 both fail. Storing a snapshot costs up to one word per instruction executed, about \(N\log N\) bits for a linear run, so \(u\ge1\). Recomputing a word by replay from the start costs the elapsed time, so \(v\ge1\), and replay from a later state needs that state stored. This is where the cost of a snapshot re-enters. It is the place the steering entry describes under "Where the hierarchy proof stops", and the seed does not move it. [Steering](../research-steering.md)

Short advice does exist for the words one interval reads. A gap of \(g\) iterations of P reads \(g\) table words. The identity must also hold at the words the gap does not read, because a forged untouched word would be used by a later gap. So each row is consulted at an arbitrary coordinate, and it has to be right at all forced ones.

On the runs of Section 3, obligation 2 is met only because a permutation has a special decoder. Claim L speaks about hypothetical machines. A proof that uses M's running time on the inputs considered, and not its correctness on all formulas, would apply to every program that is linear-time on those inputs. For that class a version asking for per-cut advice is false by Corollary 6, on accepting runs of the main family and on rejecting runs of the first. There the total advice times the defect time \(R\) is at least \(m^2/(64C_0)\) when \(g\le m/2\) and \(Q+1\le m/(4(2+\log_2m))\), since a gap of \(g\ge\rho\) iterations has \(R\ge g\,w'K_d(D^*)E\ge gQ/C_0\). The two exponents then sum to at least 2 in powers of \(m\). The shared-bank version is neither proved nor refuted here.

## 6. What is not proved

- No lower bound on the running time of any SAT solver, in any model, on any family.
- Claim L, for any \(d\). Its shared-bank form is also not refuted. Under a linear-time SAT hypothesis the transfer makes it false, which is the intended contradiction and not a proof. The journal's persistent-query theorem is the degree-0 statement of that kind. [Persistent queries](persistent-snapshot-query-cost.md)
- That seed rows are ever cheaper than the journal's product or shared-label rows on a run of a SAT solver. The mark-pass chart is a product row. The polynomial dependence is exercised only on synthetic blocks.
- Any instruction-level statement about P or the mark pass. Both are loop-level models run on parsed rows. The \(O(N)\) claims assume digit-by-digit field parsing and a linear layout check. Global correctness of P rests on that check and on an unspecified complete fallback.
- Proposition 4 in phase 1, where it is false as stated.
- The transfer from Claim L, which is borrowed. The landmark decoder, which is cited.
- Anything in Lean beyond the existing low-weight lemma. Nothing new was formalized.
- Priority. No external literature was opened for this note.

## 7. Reproduction and what each count checks

Run the commands from the directory that holds the audits. The outputs below are from 27 November 2026.

**The interrupted session's script**, unchanged except that it imports its helper module under that module's published name:

```
OPENBLAS_NUM_THREADS=1 python3 -B -u seed_interval_check_audit.py
```
```
DIMACS checker: ~/.elan/toolchains/leanprover--lean4---v4.19.0/bin/cadical
Intervals: {'UNSAT defect files': 24, 'pointwise circuit comparisons': 36864, 'nonvacuous path-coordinate checks': 1161, 'failing path-coordinate groups': 1594, 'SAT defect files': 120}
Sharp instances / seeds / largest necessary weight: 36 35350 14
All 65,536 upper-program verdicts agree with explicit assignment enumeration: {4: 256, 5: 40960, 6: 3600, 9: 20720}.
Ordinary files: {'UNSAT': 174, 'SAT': 86, 'counterfactual suffixes': 155616}
m / physical bits: 4 1408
m / physical bits: 256 70696
m / physical bits: 4096 1311968
Eight-name permutations / selector files / preimages: 40320 70 576
Adaptive sampling identities at m=7: 15
```
Apart from the shortened solver path, this is identical to the last run recorded in the interrupted session's log.

- **Intervals.** There are 144 blocks: 48 for each degree cap 1, 2, 3, on 8 seed bits. A block has a one-bit address register and three one-bit cells. It loads the cell the register points to, and if the reply is 1 it stores the register's bit in the other addressed cell. In 48 blocks the two addressed cells are seed bits and the routine writes the same seed bit. In the other 96 the routine reads one seed bit and overwrites another. The 36,864 comparisons are 144 times 256: on every seed a Boolean circuit for "some coordinate fails" agrees with direct execution. The 1,594 groups are pairs of a path and a coordinate with at least one failing seed; in each, the least failing weight is at most the original script's bound, which is the bound of Theorem 1 with \(\Delta\) replaced by \(\max(\deg p_c,\deg p'_c)\). In 1,161 groups that bound is below 8. Each circuit is serialized as a proper DIMACS 3-CNF of 2,784 to 105,648 bits, and cadical's verdict equals "some seed fails". A recount with the script's own functions (third command below) shows that the 24 unsatisfiable files are exactly the blocks where the cells are seed bits and both rows are equal, and that 20 of the 1,594 groups meet the original script's bound with equality.
- **Sharp instances.** For 36 triples with \(1\le d\le3\), \(q\le3\), \(a\le2\), all \(2^{d(q+1)+a}\) seeds are enumerated, 35,350 in all. Exactly one fails, the all-ones seed. The largest weight is 14.
- **Upper program.** This is the journal's 16-bit census replay, imported unchanged. It returns the truth table used in the next item. Its step counts concern four-bit words and give no bound in the ASCII length. [Census](exact-nine-step-clock-for-four-sat-words.md)
- **Ordinary files.** All \(4+256\) maps at \(m=2,4\) are serialized and re-read from the last \(m\) rows. For each, cadical's verdict, the census table at the file's pair of sign sets, and disjointness of the halves agree; a same-half repeat occurs exactly when a half is not injective; without a repeat, the phase-2 verdict equals disjointness. For the 26 permutations, every loop head and every memory with entries in \(\{0,\dots,m+1\}\), phase 2 accepts exactly when the suffix is the true one: \(96+155{,}520\) cases. This is Proposition 4 at \(m\le4\).
- **Eight names.** The \(8!\) permutations give 70 pairs of sign sets with 576 preimages each, all satisfiable in the census table.
- **Adaptive sampling.** For one adaptive rule at \(m=7\), lengths 1 to 5 and 1 to 3 targets, the count of permutations exposing all targets is \(7!\binom{\ell}{t}/\binom{7}{t}\).

**Independent audit**, sharing no code with the above except one byte comparison:

```
OPENBLAS_NUM_THREADS=1 python3 -B -u seed_chart_forced_memory_audit.py
```
```
A. word blocks: {'leaves': 2195, 'failing leaf-coordinate groups': 14131, 'groups with bound below the seed length': 11624, 'groups whose normal form has degree equal to the bound': 5026, 'groups whose least failing weight equals the bound': 109, 'of those, groups with bound 0': 40, 'groups from an outgoing equation': 1008, 'blocks': 260, 'block executions': 1064960} largest tight bound 11
B. sharp instances / seeds enumerated / largest forced weight: 140 1166300 18
C1. files: {"byte-identical to the worker's generator": 790, 'files decided by enumerating all assignments': 46916, 'files decided by cadical': 751, 'scatter runs without fallback': 14548, 'largest loop count / m, scatter': 2, 'UNSAT': 37080, 'SAT': 9836, 'larger random files decided by cadical': 180}
    m=4: N=1408 bits, N/(m log2 m)=176.0000, log2(m!)/N=0.0033
    m=256: N=70696 bits, N/(m log2 m)=34.5195, log2(m!)/N=0.0238
    m=4096: N=1311968 bits, N/(m log2 m)=26.6921, log2(m!)/N=0.0330
    m=65536: N=24118688 bits, N/(m log2 m)=23.0014, log2(m!)/N=0.0396
    limit of N/(m log2 m): 48/log2(10) = 14.449440
C2. forced suffix: {'phase-2 banks': 155520, 'phase-2 accepting banks': 37320, 'phase-1 banks': 155520, 'phase-1 banks accepted with a wrong written cell': 59760, 'm=6 one-cell edits': 241920, 'm=6 random banks': 20160}
C3. rows for the last live cell / rows sound on every seed: 98304 24
    first family m=4: N=2672 bits
    first family m=256: N=140336 bits
    first family m=4096: N=2622696 bits
C4. first family: {'SAT': 255, 'UNSAT (permutations)': 32, 'phase-2 memories': 158520, 'phase-1 memories': 158520}
D1. adaptive strategies x lengths x target counts with the exact law: 198
D2. advice count: s >= log2 C(m,t) - log2 C(t(Q+1),t) - 1, maximised over t <= m/2
    m=256 Q=1: s >= 81.1 bits at t=51; closed form floor(m/(2(Q+1)))-1 = 63
    m=256 Q=15: s >= 7.6 bits at t=6; closed form floor(m/(2(Q+1)))-1 = 7
    m=4096 Q=1: s >= 1317.3 bits at t=819; closed form floor(m/(2(Q+1)))-1 = 1023
    m=4096 Q=15: s >= 137.6 bits at t=95; closed form floor(m/(2(Q+1)))-1 = 127
    m=4096 Q=255: s >= 7.5 bits at t=6; closed form floor(m/(2(Q+1)))-1 = 7
    m=65536 Q=1: s >= 21096.5 bits at t=13107; closed form floor(m/(2(Q+1)))-1 = 16383
    m=65536 Q=15: s >= 2217.2 bits at t=1520; closed form floor(m/(2(Q+1)))-1 = 2047
    m=65536 Q=255: s >= 135.0 bits at t=94; closed form floor(m/(2(Q+1)))-1 = 127
E. mark-solver charts: {'failing one-step blocks': 3942, 'charts checked on every seed': 4112, 'UNSAT files with no passing chart': 174, 'SAT files with a passing chart': 86, 'two-bit mark memories': 30720}
```
The run took 37 seconds on one core.

- **A.** There are 260 random blocks of one to four instructions on a RAM with two 2-bit registers and four 2-bit cells. The instructions are indirect load, indirect store, add, AND, constant, a conditional skip, and seed reads and writes at computed indices. The seed has 12 bits. Rows have degree 0 to 3, with zero to two incoming and zero or one outgoing seed equations of degree at most 2. All 4,096 seeds are executed per block. For each of the 14,131 failing leaf-and-place groups, the failure indicator equals the product formula of the proof, its algebraic normal form has degree at most the bound of Theorem 1, and the least failing weight equals the least monomial size. In 11,624 groups the bound is below 12. In 5,026 groups the normal form has degree equal to the bound, so the degree count is tight there. The least failing weight equals the bound in 109 groups, 40 of them at bound 0.
- **B.** The sharp family is checked for \(d\le3\), \(q\le4\), \(a\le3\), in the store variant and the original script's seed-write variant, up to weight 18.
- **C1.** My generator is byte-identical to the original script's on 790 files. Truth is decided by enumerating all \(2^{m+3}\) assignments for all 46,916 maps at \(m=2,4,6\), and by cadical on 751 of them and on 180 random files at \(m=8,16,64\). P and the mark pass return the right verdict on every one. P avoids the fallback exactly on the 14,548 maps with injective halves and never exceeds \(2m\) iterations.
- **C2.** Proposition 4 is checked at \(m=4\) on all 155,520 cases, and at \(m=6\) on 241,920 one-cell edits and 20,160 random memories. The 59,760 count is the phase-1 failure quoted in Section 3.
- **C3.** This is Theorem 3 on the last iteration at \(m=4\). Of the 4,096 rows that give the three bits of the one live cell as arbitrary functions of two seed bits, exactly one per permutation passes on all four seeds: the constant row.
- **C4.** The first family is rebuilt for all 287 maps at \(m=2,3,4\). Enumeration of all assignments, cadical and the scatter program agree that the file is unsatisfiable exactly for the 32 permutations. For the 30 permutations at \(m=3,4\), every loop head of both phases and every memory with entries in \(\{0,\dots,m+1\}\), the UNSAT signal is reached exactly from the memories described in Section 3: 158,520 cases per phase. The three bit lengths equal those printed by the interrupted session's first run in its log.
- **D1.** Proposition 5 is checked for 14 hash-defined adaptive rules at \(m=5,6,7\), including uniformity of the reply sequence over injective tuples.
- **D2.** In these lines \(Q\) is the number of values of \(f\) used per decoded word, before the one verifying lookup. The printed bound is located by a floating-point scan over \(t\le m/2\) and then evaluated with exact binomials. The closed form is the bound from \(t=\lfloor m/(2(Q+1))\rfloor\).
- **E.** For all 260 maps at \(m\le4\) and all \(2^m\) sign vectors, the mark-pass chart is tested on every seed and every block. It passes exactly when \(\sigma\) agrees with all unit rows. Each of the 86 satisfiable files has \(2^{m-|f([m])|}\) passing vectors. None of the 174 unsatisfiable files has any. For the 24 permutations at \(m=4\), every loop head and all 256 two-bit mark memories, the pass accepts exactly when the opposite-sign bit of every unprocessed name is zero: 30,720 cases.

Two further commands:

```
OPENBLAS_NUM_THREADS=1 python3 -B seed_interval_recount.py
lean LowWeightPolynomial.lean
```
```
trial kinds (direct, new==old, some seed fails): {(True, True, False): 24, (False, False, True): 48, (False, True, True): 48, (True, False, True): 24}
{'gates': 6007, 'max gates': 95, 'max bits': 105648, 'min bits': 2784, 'max bound': 10, 'max least weight': 7}
groups with least weight == bound: 20 of 1594
```
The first replays the original script's 144 blocks with its own functions and random seed and sorts them by kind. The second printed nothing and returned exit status 0. It checks the journal's existing low-weight lemma and nothing written in this note.

The finite audits check the stated identities at the stated sizes. Theorem 1, Lemma 2, Theorem 3, Proposition 5 and Corollary 6 are manuscript proofs.
