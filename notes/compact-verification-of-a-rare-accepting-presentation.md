# Compact verification of a rare accepting presentation

**One successful presentation per positive native input suffices, even if its probability under uniform padding is $2^{-P}$ for a $P$-bit pad.** This holds when the successful pad has a locally readable description of $D=o(s)$ bits and its proper DIMACS output has $M=o(s\log s)$ bits, where $s$ is the encoded length of the unary-clock native input. The two bounds must hold for the **same** presentation, uniformly on sufficiently large positive inputs. Every presentation of a negative input must produce an unsatisfiable formula.

The advance is in the elapsed-time estimate. A local challenge can make polylogarithmically many adaptive reads to the description. Charging $D$ bits for each read loses the descent, for example at $D=s/\log\log s$. A constant number of guessed memory layouts lets one explicit SAT query check the challenge at total cost $O(D+M/\log(2+M)+u+\sqrt{s})$, where $u$ is the physically stored native descriptor length. The proof uses the actual construction time and the hypothetical solver’s actual clock.

A short locally readable description of an unrestricted accepting RAM history is still missing. The linear, quadratic and cubic time questions for ordinary explicit SAT remain open.

## One SAT query for all the adaptive reads

Use the journal’s bounded acceptance language $U(P,x,1^t)$. Suppose the compiler produces well-formed proper ASCII DIMACS with canonical decimal identifiers. Its length and individual bits are uniformly readable in $\operatorname{polylog}s$ time on a polynomial-length pad. A fixed deterministic decoder, given $y$, a description $d$, and a pad address, returns the corresponding bit in $\operatorname{polylog}s$ time. Every allowed description defines a consistent pad. On a positive input it suffices that one $d$ gives a satisfiable output.

For a formula of $M$ bits, use the journal’s certificate $z$ of $W=O(1+M/\log_2(2+M))$ bits. A false certificate has a failed deterministic local test. The important quantitative fact is that the **test label** has $O(\log(2+M))$ bits. Thus there are at most $s^c$ labels for a fixed $c$, although one test can take polylogarithmically many steps. The scanner records in $z$ handle long decimal names and clause boundaries. [Canonical local certificate](a-canonical-short-witness-for-locally-indexed-sat.md) · [Earlier positive-presentation descent](locally-short-sat-compilers-with-a-free-presentation.md)

Guess $d$, compute the actual $M$, and guess $z$. Put the physical source descriptor, $d$, and $z$ in one bit table. Pad its length to a power of two $H=2^\ell$, taking the least such power above $u+D+W+\lceil\sqrt{s}\rceil$. The old unary clock is supplied from its endpoints. For fixed table contents and a fixed test label, the genuine computation now reads a determinate set of at most $q=\operatorname{polylog}s$ distinct table addresses. This remains true for adaptive reads.

Use $B=2^{\lfloor\ell/2\rfloor}$ banks. An odd multiplier $a$ permutes the table by $i\mapsto ai\bmod H$. The high bits of the result select the bank. For a uniformly chosen odd $a$, two distinct addresses collide in their bank with probability at most $2/B$. Indeed, if their difference has 2-adic valuation $v$, multiplication gives a uniform residue of valuation $v$. A collision requires cyclic distance less than $H/B$. For $2^v\ge H/B$ this is impossible, and otherwise counting the two end intervals gives the bound. This is the classical multiply-shift estimate. [Dietzfelbinger, Hagerup, Katajainen and Penttonen, Lemmas 2.4 and 2.6](https://cglab.ca/~morin/teaching/484/notes/universal.pdf)

For one genuine test transcript the collision probability is at most $q(q-1)/B$. Since $H\ge\sqrt{s}$, this is at most $s^{-1/5}$ for sufficiently large $s$. Take a fixed integer $h>5c$. The probability that some label collides in **every** one of $h$ independent layouts is at most
$$
s^c\left(\frac{q(q-1)}B\right)^h<1.
$$
Consequently one tuple of $h$ multipliers works for all labels of this particular table. Different labels can use different members of the tuple. The outer native verifier guesses the tuple in $O(\log s)$ bits.

The explicit defect formula guesses **one common label**. In each layout it simulates that label until the test fails, the test passes, or a second distinct address requests an already used bank. It stops before supplying the reply to a colliding read. The formula requires *failure or collision in every layout*.

- If there is a genuine failed test, that label witnesses the formula for every tuple of layouts. In each simulation the prefix before the first collision is authentic.
- If every test passes, choose the tuple from the probability bound. For each label at least one simulation reaches the genuine pass, so the defect formula is unsatisfiable.

Thus a poor tuple can discard a good outer guess. It cannot certify a false one. The argument uses existence of the multipliers and has no randomized error in the resulting decision procedure.

**Physical bit cost.** Each bank supplies one proposed slot and reply. A read checks its slot and retrieves its reply from these $B$ proposals. Repeated reads of the same address reuse the proposal. Multiplexing the proposals and simulating the small private computation costs $B\operatorname{polylog}s=o(H)$ encoded bits, including gate names. It remains to authenticate all the proposed bank replies from the actual table.

Divide each bank into chunks of $g=\Theta(\log_2 H)$ bits, with $g$ a power of two and $g\le(\log_2 H)/8$ at large sizes. For each mask $m\in\{0,1\}^g$, a bank has a library variable saying that its proposed reply equals $m$ at the proposed low slot. A selected chunk requires the library variable for its actual mask. There are $O(H/g)$ data clauses and high-slot decoder gates. Each costs $O(\log H)$ physical bits in proper DIMACS. All bank libraries together cost
$$
O\!\left(B\,2^g\operatorname{polylog}s\right)=o(H).
$$
The outer machine can permute the table, gather the chunk masks and write all decimal clauses in $O(H)$ native steps per layout. There are constantly many layouts. This accounts for the serialized query and the work to construct it. Counting the gates of a semantic graph certificate alone would give neither estimate. [Journal’s compact lookup construction](compact-bit-projection-of-matrix-mismatch.md)

## Iteration and the sparse-pad threshold

Under an $O(N)$ deterministic SAT hypothesis, the outer verifier runs the solver on the defect file and accepts on UNSAT. Its honest branch takes $O(H)$ steps. Starting at the deterministic diagonal with $t=\Theta(n^2)$, use the fixed next cap $\lfloor t/2\rfloor$ while $t>n^{3/2}$. Through $O(\log n)$ rounds the payload is $n+O(\log^2 n)$ bits and $s=(1+o(1))t$. The controller carries only the previous program, payload and binary clock. The description, assignment and multipliers are guessed afresh inside the next verifier.

For $M=o(s\log s)$, splitting at $M=\sqrt{s}$ gives $W=o(s)$. Hence $D=o(s)$ makes $H=o(t)$ throughout the active rounds. Every positive stage has an accepting branch within the next cap. On a negative stage every completed query rejects the outer guess, and a timeout cannot create acceptance. The final ordinary bounded-run compilation and SAT call take $O(n^{3/2}\operatorname{polylog}n)=o(n^2)$, contradicting the diagonal. Rarity incurs no product of success probabilities. The promise must apply to the new verifier’s positive inputs at each stage. A supply of occasional short positive source inputs alone gives no such induction. [Native model and width simulation](native-unary-clock-band.md) · [Published clock descent and terminal compilation](compact-compilers-and-linear-sat-time.md)

For a concrete threshold, suppose a successful $P$-bit pad differs from a locally computable baseline at $k$ bit positions, with $P=s^{O(1)}$. It suffices that
$$
k\bigl(1+\log_2(P/k)\bigr)=o(s)
$$
for $k>0$. The zero-edit case needs only the baseline.

Here the leading coefficient on the address information is **one per binary bit**. For public $P,k$, put $b=\lfloor\log_2(P/k)\rfloor$ and $w=\lceil\log_2(P+1)\rceil$. Store the $b$ low bits of every sorted position $x_i$. In a high-part bit vector put a one at $\lfloor x_i/2^b\rfloor+i$, with zero-based $i$. Its length is $k+\lceil P/2^b\rceil\le3k$. Store a $w$-bit prefix count at each internal multiple of $w^2$. The total is at most
$$
kb+3k+3k/w
$$
bits, plus $O(\log P)$ if the dimensions must be supplied. Binary search on the prefix counts and a scan of at most $w^2$ bits recover a selected key. A second binary search decides pad membership in polylogarithmic time. Malformed descriptions can use a bounded decoder with default replies. For representing *all* supports at fixed dimensions, the counting lower bound is $\log_2\binom Pk\ge k\log_2(P/k)$. It says nothing about the cost of deciding an individual SAT file. At $P=65{,}536,\ k=4{,}096$, the implemented representation uses **25,052 bits** including its directory, versus 65,536 bits for the plain list of 16-bit positions. [Elias, *Efficient Storage and Retrieval by Content and Address of Static Files*](https://par.cse.nsysu.edu.tw/resource/paper/2021/210803/Efficient%20Storage%20and%20Retrieval%20by%20Content%20and%20Address%20of%20Static%20Files.pdf)

## Attempt on actual accepting histories

I tried grouping the journal’s local trace checks. Its pad records chronological and address-sorted memory events, transition data and the two index maps. Group $\lceil\log^A(s+2)\rceil$ consecutive checks per output row for any fixed $A\ge0$. One row is still locally computable in polylogarithmic time. With $O(s)$ checks this gives $m=O(1+s/\log^A(s+2))$ rows. A genuine accepting trace passes every row, and a passing pad reconstructs an accepting computation. [Original trace presentation](locally-short-sat-compilers-with-a-free-presentation.md)

There is an exact bit-length check for this construction. Seven proper clauses occupying 68 bytes force names $1,2,3$ false. Print `-1 2 3 0` and a newline for a passed group. Replace the minus by one space for a failed group. Either row occupies nine bytes. With the ordinary header, the file length is exactly
$$
M=8\bigl(77+\operatorname{digits}_{10}(m+7)+9m\bigr).
$$
The output therefore meets the length requirement. The unresolved quantity is $D$. The explicit trace pad uses $O(s\log s)$ bits. Grouping checks shortens the output without providing a sublinear locally readable description of a passing trace. In fact, **if linear SAT exists**, then for this trace presentation and every fixed total local decoder, some $c>0$ and infinitely many positive native files admit no successful description shorter than $cs$. This is the contrapositive of the descent.

A small counterexample pinpoints the failed replay argument. Partition $P=mh$ pad bits into $m$ blocks and require each block to equal `100…0`, with $h=\operatorname{polylog}P$. Print one guard row per block. The length indexer reads zero pad bits. Its all-zero replay obtains exactly the minimum length and produces UNSAT. The unique good pad has weight $m$ and density $2^{-P}$. For $P\asymp s$ and $h=\lceil\log_2\log_2(m+4)\rceil$, even the general sparse-support description costs $O(m(1+\log h))=o(s)$. This example separates the loss of satisfiability under replay from the cost of describing a successful pad.

**Quadratic and cubic scope.** For compilers covering full $U$, there is also an unconditional limit on shortening the output by arbitrary existential pads. For each fixed such local compiler there is a $K$ and there are infinitely many positive native files on which every satisfiable presentation has $M>s/\log^K s$. To see this, take a nondeterministic multitape language in time $n^2$ outside time $n^2/\log n$, and simulate its machine with native clock $Cn^2$. Guess pad bits on first access and cache them across the length computation and every later output-bit query. Reject over the proposed length cutoff. Otherwise generate the file and verify SAT nondeterministically. Every completed path uses one consistent pad. On the short branch this takes $(n+M+1)\operatorname{polylog}n$ time including the tape simulation by guessing and sorting the RAM trace. Choose $K$ larger than the simulation’s log exponent by two. If all sufficiently large positives had such a short presentation, the resulting machine would meet the forbidden clock. In particular the $O(s^{1/2}\log s)$ and $O(s^{1/3}\log s)$ output targets fail for this full-source route even with unrestricted pads. This is a compiler obstruction. The nondeterministic hierarchy supplies the separation used in it. [Seiferas, Fischer and Meyer, *Separating Nondeterministic Time Complexity Classes*](https://doi.org/10.1145/322047.322061)

## Finite checks

The audit checked 72,048 address-pair, width and bank-count combinations. Exactly 2,450 attained the $2/B$ collision bound. It checked 138,920 sparse select replies, 4,360 physical singleton-pad files, and 1,728 grouped two-store/one-load trace files.

The local 16-bit selector census tests the quantifiers in the defect query. After a fixed reindexing of its bits, two multipliers together recover all **6,560 positive files out of 65,536**. On **273 positive files**, every single odd multiplier blocks at least one genuine challenge. In the opposite direction, discarding colliding challenges in the first layout falsely accepts **5,100 negative files**. Z3 independently checked 192 serialized proper DIMACS defect instances, of which 155 were satisfiable. These are tests of the shared-label construction. Reindexing the selector bits supplies no new executed-instruction bound on the four-bit RAM.

Reproduce with `python3 -B adaptive_sparse_presentation_audit.py`. The clock and asymptotic encoding estimates are manuscript arguments. Historical priority for combining the hash layouts with the unary-clock descent is unverified. [Adaptive-layout and sparse-pad checks](../audits/adaptive_sparse_presentation_audit.py) · [Finite execution census](eight-steps-on-one-four-word-sat-input.md)