# The integer-input knapsack bound prices unpacking a word, and its ceiling is the bit scan

**Bottom line.** The classical quadratic lower bounds for knapsack on random access machines concern machines whose only arithmetic is addition and subtraction of whole input integers. I re-derived the argument with the integer size explicit. Two things are proved here and a third is argued. First, in the classical unit-cost integer model, integers of $n/2+O(\log n)$ bits already force $(1/4-o(1))n^2$ steps, where the published statement uses about $2n^2\log_2 n$ bits; in encoded bits this is $(1/2-o(1))N$, and an additive program matches it to leading order, so on this family the bound equals the number of free input bits to leading order. Second, on the journal's $w$-bit machine restricted to add, sub, the six comparisons, loads and stores, the same argument is valid while $T\le w-b-2$, where $b$ is the number of significant bits of the input words. Every bound it gives is therefore below $w$, the number of bits of one word: about $w-3w/W$ for the parity language at every width, and about $\min(w,W^2/12)$ for knapsack. It can exceed a scan of the $W$ input words only if $w>W$: exceeding the scan by a factor $f$ needs $w>fW$, and $w\approx fW$ suffices. It gives nothing at $w=\Theta(\log N)$. Third, at $w=\Theta(\log N)$ the restriction is immaterial at the linear-time scale: add, sub, compare, load and store carry out each of the twenty operations on chunked words with constant overhead, after unpacking the input in $N+O(N/\log N)$ steps by a decision tree with $2^w$ leaves per word, or in at most $8N+O(N/\log N)$ steps by one fixed loop. These routines are executed here; the preamble that turns them into one fixed program is argued, not executed. The hard family is decided in three or four instructions per word by a 20-operation program whose two certificates are sound on every input, so it is globally correct with any complete fallback. The same proof gives the same bound for "some word is odd", and the bound never exceeds $N$. **Nothing here bears on the unrestricted logarithmic-word clock.** The linear, quadratic and cubic questions remain open.

Notation: $\log$ is $\log_2$. $N$ is the encoded bit length, $W$ or $n$ the number of input words, $w$ the word width, $T$ the number of executed instructions.

## 1. What the sources state

Verification levels: **F** = I read the full text; **P** = I read the first page or the abstract; **S** = known only second-hand; **M** = bibliographic metadata only, no statement used; **X** = not accessed.

| Source | Level | What is used |
|---|---|---|
| Meyer auf der Heide 1985 [MadH85] | F | model, Lemmas 1–5, Theorems 1–6 |
| Meyer auf der Heide 1989 survey [MadH89] | F | Lemma 1, Theorems 5–10, remarks on DIV and element distinctness (stated there without proofs) |
| Ben-Or 1983 [BO83] | F | model, Theorems 3, 4, Examples 6(a), 13 |
| Kane, Lovett, Moran 2017 [KLM] | F | Theorem 1.3 and the remark after it |
| Meyer auf der Heide 1988 [MadH88] | P | abstract |
| Klein, Meyer auf der Heide 1983 [KM83] | S | not read; abstract known only through a search-tool paraphrase and the task brief; its unfolding theorem as printed in [MadH85] |
| Maass 1988 [Maa88] | P | abstract; no statement used |
| Ben-Amram, Galil [BG01] | P | a 1995 colloquium abstract; no statement used |
| Dobkin, Lipton 1978 [DL78] | M | component count only second-hand, from [BO83] and [MadH85] |
| Bshouty 1993 [Bsh93], Yao 1989 [Yao89] | M | none |
| Paul, Simon 1980 [PS80] | X | named in the abstract of [KM83] as the source of the decision-tree technique; venue as printed in the reference list of [KM83] (Crossref) |

**[MadH85], as printed.** The model: "Such a RAM has the capability of executing a direct or indirect storage access, an arithmetic operation from $\{+,-\}$, or an if-question in one step. We assume that the input is given integer by integer, not bit by bit." The RAM is "as defined in" Aho, Hopcroft and Ullman. The languages are $L_n=\{(\bar a,b):\exists\,\bar\alpha\in\mathbb N^n,\ \bar a\cdot\bar\alpha=b\}$ and $L_{n,k}$ with $\bar\alpha\in\{0,\dots,k\}^n$; $L_{n,1}$ is knapsack. A linear search algorithm (LSA) is a computation tree with operations $+,-$ and tests $f(x)>0$; its complexity is its depth.

* Theorem 1 (attributed to [BO83], [DL78]). If $L\subset\mathbb R^n$ consists of $q$ connected components, each LSA (ACT) recognizing $L$ has complexity at least $\log q$ (respectively $0.38\log q-0.61n$).
* Lemma 2. $\mathbb R_+^{n+1}\setminus L_{n,k}$ has at least $\frac{1}{2^n-1}(k+1)^{n(n-1)/2}$ connected components.
* Theorem 3, printed in [MadH85] as "Theorem 3 [7]" with [7] = [KM83]. "Let $M$ be a RAM accepting some language $L\subset\mathbb N^n$ in $t$ steps. Then there is an LSA $T_M$, with complexity $t$, that has the following property: For each leaf $v$ of $T_M$, there are hyperplanes $H_1^v,\dots,H_{2t^2}^v$ in $\mathbb R^n$, the forbidden hyperplanes for $v$, such that $T_M$ simulates $M$ for all inputs from $(c(v)\setminus\bigcup_i H_i^v)\cap\mathbb N^n$."
* Lemma 3. $M$ has at most $2^{t+n}t^{2n}$ characteristic components.
* Theorem 4. If $L$ is defined by hyperplanes with integer coefficients in $\{-k,\dots,k\}$ and $\mathbb R_+^n\setminus L$ has $q$ components, each RAM recognizing $L$ for inputs from an $(L,s,p)$-set with $s=(2k+1)^{3n^2}n^{2n^2}$ and $p\le2k$ needs at least $\log q-2n\log\log q$ steps.
* Theorem 5. "Each RAM recognizing $L_{n,k}$ needs at least $\frac12n(n-1)\log(k+1)-n$ steps for inputs from $\{0,\dots,(2k+1)^{3(n+1)^2}(n+1)^{2(n+1)^2}\}^n$."
* Theorem 6. The same bound for $L_n$, for inputs up to twice that size. Its input set consists of the members of $L_{n,k}$ together with all inputs having even $a_1,\dots,a_n$ and odd $b$.

Three inconsistencies in the print, none affecting the order of magnitude: Theorem 5's bound is the lower bound for $\log q$ alone and omits the $-2(n+1)\log\log q$ of Theorem 4; its input set is written with exponent $n$ although an input has $n+1$ integers; Lemma 4 has $n\log\log q$ where Theorem 4 has $2n\log\log q$. Both reference lists by this author print Dobkin–Lipton as "16 (1975), 417–421"; Crossref gives 16(3), 1978, 413–417.

**[MadH89], as printed.** The $S$-RAM has "an unbounded number of registers $R(0),R(1),\dots$ each of which can store an integer", direct and indirect storage accesses, branchings "IF $R(0)>0$", operations from $S$, unit cost, and only the constants 0 and 1. Lemma 1(b): "Each $S$-RAM recognizing some $L\subseteq\mathbb Z^n$ in $t$ steps can be simulated by an $S$-CT of depth $O(t\log t)$", the factor coming from a binary search among the up to $t$ addresses in use. Theorem 6: each $\{+,-,*\}$-RAM recognizing $L\cap\mathbb Z^n$, $L$ a union of hyperplanes with $q$ components, has complexity $\Omega(\log q/\log\log q)$; "Thus we e.g. only get an $\Omega(n^2/\log(n))$ lower bound for the knapsack problem." Theorem 7, attributed to [MadH85]: $\log q-n\log\log q$ for $\{+,-,*_c\}$-RAMs, where $*_c$ is multiplication with one constant operand. For element distinctness "we only get the trivial $\Omega(n)$ lower bound. … By clever use of indirect storage access, ED … can be recognized by a $\{+,-\}$-RAM in time $O(n)$." And: "If we now also take integer division into account, the above results become wrong, because there are simple languages like the set of even integers that can be recognized in constant time by a $\{+,-,DIV_c\}$-CT although it has infinitely many connected components." Theorems 9–10 and [MadH88] give polynomial-depth nonuniform trees for unions of hyperplanes; [MadH88]'s abstract says this "destroys the hope of proving nonpolynomial lower bounds on LSAs".

**[BO83].** An algebraic computation tree has operations $+,-,\times,/,\sqrt{\ }$ on real inputs and tests against zero, each of cost one. Theorem 3: $2^h3^{n+h}\ge N$ for a tree of height $h$ deciding a set with $N$ components. Theorem 4: $C(W)\ge(\log N-n\log3)/(1+\log3)\approx0.38\log N-0.61n$. Example 6(a) cites Dobkin and Lipton for $2^{n^2/2}$ components of the knapsack set and concludes $\Omega(n^2)$; [MadH85] phrases the same citation as "$\mathbb R^n\setminus L_{n,1}$ has at least $2^{(1/2)n^2}$ connected components". Example 13: integer parts of $n$ reals in $[0,M]$ need $\Omega(n\log M)$ operations.

**[KLM], Theorem 1.3.** "The SUBSET-SUM problem can be solved using a comparison decision tree of depth $O(n^2\log n)$ … all the queries are linear with $\{-1,0,1\}$ coefficients." The authors add that the number of threshold functions gives $\Omega(n^2)$ for every decision tree with a constant number of answers per query. The linear-decision-tree complexity of subset sum is therefore $n^2$ up to a logarithm. Converting their tree to RAM steps is not in their paper.

## 2. Bit-length accounting of the classical statement

Take Theorem 5 of [MadH85] at $k=1$ as printed. Each of the $n+1$ integers has
$$b(n)=\lceil\log(s+1)\rceil,\qquad \log s=(n+1)^2\bigl(3\log3+2\log(n+1)\bigr),$$
so $N=(n+1)b\sim2n^3\log n$ and $T=\frac12n(n-1)-n$. Solving, $T\sim\frac12\bigl(3N/(2\log N)\bigr)^{2/3}\approx0.655\,(N/\log N)^{2/3}$.

| $n$ | bits per integer | $N$ | $T$ | $T/(n+1)$ | $T/N$ | $\log T/\log N$ |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 3,737 | 63,529 | 104 | 6.12 | $1.6\cdot10^{-3}$ | 0.420 |
| 64 | 70,979 | 4,613,635 | 1,952 | 30.03 | $4.2\cdot10^{-4}$ | 0.494 |
| 256 | 1,371,583 | 352,496,831 | 32,384 | 126.01 | $9.2\cdot10^{-5}$ | 0.528 |
| 1024 | 26,011,063 | 26,661,339,575 | 522,752 | 510.00 | $2.0\cdot10^{-5}$ | 0.548 |

Bit lengths are exact (audit 2, section A). The last column tends to $2/3$ slowly because of the logarithm.

* **One word per integer** ($w=b$, in the classical model, whose registers are unbounded). The input has $n+1$ words. $T/(N/w)\sim n/2$: the bound is quadratic in the number of words and exceeds the word scan by a growing factor. Here $w\approx2W^2\log W$. On a machine whose registers also have $w=b$ bits the statement is not available; see section 3.3.
* **Bit scan.** $T/N\sim1/(4n\log n)\to0$. The exponent is $2/3$, with a factor $(\log N)^{-2/3}$.
* **General $k$.** $T/N\le\log(k+1)/\bigl(2(n+1)\cdot3\log(2k+1)\bigr)\le1/(6(n+1))$ for every $k\ge1$. The printed bound is below $N/(6n)$ at every parameter.
* **$w=\Theta(\log N)$ with multiword integers.** The input has $N/w=\Theta(n^3)$ words and $T/(N/w)=\Theta(1/n)$. The theorem also does not apply as a statement about the words. In word coordinates the hyperplanes $\sum_{i\in S}a_i=b$ have coefficients up to $2^{b-w}$, so Theorem 4 would need each coordinate to range up to $(2\cdot2^{b-w}+1)^{3n'^2}$ with $n'=(n+1)b/w$ coordinates, while a word is below $2^w$.

## 3. How small can the integers be?

### 3.1 The integer model and its histories

**Model Z.** Cells $M[a]$, $a\in\mathbb Z$, and registers hold integers. The input $x\in\mathbb Z^n$ is in cells $0,\dots,n-1$; everything else is zero. A program is any, possibly infinite, flow chart of instructions: add or subtract two operands; compare two operands by $=,\ne,<,\ge$ and either branch or write 0/1; load from or store to the cell addressed by a register or a literal; halt with a verdict. Operands are registers or integer literals. Every instruction costs one step, register moves are free, and the program may depend on $n$. Multiplication by a literal may be added; the proof does not change.

**Symbolic run.** Follow a run and attach to every word an affine form $c+a\cdot x$ with $c\in\mathbb Z$, $a\in\mathbb Z^n$. Keep the chronological list of writes $(B_s,g_s)$, address form and value form; the input cells are the first $n$ writes, with constant address forms. The **history** of the run is its sequence of outcomes:

* at a comparison of forms $f,g$: the sign of $f(x)-g(x)$;
* at a load with address form $A$: the latest write $s$ with $B_s(x)=A(x)$, or "none".

Arithmetic combines forms, a 0/1-writing comparison yields a constant determined by the sign, a load yields $g_s$ or $0$. By induction, the forms and the instruction executed at each step depend only on the history so far, and each word equals its form at $x$. Let $S_h$ be the set of integer inputs with halting history $h$ of length at most $T$. Then
$$S_h=(C_h\cap\mathbb Z^n)\setminus\bigcup\mathcal H_h ,$$
where $C_h$ is the convex set cut out by the sign conditions and by the equalities $A=B_s$ of the hits, and $\mathcal H_h$ consists of the hyperplanes $\{A=B_{s'}\}$ for every load and every write $s'$ later than its hit (every earlier write if there is no hit) whose address form differs from $A$. A load at step $t$ has at most $n+t-1$ earlier writes, so
$$|\mathcal H_h|\le A(T,n):=nT+\tfrac12T(T-1).$$
This is the content of Theorem 3 of [MadH85]: a tree of the same depth, wrong only on forbidden hyperplanes.

**Lemma S (segment).** Let $p,q\in S_h$. Every lattice point of the segment $[p,q]$ lying on no hyperplane of $\mathcal H_h$ belongs to $S_h$. At most $A(T,n)$ lattice points of the segment are outside $S_h$.

*Proof.* $C_h$ is convex and contains $p,q$. A hyperplane of $\mathcal H_h$ contains neither $p$ nor $q$, hence at most one point of their line. $\square$

**Lemma C (count).** There are at most $2^T\bigl(1+T(T+n)/2\bigr)^n$ histories of halting runs of length at most $T$.

*Proof.* Let $V$ be the affine subspace given by the equalities recorded so far. At a comparison of $f,g$: if $f-g$ is constant on $V$ the outcome is forced; otherwise "$<$" and "$>$" keep $V$ and "$=$" lowers its dimension. At a load, let $Z$ be the set of earlier writes whose address form agrees with $A$ on all of $V$. If $Z\ne\emptyset$ the only outcome that keeps $V$ is its latest member; "none" and earlier members of $Z$ are impossible. If $Z=\emptyset$ only "none" keeps $V$. A hit outside $Z$ adds a nontrivial equation and lowers the dimension; there are at most $T+n$ such hits. Other instructions have one continuation. A history has at most $n$ dimension-lowering events. Choosing their $k\le n$ positions gives at most $\sum_{k\le n}\binom Tk(T+n)^k2^{T-k}\le2^T(1+T(T+n)/2)^n$, using $\binom Tk\le T^k/k!$ and $1/k!\le\binom nk$. Shorter halting histories are padded injectively. $\square$

The count is that of Lemma 3 of [MadH85]. The second factor is real: a table built in $T$ steps answers a $\log T$-bit question in one indirect load, and this is why element distinctness costs only $O(n)$ in this model.

### 3.2 A fooling version that needs no large integers

**Theorem 1.** Let $F\subset\mathbb Z^n$ be a finite set of inputs with one verdict such that for all distinct $p,q\in F$ the segment $[p,q]$ contains more than $A(T,n)$ lattice points of the opposite verdict. If a model-Z program is correct on $F$ and on those lattice points and halts within $T$ steps on every member of $F$, then
$$|F|\le2^T\bigl(1+T(T+n)/2\bigr)^n .$$

*Proof.* If two members had the same history $h$, Lemma S would put an opposite-verdict lattice point in $S_h$, and the program gives all of $S_h$ one verdict. So members have distinct histories; apply Lemma C. $\square$

**Where the integer size enters, in the published proof and here.** In [MadH85] it enters in three places. Lemma 5(i) gives every component of the box $[0,s]^n$ an inscribed ball of radius $s/(k^{2n^2}n^{n^2})$; Lemma 5(ii) gives lattice points within $2k\sqrt n$ on every separating hyperplane; and Lemma 4 needs the ball radius to exceed $q(\log q)^{2n}2^{2n}(r+1)p$, because it bounds the lattice points lost to **all** $2^t\cdot2t^2$ forbidden hyperplanes of all leaves, and to all thin characteristic components, by a union bound. The factor $q$ in that union bound is what costs $\log q\approx n^2$ bits; the exponentially thin cones cost the rest. Theorem 1 argues inside one history, so only that history's $A(T,n)$ hyperplanes matter. The integers then need $\log A(T,n)\approx2\log T$ bits beyond the bits that carry the family.

**The family $K(m,b_0,\delta)$.** Put $D=2^\delta$, $\beta=b_0+\delta+1$. An instance has $n=m+\beta+1$ integers: items $x_0,\dots,x_{n-2}$ and target $x_{n-1}$. The members are
$$p_a=\bigl(2Da_1,\dots,2Da_m;\ 2,4,\dots,2^\beta;\ 2^{\beta+1}-1\bigr),\qquad a\in\{0,\dots,2^{b_0}-1\}^m .$$
Every integer is below $2^{b}$ with $b=b_0+\delta+2$. All items are even and the target is odd, so every member is a NO instance. For $a\ne a'$ let $g_0=\gcd(a'-a)$ and $v=(a'-a)/g_0$. The lattice points of the segment are $p_a+j(v,0,\dots,0)$, $0\le j\le2Dg_0$. Some $v_i$ is odd, so for odd $j$ the item $y=2Da_i+jv_i$ is odd and lies in $[1,2^\beta-1]$. Then $2^{\beta+1}-1-y$ is even and in $[2^\beta,2^{\beta+1}-2]$, hence a sum of distinct elements of $\{2,4,\dots,2^\beta\}$: a YES instance. There are $Dg_0\ge D$ odd values of $j$.

**Corollary 1 (knapsack with short integers).** Let $T_0$ be the largest $T$ with $2^T(1+T(T+n)/2)^n<2^{mb_0}$ and $A(T,n)<2^\delta$. Every model-Z program correct on the family and on its segment points runs for more than $T_0$ steps on some member. If $2^\delta>A(mb_0,n)$ then
$$T_0\ \ge\ mb_0-n\log\bigl(1+mb_0(mb_0+n)/2\bigr)-1 .$$
With $m=b_0=\mu$ and the least $\delta$ such that $2^\delta>A(\mu^2,n)$: $n=2\mu+O(\log\mu)$, the integers have $b=n/2+O(\log n)$ bits, $N=nb=n^2/2+O(n\log n)$, and $T_0\ge n^2/4-O(n\log n)=(1/2-o(1))N$.

| $\mu$ | $\delta$ | $n$ | bits $b$ | $N=nb$ | $T_0$ | $T_0/N$ | $T_0/n$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 64 | 20 | 150 | 86 | 12,900 | 1,164 | 0.090 | 7.76 |
| 256 | 31 | 545 | 289 | 157,505 | 49,086 | 0.312 | 90.07 |
| 1024 | 39 | 2,089 | 1,065 | 2,224,785 | 967,583 | 0.435 | 463.18 |
| 4096 | 47 | 8,241 | 4,145 | 34,158,945 | 16,390,437 | 0.480 | 1,988.89 |

The thresholds are exact integer computations (audit 2, section B). Against [MadH85] at $n=1024$: 26,011,063 bits per integer for $T\ge522{,}752$.

**The bound is tight on its own family.** A model-Z program correct on the whole box $[0,2^b)^n$ checks the $\beta+1$ public words (two steps each), locates each private word among the multiples of $2D$ by $b_0$ comparisons, confirms it with one equality test, and rejects; on any failure it reads every bit and answers from finite control. On members it executes exactly $m(b_0+2)+2(\beta+1)$ instructions: 66,626 at $\mu=256$ against $T_0=49{,}086$ (executed, audit 2 section D).

**Ceiling.** For any language on $[0,2^b)^n$, a model-Z program loads each word and determines it by $b$ comparisons with adaptive literals, then answers from finite control: $n(b+1)\le N+n$ steps, executed as `ceiling_reader`. The journal already records this: "unbounded nonuniform finite control can decide any bit predicate within one bit comparison per input bit plus input-word loads" ([steering entry of 27 November](../research-steering.md), [exact nine](exact-nine-step-clock-for-four-sat-words.md)). So no theorem of this kind exceeds the bit scan. Separately, [KLM] gives a nonuniform tree with $O(n^2\log n)$ subset-sum comparisons for every integer size; evaluating each comparison by $O(n)$ additions gives $O(n^3\log n)$ model-Z steps (my conversion).

### 3.3 The journal's machine: valid in a window, silent at logarithmic width

**Model N.** Words have $w$ bits, there are $2^w$ cells, arithmetic is modulo $2^w$. The input is $W$ words at addresses $0,\dots,W-1$ and memory is otherwise zero. The instruction set $I_{\rm add}$ consists of add and sub; the comparisons eq, ne, lt, ge, slt, sge, as branches or writing 0/1; any $w$-bit literal as an operand; direct and register-indirect load and store. These are 8 of the journal's 20 numerical operations. Inputs are restricted to the box $[0,2^b)^W$: the top $w-b$ bits of every input word are zero.

**Theorem 2.** Let $W\ge4$ and $T+b+2\le w$. Let $F\subset[0,2^b)^W$ have one verdict, with more than $A(T,W)$ opposite-verdict lattice points on the segment between any two members. If a program over $I_{\rm add}$ is correct on $F$ and on those points and halts within $T$ steps on $F$, then
$$|F|\le8^T\bigl(1+T(T+W)/8\bigr)^W .$$

*Proof.* Attach to every word a form $(c,a)$ with $c\in\mathbb Z/2^w$ and $a\in\mathbb Z^W$ kept unreduced; the word equals $c+a\cdot x$ modulo $2^w$. An add or sub at most doubles the largest $\|a\|_1$, so $\|a\|_1\le2^T$ throughout and $|a\cdot x|<2^{T+b}\le2^{w-2}$ on the box. The hypothesis is on $(w,b,T)$ only; literals are arbitrary and only move $c$.

*One wrap bit.* With $c\in[0,2^w)$ the integer $c+a\cdot x$ lies in $(-2^{w-2},2^w+2^{w-2})$, and for fixed $c$ only two of the wrap numbers $-1,0,1$ occur. Each wrap class is a slab, hence convex. For a signed comparison replace $c$ by $c+2^{w-1}$.

*Comparisons.* Refine the outcome of every comparison to the triple (wrap number of each operand, sign of the difference of the reduced values). Given the wrap numbers the difference is affine, so the classes are convex: at most eight with sign $\ne0$, at most four with sign $0$.

*Addresses.* Two address forms coincide at $x$ iff $(a_A-a_B)\cdot x\equiv c_B-c_A\pmod{2^w}$. The left side has absolute value below $2^{T+b+1}\le2^{w-1}$, so at most one integer value qualifies: coincidence is a single hyperplane, or never, or always when the forms are equal.

With these three facts the proofs of Lemmas S and C and of Theorem 1 go through with 8 in place of 2. $\square$

The constant in the window is not tight. An operand at step $t$ already has $\|a\|_1\le2^{t-1}$, because a run's first informative instruction is a load, and with that the same proof gives $T\le w-b-1$.

**Corollary 2 (what Theorem 2 gives at each width).** Let $W\ge4$ and let the bounds below be positive.

1. *Parity.* Every program over $I_{\rm add}$ deciding $\mathrm{PAR}_W=\{x:\text{some }x_i\text{ is odd}\}$ on $W$ words of $w$ bits runs for more than $w-3w/W-4\log(w+W)-5$ steps on some input.
2. *Knapsack.* If $6w/W+6\log(w+W)+4\le W/2$, every program over $I_{\rm add}$ deciding subset sum on $W$ words of $w$ bits runs for more than $w-6w/W-6\log(w+W)-6$ steps on some input. For wider words the bound of the widest such $w$ persists; it is $W^2/12-O(W\log W)$.

*Proof.* Put $\delta=\lceil2\log(w+W)\rceil$, so $2^\delta\ge(w+W)^2>A(w,W)$. For parity take $F=(2D\cdot[0,2^{b_0}))^W$ with $b_0=\lceil3w/W+2\log(w+W)\rceil$; its words are below $2^b$, $b=b_0+\delta+1$, and between two members there are at least $D$ points with an odd coordinate, as for $K$. Let $T=w-b-2$. Then $3T+W\log(1+T(T+W)/8)\le3w+W(2\log(w+W)-2)<Wb_0$, so $8^T(1+T(T+W)/8)^W<|F|$, and Theorem 2 applies. For knapsack take $K(m,b_0,\delta)$ with $b_0=\lceil6w/W+4\log(w+W)\rceil$ and $m=W-b_0-\delta-2\ge W/2$; then $mb_0\ge3w+2W\log(w+W)$ and the same computation applies with $b=b_0+\delta+2$. A family that fits width $w$ fits every larger width. $\square$

The table gives the best threshold $T^*$ over the families $\mathrm{PAR}$ and $K$ at prescribed $(W,w)$, computed in floating point with a conservative margin (audit 2, section W).

| $W$ | $w$ | $w/W$ | parity: $T^*$ | $T^*/W$ | formula of part 1 | knapsack: $T^*$ | $T^*/W$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| $10^4$ | $10^4$ | 1 | 9,941 | 0.99 | 9,934.8 | 9,940 | 0.99 |
| $10^4$ | 140,000 | 14 | 139,889 | 13.99 | 139,884.2 | 139,887 | 13.99 |
| $10^4$ | $10^6$ | 100 | 999,621 | 99.96 | 999,615.2 | 999,606 | 99.96 |
| $10^4$ | 8,333,333 | 833 | 8,330,742 | 833.07 | 8,330,736.0 | 8,112,167 | 811.22 |
| $10^4$ | $10^8$ | $10^4$ | 99,969,902 | 9,996.99 | 99,969,888.7 | 8,112,167 | 811.22 |
| $10^5$ | 1,700,000 | 17 | 1,699,866 | 17.00 | 1,699,860.9 | 1,699,865 | 17.00 |

**The answer to the range question.** Theorem 2 speaks only about $T\le w-b-2$, so every bound obtained from it is below $w$: fewer steps than one word has bits. It exceeds the $W$-step word scan only if $w>W$; the factor is at most $w/W$, part 1 attains $(1-3/W-o(1))\,w/W$, and it grows exactly when $w/W\to\infty$. A factor of order $W$, quadratic in the number of words, needs $w$ of order $W^2$. In encoded bits $N=Ww$ the parity bound is about $N/W$; the knapsack bound is largest at $w\approx W^2/12$, where it is about $0.44\,N^{2/3}$. The exact computation for $K(4096,4096,44)$ gives $T_0=5{,}477{,}698$ at the least width $5{,}481{,}842$, with $W=8{,}238$ and $N=4.5\cdot10^{10}$. At $w=\Theta(\log N)$ the theorem says only that a program runs for more than $O(\log N)$ steps. This is the exact form of "says nothing about our target".

**Outside the window the argument fails, not only its constants.** Two of the three facts break at $T=w-b+3$ (audit 1).

* *Lemma S fails for loads.* The program "load $x$; double it $w-b+1$ times; load from the resulting address" has $w-b+3$ steps. Its address $2^{w-b+1}x$ coincides with cell 0 on two parallel hyperplanes. At $w=12$, $b=4$ the inputs $x=0$ and $x=8$ have the same history, while $x=1,\dots,7$ have another one and lie on no recorded forbidden pair. The referee of this note found the first such example, with a store at address 100 and 13 steps; both are executed in audit 1.
* *Two wrap numbers per operand fails.* In "load $x$; double it $w-b+1$ times; branch on slt$(\cdot,0)$", also $w-b+3$ steps, the doubled operand has three wrap numbers with the signed offset, then five and nine after one and two more doublings. At $w=16$, $b=4$ its outcomes for $x=0,\dots,15$ are `0000111100001111`.

A non-convex outcome class alone would not be a failure: inside the window an outcome is already a union of up to four convex pieces. Random search does not see these failures: 12,000 random programs at each length $T=7,\dots,16$ with $w=12$, $b=4$ gave none, which only says they are rare. Whether the inequality of Theorem 2, or the lower bound itself, fails beyond the window is undecided; see section 7.

## 4. Which instructions break it

| Instruction | Status | Evidence |
|---|---|---|
| add, sub with literals; moves | survives | Theorems 1, 2 |
| eq, ne, lt, ge, slt, sge as branches | survives | Theorems 1, 2 |
| the same six writing 0/1 | survives | treated as a comparison followed by a constant |
| direct and indirect load, store | survives, at the price of the second factor in Lemma C | Lemma C; [MadH89] on element distinctness |
| multiplication by a literal over $\mathbb Z$ | survives | forms stay affine; [MadH89] Theorem 7 |
| add, sub beyond $T=w-b-2$ (wraparound) | **proof breaks, no faster program known** | doubling program above |
| multiplication of two data words over $\mathbb Z$ | proof breaks; [MadH89] Theorem 6 states $\Omega(\log q/\log\log q)$ without proof | not re-proved here |
| and, or, xor | **beaten** | 3 instructions per word |
| shl, shlmod by $w-1$; rol by $w-1$; ror by 1 | **beaten** | 3 instructions per word |
| mul by the literal $2^{w-1}$ | **beaten** | 3 instructions per word |
| shr, shrmod, sar, sarmod by 1 | **beaten** | 4 instructions per word |
| or, and, shl and shr by a data word (packed table) | **beaten on the whole box when $w\ge2^b$** | $3n+1$ instructions |
| integer division | beaten, per [MadH89]; not among the journal's 20 operations | quoted above |

**The escaping programs.** Each uses add, compare, load, store and one further operation to test the low bit: `(x and 1) != 0`; `(x or 1) == x`; `(x xor 1) < x`; `(x shl (w-1)) != 0`; `(x mul 2^(w-1)) != 0`; `slt(x ror 1, 0)`; `(h := x shr 1; h+h != x)`. The program loads all $n$ words and tests their parity. If all items are even and the target is odd it rejects, which is sound on every input. Otherwise it compares the public words with the ruler and the target; if they match and some private word is odd and below $2^\beta$ it accepts, which is sound because the even remainder is a ruler sum. Otherwise it calls a complete solver. Both certificates are sound on every input. With the executed fallback, the additive table program, the whole program is correct on every input of the box $[0,2^b)^n$ when $n+2^b<2^w$; it was checked against brute force on all 4,096 and all 32,768 inputs of two small boxes, for each of the twelve operations. On $K(256,256,31)$, with $n=545$, $b=289$ and $w=32{,}768$:

| Program | Instruction set | Steps on a member | Steps on a YES segment point |
|---|---|---:|---:|
| lower bound, Theorem 1 | model Z, additive | $>49{,}086$ | |
| lower bound, Theorem 2 | $I_{\rm add}$, $w\ge17{,}558$ | $>17{,}267$ | |
| additive family solver | $I_{\rm add}$ | 66,626 | |
| ceiling reader | $I_{\rm add}$ | 158,050 | |
| and, or, xor, shl, shlmod, mul, rol, ror | one extra operation | 1,635 $=3n$ | 1,925 |
| shr, shrmod, sar, sarmod | one extra operation | 2,180 $=4n$ | 2,470 |

**The dynamic programs.** The additive table-filling program uses only $I_{\rm add}$ and 7 to 9 steps per item and table cell, up to $9n\cdot2^b$ in all. It never beats $mb_0$ on the family: that would need $2^b\lesssim b_0$, and $b>b_0$. The word-packed program `R := 1; for each item a: R := R or (R shl a); answer bit t of R` takes $3n+1$ steps and is correct on the whole box when $w\ge2^b$ (executed and checked exhaustively at $b=3$, $w=16$). Its range does meet Theorem 2's: for $w\ge2^b$ both hold, and the packed program then beats the additive bound on every input of the box. Such a word is longer than the whole table of reachable sums. For $w<2^b$ the bitset has $\lceil2^b/w\rceil$ words and the program costs about $8n\lceil2^b/w\rceil$ steps (derived, not executed), which is above $mb_0$ unless $w\gtrsim2^b/b_0$. In the remaining range $T+b+2\le w\ll2^b/b_0$ no fast program for the whole box is known or expected, since for $w$ polynomial in $n$ it would decide subset sum in polynomial time. There the escape is the parity structure of the family, not the dynamic program.

**A remark on multiplication.** Over $\mathbb Z$ and without memory, parity of one $b$-bit integer still needs about $b/2$ steps with $+,-,\times$: a tree of depth $T$ computes polynomials of degree at most $2^T$, each leaf meets the line in at most $T(2^T+1)$ intervals, and each interval of a rejecting leaf contains at most one even number. The one-step escape by mul on the journal's machine comes from truncation modulo $2^w$.

## 5. Transfer to SAT

**Proposition U (the restriction is immaterial at the linear scale).** Let $h\ge1$, $2h\le w\le4^h$ and $K=\lceil w/h\rceil$. A program over $I_{\rm add}$ on words of width $w+\lceil\log(K+1)\rceil+3$ can

1. convert a raw $w$-bit input word into $K$ chunks of $h$ bits in $w+K+1$ steps with length-dependent literal thresholds, or in at most $8w+3K$ steps by one fixed loop that loads its thresholds from a table of powers of two;
2. after storing tables of $5\cdot4^h+(4h+2K+2)2^h+4w$ words, carry out any of the 20 operations on chunked words in at most $c_K=\max(8K^2+2K+2,\ 34K+12)$ steps, and a load or store at a chunked address in $5K$ steps.

Consequently a 20-operation program of running time $T_{\rm full}$ on $W$ input words is simulated in at most $W(w+K+1)+c_K\,T_{\rm full}$ steps plus one store per table word; with the fixed loop the first term is $W(8w+3K)$. The hypothesis $2h\le w$ makes the tables fit in the address space. *Program text.* The $w+K+1$ unpacking is a decision tree with $2^w$ leaves per input word and literal addresses, and the tables are written by one literal store per word; both make the program text grow with $N$. The fixed loop has constant text. With $w\le C\log N$ and $h=\lfloor\frac14\log N\rfloor$ this is $N+O(N/\log N)+O(C^2)\,T_{\rm full}+O(\sqrt N)$, respectively $8N+O(N/\log N)+O(C^2)\,T_{\rm full}+O(\sqrt N)$.

*Proof.* Unpacking is one load, $w$ comparisons with adaptive literals, and $K$ literal stores; the fixed loop spends at most eight instructions per bit (load a threshold, compare, subtract, double and increment the chunk, two counters, one test) and three per chunk. Bitwise operations are table lookups on chunk pairs. Add and sub propagate a carry learned by one comparison per chunk. Mul is schoolbook with low and high product tables and carry normalization by repeated subtraction. Comparisons are lexicographic from the top chunk, with one test of the sign bit for the signed ones. A shift count is formed from the two low chunks after testing that the others vanish, or reduced modulo $w$ by per-chunk residue tables; its quotient and remainder by $h$ come from tables. The chunks are written to a scratch array between zero or sign fill and each output chunk is the sum of two table entries addressed through the data-dependent offset. A rotation is a left shift plus a right shift. A narrower top chunk is reduced by one more table. The step bounds count these instructions. $\square$

Audit 3 runs all twenty chunk routines, both unpacking routines and the chunk-addressed memory, written with $I_{\rm add}$ primitives only, against the native reference for ten pairs $(w,h)$ including widths not divisible by $h$. The largest observed counts are 148 steps at $K=4$, 260 at $K=6$ and 352 at $K=7$. The tables there are filled by literal stores; a uniform program computes each entry in $O(1)$ steps from its neighbours, which I did not execute.

**Corollary 3.** Fix a width rule $w(N)\le C\log N$. If one 20-operation program decides explicit SAT in $O(N)$ steps, then one program over $I_{\rm add}$ at word width $w+O(1)$ does too. That machine reads the file packed at its own width; unpacking to bits and regrouping costs the same $O(N)$. For programs that may depend on $N$ the statement is empty, because the ceiling reader decides every language in $N+W$ steps. For one fixed program the unpacking is the fixed loop above, at most $8N+O(N/\log N)$ steps (executed). The chunk size, the powers of two and the tables must then be computed in a preamble instead of being stored as literals, and the loops over the $K$ chunks need counters: $O(1)$ additive steps per table entry and per chunk. That preamble is argued, not executed. Granting it, no lower-bound method that depends on the absence of and, or, xor, mul, shifts or rotations can exclude linear time for SAT at $w=\Theta(\log N)$: any $\omega(N)$ bound for $I_{\rm add}$ there is already a bound for the full machine.

**The journal's DIMACS families.** On the two-record families the journal's own scan programs are additive. The uniform one is "increment the pointer, load its word, and branch back to the increment if the loaded word equals $A$" ([fresh addresses](generating-fresh-addresses-on-one-native-sat-file.md)); the specialized one "loads each native input word from its hardwired literal address and compares it with its hardwired expected value" ([two instructions](two-instructions-per-homogeneous-dimacs-word.md)). Audit 4 runs both with every instruction except add, load and eq-branch disabled: 3,000 and 2,000 steps for $m=1000$. A restricted bound above a scan is impossible there.

Theorem 1 also has nothing to hold on. Each designated word takes two values. Two unsatisfiable files sharing a $B$ position have no satisfiable well-formed point between them. This uses the little-endian layout: $A$ and $B$ agree on their eight high-order bytes ` 1 2 0\n `, so every integer between them does too (asserted in audit 4), each intermediate word still ends its own record, and the shared $B$ word stays an intact falsified clause. In a big-endian packing an intermediate word could end in a minus sign and the claim would need another argument. So a separated family of unsatisfiable files has pairwise disjoint $B$ sets and at most $m$ members; the satisfiable side has one member. Thus $\log|F|\le\log m$. For the lattice condition, I counted the interior points $(x,A+B-x)$ of the segment between the files $(B,A)$ and $(A,B)$ at 16-byte words in which both words are records with eight-digit names. There are at most 33 for the names 10000019 and 10000033, and at most 79,999,998 for a digit-complementary pair, against $A(2W,W)=3{,}999{,}000$ at $W=1000$ and $399{,}990{,}000$ at $W=10^4$. The count depends on the names; the cap $\log|F|\le\log m$ does not. I have no proof that no ASCII family admits a large fooling set; Corollary 3 makes that question irrelevant to the target.

**A positive statement in an idealized setting.** Encode a 3-CNF with one literal per word: variable $=\lfloor\ell/2\rfloor$, negated iff $\ell$ is odd. Use eight public clauses forcing $y_1,y_2$ false, and $m$ pairs of clauses $(\ell_i\vee y_1\vee y_2)$, $(\ell_i'\vee y_1\vee y_2)$. The members have $\ell_i=(i+1)2^{b_0+\delta+2}+1+2Da_i$ and $\ell_i'=\ell_i+1$: a negated variable $u$ and the positive variable $u+1$, in disjoint slots, hence satisfiable. On the segment between two members, every odd step makes some $\ell_i$ even with $\ell_i'=\ell_i+1$: the clauses $(x_u\vee y_1\vee y_2)$ and $(\neg x_u\vee y_1\vee y_2)$, unsatisfiable. There are at least $D$ such points (checked by a complete search on four small parameter sets).

**Proposition 4.** In model Z, on these files of $W=6m+24$ words, every program correct on the family and its segment points runs for more than $T_0$ steps on some member, where $T_0$ is the largest $T$ with $2^T(1+T(T+W)/2)^W<2^{mb_0}$ and $A(T,W)<2^\delta$. With words of the journal's wide rule $w=32\lceil\log(N+2)\rceil$ this gives $T_0=465{,}082$ at $m=1000$ ($w=736$, $T_0/W=77$, $T_0/N=0.105$) and $T_0=630{,}143{,}326$ at $m=10^6$ ($w=1056$, $T_0/W=105$, $T_0/N=0.099$). It is vacuous for $w\le128$ at these sizes.

This is linear in $N$ and superlinear in the number of words by a factor $\Theta(\log N)$. Its premises are essential: unbounded integer registers, so no wraparound; a binary encoding in which every word value is a legal literal; words wider than about $15\log T$. It fails all three tests of section 6: a 20-operation program decides the family and its segment points in $16m+48$ steps (executed: 16,048 at $m=1000$) and, with a complete fallback that learns the signs and the equality pattern of the variables in at most $4W+W(W-1)/2$ steps, is correct on every file (checked on 3,000 random perturbed files); the same proof bounds "some word is odd"; and the bound is the cost of extracting the sign bit of each literal. On the journal's machine Theorem 2 confines it to $T<w$.

**Why "knapsack as SAT with packed integers" does not help.** Theorem 1 never exceeds $\log|F|$. If every word of a family of files takes at most $V$ values then $|F|\le V^W$, and the theorem gives at most $W\log V-W\log(1+T(T+W)/2)$, which is negative once $V\le T^2/2$. A non-vacuous application needs words that range over more than $T^2/2\ge W^2/2$ values each, with the fooling property across that whole range. The standard linear-length CNF for subset sum spends a constant number of clause records per integer bit, so each word carries $O(1)$ free bits and a compare-only scan of two steps per word already separates all members. The handicap of $I_{\rm add}$ is unpacking a wide word; an encoding that has unpacked the bits removes it.

## 6. The three standard tests

For Theorems 1 and 2 and their corollaries:

**(a) Does the hard family have a fast globally correct solver on the unrestricted 20-operation RAM?** Yes. $K(m,b_0,\delta)$ together with all the segment points used in the proof is decided in $3n$ to $4n$ instructions on members and $3n+\beta+2$ to $4n+\beta+2$ on the segment points by the program of section 4. Its two certificates are sound on every input; the executed fallback is complete on the box, and with any complete fallback the program is globally correct. For $w\ge2^b$ the packed program decides the whole box in $3n+1$. The published statement quantifies over the whole box, which contains NP-hard inputs; but the argument certifies its bound already on this subfamily, so it does not price that hardness. [MadH85] itself proves Theorem 6 on an input set of even $a_i$ and odd $b$.

**(b) Does the same argument give the same bound for a trivially easy language?** Yes. Let $\mathrm{PAR}_W=\{x:\text{some }x_i\text{ is odd}\}$ and $F=(2D\cdot[0,2^{b_0}))^W$. Between two members there are at least $D$ lattice points with an odd coordinate, by the argument for $K$. Theorem 1 gives $T>T_0$ with $T_0\approx W\bigl(b-1-\log A-\log(1+T(T+W)/2)\bigr)$:

| $W$ | bits $b$ | $T_0$ | $T_0/W$ | additive reader $W(b_0+2)$ | 20-operation scan |
|---:|---:|---:|---:|---:|---:|
| 1,000 | 64 | 10,628 | 10.63 | 39,000 | 2,002 |
| 1,000 | 256 | 185,982 | 185.98 | 222,000 | 2,002 |
| $10^6$ | 256 | 147,713,806 | 147.71 | 203,000,000 | 2,000,002 |
| $10^6$ | 1024 | 905,490,159 | 905.49 | 966,000,000 | 2,000,002 |

The 20-operation program ORs the words and tests one bit: $2W+2$ steps (executed at $W=1000$). At $b=32$ the bound is below a scan at both sizes ($T_0=59$ and $0$). On the journal's machine, Corollary 2 gives parity $w-3w/W-4\log(w+W)-5$, which is at least the knapsack value at every width.

**(c) Is it a bound on reading or encoding rather than on deciding?** Yes, in three precise senses. The bound is at most $\log|F|$ and the ceiling reader achieves $N+n$ for every language. On its family the bound equals the free bits to leading order and is matched by a program that only locates each word. And at $w=O(\log N)$, by Proposition U, the advantage of the full machine over $I_{\rm add}$ is the unpacking of each word, $w+K+1$ steps with a program text that grows with $N$ or at most $8w+3K$ with a fixed loop, up to the constant factor $c_K$ per operation and $O(\sqrt N)$ table words. At the widths where Theorem 2 exceeds a scan, $w>W$, Proposition U does not apply, since its tables need $4^h$ words with $w\le Kh$. In the component-counting form, $n^2$ is the number of bits naming a threshold function of $n$ variables, and [KLM] reads them with $O(n^2\log n)$ comparisons.

## 7. What is not proved

* No lower bound for the unrestricted 20-operation machine, at any width, beyond those already in the journal.
* Nothing for $I_{\rm add}$ beyond $T=w-b-2$; every bound from Theorem 2 is below $w$. In particular I do not know whether $\mathrm{PAR}_W$ on full-width words needs $\Omega(Ww)$ steps over $I_{\rm add}$ with wraparound. The natural programs cost $w$ doublings or $b$ comparisons per word, and the convexity argument does not reach them. Outside the window Lemma S itself fails for loads and the bound on wrap numbers fails for comparisons, both at $T=w-b+3$ by explicit programs; the window constant is not tight below that ($T\le w-b-1$ follows from the same proof).
* The statements quoted from [MadH89] for $\{+,-,*\}$ and for DIV are cited, not re-proved. The remark on parity with multiplication covers one integer and no memory.
* The worst-case constant $c_K$ of Proposition U is derived by counting instructions and confirmed only on the tested operands. The uniform preamble on which Corollary 3 rests (chunk size, powers of two and tables computed by one fixed program) is argued, not executed. No complete 20-operation program was simulated end to end: the per-operation routines, the unpacking and the chunk-addressed memory were each checked separately, and their composition is by counting. The multiword packed dynamic program is costed by derivation only.
* No impossibility result for fooling families in ASCII DIMACS in general.
* I could not read [KM83] or [PS80]. Statements attributed to [KM83] are those quoted in [MadH85]. I found no earlier statement of Theorem 1 with integers of $n/2+O(\log n)$ bits in the sources I opened, which are few; priority is unestablished. It is a routine sharpening.
* The $(1/4-o(1))n^2$ of Corollary 1 is half the classical leading constant, because the ruler occupies half of the coordinates.

## 8. Executable checks

The scripts sit with the other audits, import nothing else from the journal, and write no files. Run each from that directory with `python3 -B <script>`. [Machines](../audits/integer_ram_step_model.py) · [audit 1](../audits/integer_ram_unfolding_audit.py) · [audit 2](../audits/knapsack_fooling_family_audit.py) · [audit 3](../audits/additive_word_unpacking_audit.py) · [audit 4](../audits/knapsack_sat_transfer_audit.py)

**Audit 1, `integer_ram_unfolding_audit.py 14`** (20 s). Lemma S on random programs with large literals, both comparison kinds, loads through input values and stores onto input cells; then the explicit failures outside the window.

```
Z n=2 b=5 T=10: pairs=6000 same_history=5330 lattice_points=31232 changed_on_forbidden=49 alias_hits=61 wrapped_operands=0 max_forbidden_pairs=15 count_bound_ok=True VIOLATIONS=0
Z n=3 b=5 T=14: pairs=6000 same_history=5194 lattice_points=24506 changed_on_forbidden=66 alias_hits=118 wrapped_operands=0 max_forbidden_pairs=27 count_bound_ok=True VIOLATIONS=0
Z n=4 b=4 T=18: pairs=4000 same_history=2865 lattice_points=6106 changed_on_forbidden=57 alias_hits=249 wrapped_operands=0 max_forbidden_pairs=34 count_bound_ok=True VIOLATIONS=0
N n=2 b=4 w=16 T=10: pairs=6000 same_history=5087 lattice_points=16190 changed_on_forbidden=40 alias_hits=80 wrapped_operands=229 max_forbidden_pairs=15 count_bound_ok=True VIOLATIONS=0
N n=3 b=4 w=16 T=10: pairs=6000 same_history=4979 lattice_points=12633 changed_on_forbidden=36 alias_hits=174 wrapped_operands=228 max_forbidden_pairs=24 count_bound_ok=True VIOLATIONS=0
N n=3 b=5 w=20 T=13: pairs=6000 same_history=5288 lattice_points=24109 changed_on_forbidden=47 alias_hits=100 wrapped_operands=436 max_forbidden_pairs=26 count_bound_ok=True VIOLATIONS=0
N n=4 b=3 w=24 T=19: pairs=6000 same_history=3242 lattice_points=4629 changed_on_forbidden=36 alias_hits=745 wrapped_operands=331 max_forbidden_pairs=35 count_bound_ok=True VIOLATIONS=0
load; 9 doublings; load: T=11 (T+b+2-w=+5); history(0)==history(8): True; x=1..7 with the same history: 0; on a recorded forbidden pair: 0
load; 9 doublings; add 100; store 100; load: T=13 (T+b+2-w=+7); history(0)==history(8): True; x=1..7 with the same history: 0; on a recorded forbidden pair: 0
d=12 T=14 (T+b+2-w=+4): unsigned wrap numbers=1 signed=2
d=13 T=15 (T+b+2-w=+5): unsigned wrap numbers=2 signed=3
d=14 T=16 (T+b+2-w=+6): unsigned wrap numbers=4 signed=5
d=15 T=17 (T+b+2-w=+7): unsigned wrap numbers=8 signed=9
steps 15 = w-b+3 = 15
branch outcome for x=0..15: 0000111100001111
```

The rows `Z` are the integer model, `N` the native model at the edge of the window $T=w-b-2$. The two rows starting with `load` are the failures of Lemma S at $w=12$, $b=4$. The random search outside the window ($T=7,\dots,16$, 12,000 programs each) reports no violation. The random rows are tests, not proofs.

**Audit 2, `knapsack_fooling_family_audit.py`** (about 3 min; sections A–E and W). Section A is the table of section 2. Section B checks the family by brute force and prints the thresholds of Corollaries 1 and 2:

```
m=2 b0=2 delta=2: n=8 bits=6 members=16 all NO; pairs=120; fewest YES lattice points strictly inside a segment=4 (required >= D=4)
m=2 b0=3 delta=1: n=8 bits=6 members=64 all NO; pairs=2016; fewest YES lattice points strictly inside a segment=2 (required >= D=2)
m=3 b0=2 delta=0: n=7 bits=4 members=64 all NO; pairs=2016; fewest YES lattice points strictly inside a segment=1 (required >= D=1)
```

Section C computes the number of components of $\mathbb R_+^{n+1}\setminus L_{n,1}$, which Claim 1 of [MadH85] identifies with the number of threshold functions in its sense. Each function is settled by explicit integer weights or by a 2-summability certificate:

```
n, decreasing functions, #N(n,1), log2 #N, Lemma 2 lower bound 2^(n(n-1)/2)/(2^n-1), n^2, non-threshold (2-/3-summable)
1      3      2   1.00      1.00   1 0+0
2      6      5   2.32      0.67   4 0+0
3     20     19   4.25      1.14   9 0+0
4    168    149   7.22      4.27  16 18+0
5   7581   3286  11.68     33.03  25 4294+0
```

Section D:

```
exhaustive box: m=1 b0=1 delta=0 n=4 b=3 w=16: 4096 inputs, every program correct on all
exhaustive box: m=2 b0=1 delta=0 n=5 b=3 w=16: 32768 inputs, every program correct on all
large instance: m=b0=256 delta=31 n=545 b=289; T0_int=49086, T0_nat=17267, native w=32768 (window needs w >= T0_nat+b+2 = 17558)
   additive-family on member: steps [66626]
   additive-family/native on member: steps [66626]
   ceiling on member: steps [158050]
   fast/and on member: steps [1635]
   fast/and on YES point: steps [1925]
   fast/shr on member: steps [2180]
   fast/shr on YES point: steps [2470]
```

"Every program" means the ceiling reader, the additive family solver, both in models Z and N, the packed and additive dynamic programs, and the twelve escaping programs. The packed program's worst case over the boxes is 13 and 16 steps, $3n+1$. Section E prints the table of test (b). Section W prints the table of Corollary 2 and asserts the formulas of parts 1 and 2 against the computed thresholds:

```
W, w, w/W | PAR: b0, delta, T*, T*/W, T*/w, formula w-3w/W-4log2(w+W)-5 | K: m, b0, delta, T*, T*/W, T*/w
   1000         1000       1.0 |      21  21          955       0.95  0.955          948.1 |     955      22  21          953       0.95  0.953
  10000       140000      14.0 |      74  34       139889      13.99  0.999       139884.2 |    9889      75  34       139887      13.99  0.999
  10000      8333333     833.3 |    2543  45      8330742     833.07  1.000      8330736.0 |    4977    4976  45      8112167     811.22  0.973
 100000      1700000      17.0 |      90  41      1699866      17.00  1.000      1699860.9 |   99867      90  41      1699865      17.00  1.000
```

**Audit 3, `additive_word_unpacking_audit.py 14`** (14 s).

```
w=16 h=4 K=4 (simulating width 22): tables 1696 words, 20 operations checked on 1124 operand pairs each
   worst steps per operation: and=20, or=20, xor=20, add=15, sub=15, mul=118, shl=68, shr=66, sar=70, shlmod=76, shrmod=74, sarmod=78, rol=143, ror=145, eq=4, lt=8, slt=10, ne=4, ge=8, sge=10
   unpack: 21 steps per raw word (= w+K+1); as one fixed loop: at most 139 (<= 8w+3K = 140); chunk-addressed load/store: at most 20 steps (147 random addresses over all 2^16 agree with a dictionary)
w=31 h=5 K=7 (simulating width 37): tables 6172 words, 20 operations checked on 924 operand pairs each
   worst steps per operation: and=35, or=35, xor=35, add=27, sub=27, mul=352, shl=113, shr=111, sar=115, shlmod=135, shrmod=133, sarmod=136, rol=246, ror=249, eq=7, lt=14, slt=16, ne=7, ge=14, sge=16
   unpack: 39 steps per raw word (= w+K+1); as one fixed loop: at most 268 (<= 8w+3K = 269); chunk-addressed load/store: at most 35 steps (150 random addresses over all 2^31 agree with a dictionary)
```

The other eight configurations are $(w,h)=(24,4),(24,6),(30,5),(32,8),(13,4),(23,6),(29,8),(12,5)$. The printed table sizes exclude the $K2^h$ address-translation words.

**Audit 4, `knapsack_sat_transfer_audit.py`** (8 s).

```
m=1000, all A (satisfiable): hardwired check 2000 steps, pointer loop 3000 steps; every instruction except add, load, eq-branch disabled
A and B share the 8 high-order bytes b' 1 2 0\n ' (little-endian); so does every integer between them: a word
names 10000019/10000033: at most 33 interior lattice points (x, A+B-x) of the segment between (B,A) and (A,B)
names 53817264/46182735: at most 79999998 interior lattice points (x, A+B-x) of the segment between (B,A) and (A,B)
m=2 b0=2 delta=1: W=36 words of 7 bits, 16 satisfiable members; fewest unsatisfiable lattice points inside a segment=2 >= D=2; scan solver 80 steps on a member
with the complete fallback: correct on 3000 random perturbed files (worst 322 steps; fallback bound 4W+W(W-1)/2)
    1000   736   686   37     6024      4433664       465082    77.20  0.1049     16048
 1000000  1056   975   58  6000024   6336025344    630143326   105.02  0.0995  16000048
executed: m=1000, w=73: member accepted in 16048 steps (16m+48); a neighbouring segment point rejected in 158
```

Thresholds with $\log|F|>2^{25}$ or more than $10^4$ words, and all of section W, are computed in floating point with a conservative margin; the others, including every row of the tables in sections 3.2 and 4, are exact integer comparisons.

## References

* [MadH85] F. Meyer auf der Heide, "Lower bounds for solving linear diophantine equations on random access machines", J. ACM 32(4) (1985) 929–937. [doi:10.1145/4221.4250](https://doi.org/10.1145/4221.4250). Full text read from the scan at [urn:nbn:de:hbz:466:2-5951](https://nbn-resolving.org/urn:nbn:de:hbz:466:2-5951). **F**
* [MadH89] F. Meyer auf der Heide, "On genuinely time bounded computations", STACS 1989, Lecture Notes in Computer Science, pp. 1–16. [doi:10.1007/BFb0028969](https://doi.org/10.1007/BFb0028969). Full text read from the [Paderborn digital collection, record 43624](https://digital.ub.uni-paderborn.de/hsx/download/pdf/43624). **F**
* [BO83] M. Ben-Or, "Lower bounds for algebraic computation trees (preliminary report)", STOC 1983, 80–86. [doi:10.1145/800061.808735](https://doi.org/10.1145/800061.808735). Full text read from a [course copy](https://ibr.cs.tu-bs.de/courses/ws2223/ag/papers/Ch3/BenOr.pdf). **F**
* [KLM] D. Kane, S. Lovett, S. Moran, "Near-optimal linear decision trees for k-SUM and related problems", [arXiv:1705.01720v1](https://arxiv.org/abs/1705.01720v1); STOC 2018, [doi:10.1145/3188745.3188770](https://doi.org/10.1145/3188745.3188770). arXiv version read. **F**
* [MadH88] F. Meyer auf der Heide, "Fast algorithms for N-dimensional restrictions of hard problems", J. ACM 35(3) (1988) 740–747. [doi:10.1145/44483.44490](https://doi.org/10.1145/44483.44490). First page read from the [Paderborn digital collection, record 43614](https://digital.ub.uni-paderborn.de/hsx/download/pdf/43614). **P**
* [KM83] P. Klein, F. Meyer auf der Heide, "A lower time bound for the knapsack problem on random access machines", Acta Informatica 19 (1983) 385–395. [doi:10.1007/BF00290735](https://doi.org/10.1007/BF00290735). Publisher page blocked; not read. Abstract known through a search-tool paraphrase, metadata via Crossref. **S**
* [Maa88] W. Maass, "On the use of inaccessible numbers and order indiscernibles in lower bound arguments for random access machines", J. Symbolic Logic 53(4) (1988) 1098–1109. [doi:10.2307/2274607](https://doi.org/10.2307/2274607). Abstract only. **P**
* [BG01] A. Ben-Amram, Z. Galil, "Topological lower bounds on algebraic random access machines", SIAM J. Comput. 31(3) (2001) 722–761. [doi:10.1137/S0097539797329397](https://doi.org/10.1137/S0097539797329397). Only a [1995 colloquium abstract](https://www.imada.sdu.dk/Events/CS_Colloquia/Announcements/19950314.html) read. **P**
* [DL78] D. Dobkin, R. Lipton, "A lower bound of ½n² on linear search programs for the knapsack problem", J. Comput. System Sci. 16(3) (1978) 413–417. [doi:10.1016/0022-0000(78)90026-0](https://doi.org/10.1016/0022-0000(78)90026-0). Metadata from Crossref. **M**
* [Bsh93] N. Bshouty, "On the complexity of functions for random access machines", J. ACM 40(2) (1993) 211–223. [doi:10.1145/151261.151262](https://doi.org/10.1145/151261.151262). **M**
* [Yao89] A. Yao, "Lower bounds for algebraic computation trees with integer inputs", FOCS 1989, 308–313. [doi:10.1109/SFCS.1989.63495](https://doi.org/10.1109/SFCS.1989.63495). **M**
* [PS80] W. J. Paul, J. Simon, "Decision Trees and Random Access Machines", Symposium über Logik und Algorithmik, Zürich 1980. Citation as printed in the reference list of [KM83] in its Crossref record. Not accessed. **X**
