# The instruction-capacity line is capped at about n/w charged steps and gives no SAT time bound

This note retires the instruction-capacity line. In the per-path codimension forms that cover branches, loads, stores and indirect addressing (Theorems 1 and 1′), every lower bound the line can give is at most about $n/c^*$ charged steps for every Boolean function, where $c^*\ge w-1$ is the largest single-step charge: about $n/w$, one packed scan. So the line gives no SAT time bound. The inequality proposed for it, "charged instructions times products per instruction is at least $\mathrm{MC}(f)$", is false in the journal's native model (freeze count, branches, indirect addressing). It is true only for oblivious code under the structural count, where it is a standard circuit simulation, and using it there would need a new superlinear explicit circuit lower bound. No lower bound for SAT or for any language is proved here, and the linear, quadratic and cubic questions remain open.

Reading by reading:
- **Oblivious code, structural count, capacity = MC of the operation:** true. This is Theorem 2: every executed nonlinear instruction is counted, the capacity is $\mu(\mathrm{op})$, the multiplicative complexity of that operation, and control flow and addresses are fixed.
- **Branches or indirect addressing:** false for every capacity polynomial in $w$, whatever the reading. This is Proposition 4: $\mathrm{MC}(\mathrm{MUX}_k)=2^k-1$, yet one charged indirect load, or $k$ charged one-bit branches, computes $\mathrm{MUX}_k$.
- **Each addition charged its journal capacity $\lfloor w/2\rfloor$ as an MC capacity:** false already for one oblivious addition. This is Proposition 3: the top sum bit has MC exactly $w-1$. The journal's $\lfloor w/2\rfloor$ is a codimension capacity, and it pairs with $\lambda$ (defined in Section 1), not with MC.

What does cover branches, loads, stores and indirect addressing is a per-path codimension inequality (Theorem 1 for the structural count, Theorem 1′ for the journal's freeze count). Every lower bound derived from it is at most about $n/c^*$ charged steps for every Boolean function, unconditionally. Here $c^*$ is the largest single-step charge: $c^*\ge w$ once computed addresses are allowed (each costs up to $w$), $c^*\ge w-1$ from a full-word ADD alone, and $c^*=rw$ under freezing. The per-path caps are the journal's own remark; this note makes them explicit for the capacity line. [Packed control words](processing-packed-control-words-in-dimacs.md)

So the line cannot pass a scan. In its MC form it would need a new superlinear explicit circuit lower bound, and that form applies only to oblivious code.

## 1. The journal's charging model

Two variants appear in the journal, and both are covered below.

- **Straight-line native model.** Instruction $j$ is a native word operation. Its operands are arbitrary $\mathbb F_2$-affine functions of the raw input bits and of the combinations exposed earlier. It exposes $k_j$ affine combinations of its output bits, and the final answer is affine in everything exposed. The journal proves these capacities: [Native addition](native-addition-and-independent-bit-products.md)
  - one addition, one exposed scalar: exactly $\lfloor w/2\rfloor$ independent products;
  - one AND: $w$;
  - one addition, all bits: codimension $w-1$;
  - one addition, $k$ scalars: codimension $\le h-\lfloor h/2^k\rfloor$ with $h=w-1$.

  The composed bound is $m\le\sum_j(h-\lfloor h/2^{k_j}\rfloor)$ for $\mathrm{IP}_m$.
- **Charged-step RAM model.** A step is *free* if its control and effective addresses are already determined and its new data are affine in old data. Otherwise it is *charged*: a nonlinear operation on data, a data-dependent branch, or a data-dependent address. At a charged step the operands are frozen, which costs at most $Cw$ affine equations. After $s$ charged steps the run lies in a flat of codimension at most $Cws$, plus 1 for the output bit. [Packed control words](processing-packed-control-words-in-dimacs.md) · [Nonlinear work after the cut](nonlinear-work-after-the-one-bit-sat-cut.md)

**The two step counts must be kept apart.**
- **$s_J(x)$, the journal's freeze count.** Once a step is charged, its operands are resolved. Everything computed from resolved values afterwards is free, however nonlinear.
- **$s_S(x)$, the structural count.** It counts the steps on $x$'s path that are either a non-affine data operation whose operands are not all constant on the *path cell*, or a branch or computed-address access whose control or address word is not constant on the path cell. The path cell is the set of inputs that share $x$'s path up to that step. Every native instruction of the straight-line model counts.

$s_J\le s_S$, and the gap can be huge. Resolve each input word with one charged step, about $N/w$ steps; after that any amount of nonlinear work is free under $s_J$ but counted under $s_S$.

**Notation.** All of the following are over $\mathbb F_2$. A *flat* is a nonempty affine subspace of $\{0,1\}^n$.
- $\lambda(f)$: the minimum codimension of a flat on which $f$ is affine. This is $n$ minus the weak-normality dimension.
- $C_{\rm aff}(f,x)$: the same minimum over flats that contain $x$.
- $D_{\rm aff}(f)$: the minimum depth of a parity decision tree whose leaves output affine functions. This is the journal's notation. [Independent dot product](adding-an-independent-dot-product-to-a-boolean-circuit.md)
- $\mathrm{MC}(f)$: the minimum number of binary AND gates in an XOR/AND/1 circuit; for multi-output maps, all outputs are counted together.

For an operation $\mathrm{op}:\{0,1\}^{rw}\to\{0,1\}^{r'w}$ and a linear map $L$ selecting the output combinations that are used later, define two capacities:
$$\kappa(\mathrm{op},L)=\max_{E\ \text{flat}}\ \min\{\operatorname{codim}_E E' : E'\subseteq E\ \text{flat},\ L\circ\mathrm{op}\ \text{affine on }E'\},\qquad \mu(\mathrm{op},L)=\mathrm{MC}(L\circ\mathrm{op}).$$
The journal's "products per instruction" is $\kappa$: its proofs bound codimension "on any nonempty affine flat of raw inputs". It is not $\mu$.

## 2. Statements

**The proposed inequality.** For every program, the number of charged instructions (the journal's free-XOR/affine count) times the products per instruction is at least $\mathrm{MC}(f)$.

**Theorem 1 (per-path codimension, structural count).** Fix a word RAM of width $w$ with a finite bounded-arity instruction set, unrestricted memory (unwritten cells are 0), conditional branches, and computed-address loads and stores. Let $P$ halt on every $x\in\{0,1\}^n$, where the input is placed affinely in memory, and let $P$ compute $f$. Let $s(x)=s_S(x)$ be the structural count from Section 1.

Give each step $t$ a charge $c(t)$ as follows.
- **Nonlinear data operation:** $c(t)=\kappa(\mathrm{op}_t,L_t)$, where $L_t$ spans every combination of $\mathrm{op}_t$'s output that is used on *some* continuation of the current path prefix. For a RAM register this is normally the whole word ($L_t=\mathrm{id}$; for example $c(t)\le w-1$ for ADD). Charging only the combinations used on the eventual path is justified only in the straight-line variant, where the uses are fixed in advance.
- **Branch on a zero test:** $c(t)\le1$. For any other branch predicate, $c(t)$ is at most the number of control bits it reads.
- **Computed address:** $c(t)\le w$.
- **Step not counted in $s_S$:** $c(t)=0$.

Then three statements hold.
- (a) There is an input $x^*$ with $\lambda(f)\le\sum_{t\in\mathrm{path}(x^*)}c(t)\le c^*\max_x s(x)$, where $c^*=\max(\kappa_{\max},w,b_{\max})$ and $b_{\max}$ is the largest branch charge. In (a), $b_{\max}\le2$ for zero tests, equality tests and two-word comparisons: force the outcome at the highest bit position where the operands can differ, using at most 2 equations.
- (b) For every $x$, $C_{\rm aff}(f,x)\le\sum_{t\in\mathrm{path}(x)}c_x(t)$. Here $c_x(t)\le w-1$ for ADD, $\le w$ for AND, $\le rw$ for any operation of arity $r$, and $\le w$ per branch word or address.
- (c) $\lambda(f)\le\min(\mathrm{MC}(f),\,C_{\rm aff}(f,x))$, and $C_{\rm aff}(f,x)\le D_{\rm aff}(f)\le n-1$ for $n\ge1$.

**Theorem 1′ (journal's freeze count).** For every input $x$:
$$\lambda(f)\le C_{\rm aff}(f,x)\le rw\cdot s_J(x)+1,\qquad D_{\rm aff}(f)\le rw\cdot\max_x s_J(x)+1.$$
Freezing all $\le rw$ operand, control and address bits of each charged step makes its outputs constants, so later steps on them are free. This is the journal's "$Cws+1$" with $C=r$. The smaller constants of Theorem 1 ($\kappa$, $w-1$, $w$) are proved only for $s_S$. The ADD-then-BRZ-on-the-sum pattern counts 1 under $s_J$ but 2 under $s_S$.

**Credit, and what is new.**
- Theorem 1(b) is the per-run accounting of the affine-dimension note. That note uses nested flats through the true input, charges $O(w)$ per bounded-arity instruction, and the charges telescope to the final codimension. It even uses finer charges: for example, a load through a moving address is free when the returned word is affine. [Affine dimension along runs](affine-dimension-along-sat-runs.md)
- Theorem 1′ is the parity-decision-tree simulation of the guarded-SAT note (at most $Cw$ adaptive parity probes per charged instruction), together with the $Cws+1$ remark of the packed-control-word note. [Nonlinear word steps](nonlinear-word-steps-on-guarded-sat.md) · [Packed control words](processing-packed-control-words-in-dimacs.md)
- New here:
  - the existential form 1(a), with $\kappa$ charges and zero tests charged 1;
  - Theorem 2 and its $s_J$ counterexample;
  - Propositions 3 and 4;
  - $\lambda(\mathrm{MUX}_k)=k$ (a proof contributed during review);
  - the explicit $n-1$ caps, tied to the capacity line.

**Theorem 2 (MC, oblivious code, structural count).** Suppose the control flow and all effective addresses of $P$ do not depend on the input. Then $\mathrm{MC}(f)\le\sum_{\text{executed nonlinear }t}\mu(\mathrm{op}_t,L_t)\le s_S\cdot\mu_{\max}$. This is **false for $s_J$**, even for oblivious code. One nonlinear operation per input word resolves the whole input in about $N/w$ charged steps. After that, an oblivious circuit of any MC runs free. For instance, take $n=4$, $w=2$ and the instruction set {ADD$_2$, AND$_2$}, so $\mu_{\max}=2$. One AND of the two input words resolves all four bits, and after that any degree-4 function (MC 3) is computed free. So $s_J=1$ and $\mathrm{MC}=3>1\cdot2$.

**Proposition 3.** For $w\ge3$, the reading of the inequality that charges each addition its journal capacity $\lfloor w/2\rfloor$ as an MC capacity is false, even for one oblivious addition. If each instruction is instead charged the maximum $\mu$ over an instruction set containing AND, which is $\ge w$, Theorem 2 makes the inequality true for oblivious code.

**Proposition 4.** $\mathrm{MC}(\mathrm{MUX}_k)=2^k-1$, where $\mathrm{MUX}_k(T,i)=T_i$ with $T\in\{0,1\}^{2^k}$ and $i\in\{0,1\}^k$. A RAM computes it with one charged step (an indirect load), or with $k$ charged one-bit branches followed by a free load at an address that is then known. In contrast, $\lambda(\mathrm{MUX}_k)=k$.

## 3. Proofs, capacities and computations

### Proofs

**Theorem 1(a).** The construction keeps the following invariants:
- a flat $F$ on which every input follows the current path prefix;
- every input word and every value written so far, or every used combination in the straight-line variant, is affine on $F$;
- memory is a finite map from addresses that are constant on $F$.

Each kind of step preserves them as follows.
- **Affine data step:** affine maps of affine data stay affine.
- **Charged nonlinear operation:** the operand map $A$ is affine on $F$ with image a flat $E$. Choose $E'\subseteq E$ of codimension at most $\kappa$ on which $L\circ\mathrm{op}$ is affine, and set $F'=F\cap A^{-1}(E')$. This is nonempty, and its codimension in $F$ equals $\operatorname{codim}_E E'$ because $A$ maps $F$ onto $E$.
- **Branch:** the control word is affine on $F$. Restrict to a value set that fixes the outcome. A zero test needs one equation: set one nonconstant bit to 1.
- **Computed address:** the address word is affine on $F$; fix its nonconstant bits, at most $w$ equations.
- **Halt:** the output bit is affine on $F$.

Steps not counted in $s_S$ cost nothing. Affine data operations keep affinity. A branch or address that is constant on its path cell is constant on $F$, because $F$ is contained in the path cell. The final $F$ is nonempty, and its path is the halting path of each of its inputs, so the cost is at most $c^*s_S(x^*)$ for any $x^*\in F$. Since $f$ is affine on $F$, $\lambda(f)\le\operatorname{codim}F$. ∎

**Theorem 1(b).** Repeat the construction, but fix every chosen form to its value at $x$, so the flat always contains $x$.
- **ADD:** fix the propagate bit $p_i=a_i+b_i$ at each level; then $c_{i+1}=(1+p_i)a_i+p_ic_i$ is affine. Fixing $a_i+c_i$ instead, as the code does, also works. Either way the cost is at most $w-1$.
- **AND:** fix one operand, at most $w$.

**Theorem 1′.** At each step charged under $s_J$, query all of its $\le rw$ operand, control and address bits. Each query is an affine form on the current flat that depends only on earlier answers. The step's outputs are then constants, matching the journal's resolution, so the steps it calls free are free here too. This gives a parity decision tree with affine leaves; following $x$ gives the bound on $C_{\rm aff}(f,x)$. ∎

**Theorem 1(c).** $\lambda\le\mathrm{MC}$ is known (Boyar–Find, https://arxiv.org/abs/1407.6169, Section 1.1, citing Boyar–Peralta 2008). Proof: go through the AND gates in topological order and fix one operand of each. That operand is affine on the current flat, so fixing it costs 0 or 1 equation and keeps the flat nonempty. For $D_{\rm aff}\le n-1$, query $x_1,\dots,x_{n-1}$: every function is affine on a line. ∎

The straight-line case of Theorem 1(a) with $\kappa(\mathrm{ADD},k)\le h-\lfloor h/2^k\rfloor$ reproduces the journal's bound $m\le\sum_j(h-\lfloor h/2^{k_j}\rfloor)$ exactly, because $\lambda(\mathrm{IP}_m)=m$ by polar rank.

**Theorem 2.** Substitute an optimal XOR/AND circuit for each operation. Affine wiring and fixed-address memory traffic are XOR, NOT and wires, which are free. ∎

**Proposition 3 (counterexample).** Take the one-instruction program "add two $w$-bit words and expose the top sum bit $s_{w-1}$."
- $s_{w-1}$ has algebraic degree $w$, so $\mathrm{MC}\ge w-1$ by Schnorr's degree bound.
- Ripple carry $c_{i+1}=(a_i+c_i)(b_i+c_i)+c_i$ uses $w-1$ ANDs, so $\mathrm{MC}(s_{w-1})=w-1$.
- Then $s\cdot\lfloor w/2\rfloor=\lfloor w/2\rfloor<w-1$ for $w\ge3$.
- Meanwhile $\lambda(s_{w-1})=1$: on $a_{w-2}+b_{w-2}=0$ the top carry equals $a_{w-2}$.

The journal's $\lfloor w/2\rfloor$ is a $\kappa$-capacity. It pairs with $\lambda$, not with MC. On the journal's inner-product families $\lambda=\mathrm{MC}=m$ (Mirwald–Schnorr), which is why the two readings agreed there.

**Proposition 4 (not found in any source consulted; priority is unestablished).**

*Upper bound.* Use $\mathrm{MUX}_k=M_0+i_{k}(M_0+M_1)$ recursively, where $M_0$ and $M_1$ are the two $\mathrm{MUX}_{k-1}$ halves. This gives $A(k)=2A(k-1)+1$, so $A(k)=2^k-1$.

*Lower bound.* This adapts the elimination of the independent-dot-product note. Take an $M$-AND circuit and let $Z$ be the set of still-free $T$-coordinates. [Independent dot product](adding-an-independent-dot-product-to-a-boolean-circuit.md)
1. Pick the earliest AND gate with an operand that has a direct $Z$-coefficient. Every earlier gate depends only on $i$, so that operand is $\ell(Z)+B(i)$ with $\ell\ne0$.
2. Branch on its value $c$. Solve for one coordinate of $Z$ and substitute it into the later gates and the output. The gate becomes constant or a copy, so delete it. Each step removes one gate and one $Z$-coordinate, and every remaining assignment of $(Z,i)$ stays admissible.
3. Stop when no AND gate depends on $Z$. The output is then $\langle\alpha,Z\rangle+H(i)$ with $\alpha$ constant.

For each $i$ whose coordinate $T_i$ is still free, the true function restricted to fixed $i$ has $Z$-linear part $e_i$. Two free coordinates $i\ne j$ would force $e_i=\alpha=e_j$. So at most one coordinate stays free, there are at least $2^k-1$ steps, and $M\ge2^k-1$. ∎

*The RAM side.* One indirect load at address $\mathrm{base}\oplus i$ has address width $k\le w$. After branching on the $k$ bits of $i$, the address is known and the load is free in the journal's convention. Both programs have $s_S=s_J=1$ (load) or $s_S=s_J=k$ (branches). So under indirect addressing a single charged step can carry MC $2^k-1$, for any $k\le w$ with $2^k+k\le N$, and that is about $N/2$ at the largest such $k$. No inequality $\mathrm{MC}(f)\le s\cdot\mu(w)$ with $\mu$ polynomial in $w$ holds for non-oblivious programs, under either count.

*Context (from an independent literature search during review; not rechecked here).*
- That search found no statement of $\mathrm{MC}(\mathrm{MUX}_k)=2^k-1$ in Boyar–Find 2018, in Häner 2023's list of function classes with known exact MC, or elsewhere.
- The only multiplexer lower bounds found were full-basis or De Morgan size bounds (Paul's bound of about $2N$, seen only in search snippets).
- The same elimination proves a column-rank principle. If $f(T,i)$ is affine in $T$ for each fixed $i$, with linear part $\ell_i$, then $\mathrm{MC}(f)\ge\dim\operatorname{span}\{\ell_i-\ell_{i_0}\}$. Reason: at a leaf, $T=LZ+b(i)$ with $L$ injective and independent of $i$, so the image of $L$ lies in the common kernel of the $\ell_i-\ell_{i_0}$. This was checked exhaustively at $n=4$ and on 60 random 6-variable instances during review.

**$\lambda(\mathrm{MUX}_k)=k$ for every $k\ge1$** (a manuscript proof contributed during review; the exhaustive $\lambda(\mathrm{MUX}_2)=2$ agrees).
- Upper bound: fixing the index gives $\le k$.
- Lower bound: suppose $\mathrm{MUX}_k$ is affine on $a+V$. Let $V_I$ be the projection of $V$ to the index coordinates, of dimension $d$, and let $I=i_0+V_I$ be the set of indices on the flat. Take $v\in V$ with zero index part and any $u\in V$. Then $D_uD_v\mathrm{MUX}_k(T,i)=v_T(i)+v_T(i+u_I)$, which must vanish for all $i\in I$, so $v_T$ is constant on $I$. The vectors of $V$ with zero index part therefore have dimension at most $(2^k-2^d)+1$. Hence $\dim V\le d+(2^k-2^d)+1$, and the codimension is at least $k+2^d-1-d\ge k$. ∎

So in the codimension measure, the indirect load costs exactly its address width, while in MC it costs $2^k-1$.

### Capacities, checked against the journal

| instruction (outputs used) | $\kappa$ (pairs with $\lambda$) | $\mu$ (pairs with MC) |
|---|---|---|
| ADD$_w$, one scalar (straight-line model) | $\lfloor w/2\rfloor$ (journal, Lean) | $w-1$ (top bit) |
| ADD$_w$, $k$ scalars | $\le (w-1)-\lfloor (w-1)/2^k\rfloor$ (journal) | $\le w-1$ |
| ADD$_w$, whole word | $w-1$ (journal) | $w-1$ |
| AND$_w$ | $w$ (journal) | $w$ |
| MUL$_w$, low word | $\le 2w$ (freeze both operands) | $O(w^2)$ (schoolbook; one AND per adder) |
| indirect load, $k\le w$ address bits | $\le k$ | up to $2^k-1$; no bound polynomial in $w$ |
| zero-test branch | 1 (existential), $\le w$ (through $x$) | no bound in $w$ ($k$ branches give MUX$_k$) |

Exact $\kappa$ and $\mu$ for MUL$_w$ were not determined.

### Computations

All commands run from `audits/`. The census program is compiled once with `c++ -O2 -std=c++17 mc_and_affine_codimension_census.cpp -o /tmp/mc-lambda`. Each run takes a few seconds. [mc_and_affine_codimension_census.cpp](../audits/mc_and_affine_codimension_census.cpp) · [addition_capacity_and_multiplexer_checks.py](../audits/addition_capacity_and_multiplexer_checks.py) · [toy_ram_affine_flat_check.py](../audits/toy_ram_affine_flat_check.py)

**1. Exhaustive census of all 65,536 four-variable functions** (exact MC by search over spans, exact $\lambda$ over all 307 flats). Output abridged to the result lines:
```
$ /tmp/mc-lambda all4
MC distribution:  MC=0:32  MC=1:1120  MC=2:31616  MC=3:32768
lambda distribution:  lambda=0:32  lambda=1:50272  lambda=2:15232
joint (MC,lambda):  (0,0):32  (1,1):1120  (2,1):30720  (2,2):896  (3,1):18432  (3,2):14336
violations of lambda<=MC: 0 ; violations of lambda<=n-1: 0
violations of MC >= deg-1: 0
```
Internal consistency checks:
- $1120=35\cdot32$: the rank-2 quadratic classes times the affine functions.
- The MC=3 count, 32,768, equals the number of degree-4 functions.
- The maximum MC is 3, which agrees with the Turan–Peralta abstract.
- $\lambda$ can be far below MC: 18,432 functions have MC 3 and $\lambda=1$.

An independent census written during review (different flat enumeration and affinity test) reproduced the 307 flats, both distributions and the joint table exactly.

**2. Six-variable targets** (MC $\le2$ decided by exhaustion over all 2-AND circuits; $\lambda$ exact over all 26,387 flats). Output abridged (the per-mask lines of the scalar observables are omitted):
```
$ /tmp/mc-lambda targets6
MUX_2 (T0..T3=x0..x3, index x4+2x5)        degree=3  MC>2 (exhaustive over all 2-AND circuits)  lambda=2
top sum bit s2 of 3-bit addition           degree=3  MC=2  lambda=1
IP_3                                       degree=2  MC>2 (exhaustive over all 2-AND circuits)  lambda=3
IP_2 (positive control)                    degree=2  MC=2  lambda=2
max lambda over the 7 scalar observables of add3 (identity operands) = 1 (floor(w/2)=1)
```
What this shows:
- $\mathrm{MC}(\mathrm{MUX}_2)=3$, combining this exhaustion with the 3-AND circuit.
- The Proposition 3 counterexample is checked at $w=3$: MC 2 > 1·1.
- The scalar capacity at $w=3$ with identity operands is 1. The journal's audit already covers all 26,387 operand flats.

**3. Random oblivious straight-line programs** ($n=4$, $w=2$, 1–3 instructions of ADD$_2$/AND$_2$, random affine wiring, exact MC from the census).
```
$ /tmp/mc-lambda slp4
slp4: 200000 random straight-line programs; violations MC(f)<=sum mu: 0; lambda(f)<=sum kappa: 0; tight MC: 22106; tight lambda: 16383
```

**4. Widths 2–8, exhaustive over inputs.** Output abridged to three of its lines:
```
$ python3 addition_capacity_and_multiplexer_checks.py
w=8: degree(top bit)=8  => MC>=7; ripple carry with w-1=7 ANDs correct: True; top bit affine on flat a_(w-2)+b_(w-2)=0 (|flat|=32768=2^15): True; floor(w/2)=4
w=8: one addition computes IP_4 (m=floor(w/2)): True; one AND computes IP_8: True
k=4: n=20, recursive circuit correct: True, ANDs=15 (=2^k-1=15), degree=None
```
Every $w=2,\dots,8$ line is True, with degree(top bit) $=w$. The even-lane packing reproduces the journal's $\lfloor w/2\rfloor$ and $w$ attainments. The $\mathrm{MUX}_k$ circuits are correct for $k=1..4$, with degree $k+1$ for $k\le3$.

**5. Theorem 1 with branches and indirect addressing on a toy RAM.** The script's "charged" counts every executed AND/ADD, and every BRZ/LD/ST whose control or address is not constant on the current flat. What it verifies is $\operatorname{codim}F\le\sum_t c(t)$, with each $c(t)\le w$. A step with $c(t)>0$ is nonconstant on $F$, which lies inside the path cell, so that step is counted in $s_S$. The toy instruction set is ADD, AND, XOR, XORI, ANDI (constant mask), shifts by constants, BRZ, LD/ST with computed addresses, and LDI/STI. The executor is symbolic over affine forms. Each check is verified by brute force over all $2^n$ inputs:
- every input in $F$ follows the same PC trace;
- the program's output equals the symbolic affine output on $F$;
- $\operatorname{codim}F\le\sum c\le w\cdot\#\text{charged}$.

Output abridged (the two $\mathrm{MUX}_2$ lines are omitted):
```
$ python3 toy_ram_affine_flat_check.py
random programs: {'programs': 400, 'exist_ok': 400, 'thru_checks': 2400, 'thru_ok': 2400, 'max_ratio': 1.0, 'max_codim': 8, 'bound_ok': True}
existential charged-count histogram: {1: 5, 2: 43, 3: 50, 4: 69, 5: 75, 6: 63, 7: 44, 8: 25, 9: 13, 10: 7, 11: 3, 12: 3}
MUX_3 via one indirect load (w=8, n=11): computes MUX: True; existential path: charged=1, codim=3, verified=True; max charged over all inputs=1; MC(MUX_3)=2^k-1=7
MUX_3 via k one-bit branches (w=8, n=11): computes MUX: True; existential path: charged=3, codim=3, verified=True; max charged over all inputs=3; MC(MUX_3)=2^k-1=7
```
The demos use $w=8$, and the concrete interpreter masks every immediate to $w$ bits; with $w=3$ the base address 64 of the indirect-load demo would not fit in a word.

### Consequence for the line, with sources

1. **Codimension form.** Theorems 1 and 1′ are the forms that cover branches, loads, stores and indirect addressing. They are also the forms in which the journal's capacity results are proved (codimension or parity-decision depth). From them, $s_S\ge\lambda(f)/c^*$ and $s_J\ge(C_{\rm aff}(f,x)-1)/(rw)$, and both $\lambda$ and $C_{\rm aff}$ are at most $n-1$. So no derived bound exceeds about $n/c^*$ charged steps:
   - with a full-word ADD or AND, this is at most $(n-1)/(w-1)$, about one packed scan;
   - in the straight-line model with scalar-exposed additions only, it is at most $(n-1)/\lfloor w/2\rfloor$;
   - with any per-step capacity of at least 1, it is at most $n-1$ steps.

   This holds for every Boolean function. No circuit lower bound would lift it. The per-input form ($C_{\rm aff}$, $D_{\rm aff}\le n-1$) has the same cap; it is the journal's own remark that certificate codimension cannot exceed $N$.
2. **MC form.** Only Theorem 2 can exceed $n$, and only for oblivious code under the structural count, where every executed nonlinear instruction is charged.
   - With $\mu_{\max}=\Theta(w)$ (ADD, AND, comparisons; $O(w^2)$ with MUL), a lower bound of $\omega(N/w)$ charged steps obtained from Theorem 2 needs $\mathrm{MC}=\omega(N)$ for the verdict restricted to the hard family.
   - A lower bound of $\omega(N)$ steps, the real linear target, needs $\mathrm{MC}=\omega(N\log N)$ (with $\mu_{\max}=\Theta(w)$ and $w=\Theta(\log N)$).
   - An affine restriction cannot raise MC, so this means superlinear MC for SAT$_N$ itself.
   - As of Boyar–Find, no explicit *family* of single-output functions was known with MC $\ge n$ for all large $n$, and a limited search during review found nothing newer.
     - Boyar and Find (https://arxiv.org/abs/1407.6169, Section 3; TCS 720 (2018)) note that no concrete $(n,1)$-function had been shown to need more than $n-1$ AND gates.
     - The degree bound gives $n-1$ for degree-$n$ functions.
     - Exhaustive search gives isolated small exceptions: Çalık, Sönmez Turan and Peralta (Cryptogr. Commun. 11 (2019)) exhibit 6-variable functions with MC 6.
     - Other exact linear values are $n/2$ for IP (Mirwald–Schnorr) and $2^k-1=n-k-1$ for MUX (Proposition 4).
   - $\mathrm{MC}\le$ (size over the full binary basis): each non-affine binary gate is one AND up to affine maps. So superlinear MC would be a superlinear explicit circuit lower bound, beyond the best known $(3.1-o(1))n$.
3. **Non-oblivious RAMs.** Proposition 4 rules out any per-step MC capacity polynomial in $w$. Making memory oblivious (sorting networks) charges every one of the $T$ steps. That is a circuit-simulation route, not a capacity argument.

Sources (primary literature only; access status as stated):
- C. P. Schnorr, *The multiplicative complexity of Boolean functions*, AAECC-6, LNCS 357 (1989) 45–58: not accessed. The degree bound MC ≥ deg − 1 is quoted from secondary snippets (Boyar–Find TCS 2018; a 2010 Kulikov talk saying $n-1$ is the best known explicit MC lower bound, which isolated small cases such as MC 6 at $n=6$ have since exceeded; see Çalık et al. below), and was re-derived during review.
- J. Boyar, R. Peralta, D. Pochuev, TCS 235 (2000) 43–57: not accessed (citation from search snippets; for almost all functions MC ≥ $2^{n/2}-O(n)$, as quoted by Boyar–Find).
- M. Mirwald, C. P. Schnorr, TCS 102 (1992) 307–328: not accessed (the journal's own citation).
- J. Boyar, M. G. Find, *Multiplicative complexity of vector valued Boolean functions*, https://arxiv.org/abs/1407.6169 / TCS 720 (2018): abstract and snippets only for this note; passages of Sections 1–3 were read during review. They give an $(n,n)$-function with MC ≥ $2n-3$, which is multi-output; T. Häner, https://arxiv.org/abs/2307.07424 (abstract only), shows it is exactly $2n-3$.
- J. Boyar, M. G. Find, R. Peralta, *On various nonlinearity measures for Boolean functions*, Cryptogr. Commun. 8 (2016) 313–330: abstract only.
- M. S. Turan, R. Peralta, *The multiplicative complexity of Boolean functions on four and five variables*, LightSec 2014: abstract only (max MC is 3 for $n=4$ and 4 for $n=5$).
- Ç. Çalık, M. Sönmez Turan, R. Peralta, *The multiplicative complexity of 6-variable Boolean functions*, Cryptogr. Commun. 11 (2019) 93–107 (https://eprint.iacr.org/2018/002): not accessed for this note; its abstract ("specific 6-variable Boolean functions which have multiplicative complexity 6") was read during review.
- J. Li, T. Yang, *3.1n − o(n) circuit lower bounds for explicit functions*, STOC 2022 / https://eccc.weizmann.ac.il/report/2021/023/: abstract only. Find–Golovnev–Hirsch–Kulikov (FOCS 2016): not accessed.

## 4. The three standard tests

- **(a) Fast solver on the hard family?** No lower bound for SAT is claimed. The families where this line is exact (IP slices) have packed-scan solvers in $O(m/w+\log w)$ (journal). The theorem shows the line cannot exceed about one scan on *any* family.
- **(b) Same bound for an easy language?** Yes. The inequalities depend only on $\lambda$ or MC of the computed function, never on NP-hardness. $\mathrm{IP}_m$, which is trivially easy, has $\lambda=\mathrm{MC}=m$ and gets the same $\Omega(m/w)$. 2-SAT gets the same $n-1$ cap. The line does not separate SAT from easy languages.
- **(c) Relativized clock?** Both inequalities use bounded per-instruction capacity. An oracle query of the relativized-clock model reads $\Theta(n\log n)$ bits, so its $\kappa$ and $\mu$ are unbounded and the lower-bound use collapses. That is consistent with what the oracle model shows: a proof must use that one instruction reads $O(w)$ bits. The cap $\lambda\le n-1$ holds with or without oracles, so the retirement conclusion survives. [Relativized clock](relativized-clock.md)

## 5. Exact obstruction and next step

Two readings of the proposed inequality fail.
- **Every reading, with branches or indirect addressing.** This is Proposition 4.
- **The reading that uses the journal's "products per instruction" as an MC capacity.** This is Proposition 3. The journal's figure is a codimension capacity $\kappa$, and $\kappa<\mu$: $\lfloor w/2\rfloor$ against $w-1$ for an addition exposing one scalar.

The correct pairings are $\lambda\leftrightarrow\kappa$ (Theorem 1, structural count; Theorem 1′ with $rw$ for the freeze count) and $\mathrm{MC}\leftrightarrow\mu$ (Theorem 2, oblivious code, structural count only).

The line itself is obstructed in two ways:
- per-path measures are at most $n-1$;
- global MC measures need oblivious code and a new superlinear explicit circuit lower bound, and one charged indirect load can carry $2^k-1$ ANDs for every $k\le w$ with $2^k+k\le N$ (about $N/2$ at the largest such $k$).

A future instruction-level argument would need a measure that is neither path-local nor confined to oblivious code. Two kinds are known to grow past $n$: measures of total work after oblivious compilation, and space-time or memory-traffic measures. Neither is a capacity count.

A small follow-up: find out whether $\mathrm{MC}(\mathrm{MUX}_k)=2^k-1$ is already stated in the XAG-synthesis or quantum table-lookup (T-count) literature. No search was made there.

## 6. What is not proved

- No lower bound for SAT or for any language is proved.
- Under the journal's freeze count $s_J$, only the constant $rw$ is proved (Theorem 1′). The smaller per-step constants ($\kappa$, $w-1$, $w$, and 1 for zero tests) hold for the structural count $s_S$.
- Checked only at finite size:
  - the toy-RAM checks, which cover only the listed instruction set (no comparisons or multiplication);
  - the census, at $n=4$;
  - the targets, at $n=6$ and MC ≤ 2.
- Not determined: exact $\kappa$ and $\mu$ for multiplication and variable shifts (only $O(w^2)$ and $\le2w$ bounds are given).
- The statement that no explicit single-output *family* is known with MC $\ge n$ for all large $n$ rests on Boyar–Find (passages read during review, not for this note) and on limited searches. Isolated small exceptions exist (MC 6 at $n=6$, Çalık–Sönmez Turan–Peralta).
- Proposition 4's lower bound and $\lambda(\mathrm{MUX}_k)=k$ (the latter contributed during review) are manuscript proofs checked exhaustively only at $k=2$. $\mathrm{MC}(\mathrm{MUX}_2)=3$ was also confirmed with a SAT solver during review. Their priority is unknown.

## Reproducing the checks

From `audits/`:

```
c++ -O2 -std=c++17 mc_and_affine_codimension_census.cpp -o /tmp/mc-lambda
/tmp/mc-lambda all4
/tmp/mc-lambda targets6
/tmp/mc-lambda slp4
python3 addition_capacity_and_multiplexer_checks.py
python3 toy_ram_affine_flat_check.py
```

[mc_and_affine_codimension_census.cpp](../audits/mc_and_affine_codimension_census.cpp) · [addition_capacity_and_multiplexer_checks.py](../audits/addition_capacity_and_multiplexer_checks.py) · [toy_ram_affine_flat_check.py](../audits/toy_ram_affine_flat_check.py)
