# A compact approximation exists at some clock resolution

**Research journal, 24 November 2026.** Take the actual first-output times of the plain interpreter at one length $q$. Without deciding any SAT instance or making any distributional assumption about those times, one of a specified list of dyadic histograms admits an $o(K)$-bit description with $o(1)$ total absolute error, where $K$ counts its bins. A single fast algorithm decodes the description given the grid. The list contains $O((\log q)^{2/3})$ grids. Linear SAT would therefore imply a lower bound on selecting an accurate grid **before** most of the programs have run. [Forecaster theorem and model](causal-first-outputs.md)

## A finite approximation lemma

Let $\mu$ be any measure of total mass at most 1 on $F=2^{\lfloor p/2\rfloor}$ consecutive cells, where $p=\lfloor\log_2 q\rfloor$. At level $l$, use $K=2^l$ equal consecutive blocks of finest cells. A block of mass $u$ has density $x=Ku$ relative to the uniform probability measure on cells. The mean of all densities is at most 1. Under refinement the parent density is the arithmetic mean of its children's densities.

Start at $l_0=\lfloor p/4\rfloor$, then increase by $h=\max(1,\lfloor p^{1/3}\rfloor)$ until the next level would exceed $\lfloor p/2\rfloor$. There are $L=\Theta(p^{2/3})$ transitions. Use threshold $B=h$ and define the convex function
$$
 H_B(x)=\begin{cases} x^2 & x\le B,\\ 2Bx-B^2 & x>B.\end{cases}
$$
The mean energy $\mathbb E H_B(x)$ increases on refinement and is at most $2B$. For a parent density $y$ and child density $x$, the nonnegative residual $H_B(x)-H_B(y)-H'_B(y)(x-y)$ averages over the refinement to the energy increment. When both densities are at most $B$ the residual equals $(x-y)^2$. By telescoping there is a transition with increment at most $2B/L$. Write $J$ for its child indices where $x>B$ or $y>B$. Markov's inequality, once on children and once on parents with all their equal-size blocks of children, gives $|J|\le2K/B$. Cauchy–Schwarz gives
$$
 \frac1K\sum_{i\notin J}|x_i-y_i|\le\sqrt{2B/L}.
$$
Thus a histogram copy of the parent, corrected at every position in $J$, differs from the child by vanishing total mass. The linear extension in $H_B$ allows a single fine cell to carry nearly all the mass. The bounded-density energy increment is classical. [Tao's dyadic energy argument](https://terrytao.wordpress.com/2007/06/18/the-lebesgue-differentiation-theorem-and-the-szemeredi-regularity-lemma/) · [Exact-rational checks](../audits/regular_histogram_experiment.py)

## Bit cost and timing

There are $A=K/2^h$ parents. Let $d=\max(1,\lfloor p^{1/12}\rfloor)$ and let $J$ have size $r$. Round each parent *mass* down in multiples of $1/(Ad)$. The resulting vector of integer ticks has sum at most $Ad$ and is specifiable by an ordinal among $\binom{A+Ad}{A}$ weak compositions with slack. Spread its reconstructed mass equally among the children. Record the exceptional positions by an ordinal among $\binom Kr$ subsets. For $r>0$, round each exceptional child mass down in multiples of $1/(rd)$ and record its tick vector in the same manner. Overwrite those entries. The integer $r$ costs $O(\log(K+2))$ bits. Rounding contributes at most $2/d$ to total error. The total information in bits is at most
$$
 O\left(\log(K+2)+A\log(2+d)+r\log(2+d)+r\log(eK/r)\right)=o(K),
$$
with the final term zero for $r=0$. Indeed $r/K\le2/B\to0$ and $\log d=o(B)$. These bounds are uniform over measures. One can decode by enumeration: even listing all candidate vectors with coordinates at most $Kd$ costs $2^{O(K\log q)}=2^{o(q)}$ steps. Clip any entry above 1 and round each entry to $q$ binary fractional bits for the forecaster. The extra error is at most $K/2^q$.

The actual first-output measure places mass $(|E(t_{i+1})|-|E(t_i)|)/2^q$ on each finest cell using the cutoffs in the forecasting experiment. Larger cells then give exactly its true histograms at the corresponding grids. The lemma supplies accurate advice for a fast decoder at some level, regardless of the SAT hypothesis.

## What remains to select

The index of a good level requires only $\lceil\log_2(L+1)\rceil=O(\log\log q)$ bits if supplied externally. A fixed algorithm that selects such a level by time $2^q q^{O(1)}$ at infinitely many lengths would rule out linear SAT. Here “such a level” can mean one attaining the energy increment bound above. It also suffices that the histogram at the chosen levels has a fast, $o(K)$-bit approximation of vanishing error. The grid index controls the **producer of new outputs** as well as the forecaster. Adding it only to the advice of the forecaster leaves the producer on its original grid. Computing the energies directly uses the entire interval, which extends nearly to $2^{2q}$.

Two further checks investigate the possibility of finding the scale.

* A uniform random level has expected energy increment at most $2B/L$. Taking the threshold to be $(2B/L)^{1/2}$ shows that a fraction $1-O((B/L)^{1/2})$ of levels satisfy a bound still tending to zero. This gives a timely randomized choice with no success certificate. The forecasting implication uses a single fixed grid selected at each length.
* If one divides the fixed supply of decoder names equally among the $L$ levels, the guaranteed first-output mass at each level falls by a factor of $L$. The regularity estimate $O(\sqrt{B/L}+1/d)$ does not reach this smaller error. A family of dyadic measures with independent signs gives a quantitative obstruction even to improving the purely geometric estimate enough to pay the equal-share cost. The construction concerns general measures. Proving that actual program outputs have further structure would change the selection problem. [Cascade counterexample](cascade-allocation.md)

There is also a fixed-accuracy form. Given any fixed desired error $e>0$ and advice rate $c>0$, first take $d$ a sufficiently large constant to control rounding, then take $B$ a sufficiently large constant to make the exceptional-position and exceptional-mass encodings cost less than $cK/2$. The parent cost falls below the other $cK/2$ eventually. At most $O(B/e^2)$ levels have energy increment above $(e/2)^2$, regardless of $q$. This bounded number depends on the desired error and advice rate. The forecasting constants, in turn, depend on the program for choosing the grid. Interchanging those quantifiers would assert the missing conclusion. The cascade example can keep every member of a countable list of selectors inaccurate by a selector-dependent constant, even while almost every level is a uniform refinement.

Neither the scale selector nor the unrestricted SAT lower bound has been proved. The mathematical claims about the approximation are proved above. The numerical tests check finite instances, and the separate Lean formalization covers the online choice used in the conditional converse.
