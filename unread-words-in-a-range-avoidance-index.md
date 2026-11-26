# Unread words in a range-avoidance index

A single indexed family forces any deterministic algorithm that avoids its range on every input to read almost every input word. The exact number is $L-k+1$ when the index has $L$ complete words and the output occupies $k$ words, including its last partial word. The construction uses the classical Vandermonde generator matrix for a maximum-distance-separable code. [Reed–Solomon generator matrix, RFC 5510 §8.1](https://www.rfc-editor.org/rfc/rfc5510.html#section-8.1)

## The family

Fix a rational $0<\epsilon<1$. For index length $n\ge1$, let $w=\lceil\log_2(n+1)\rceil$, $L=\lfloor n/w\rfloor$, $m=\lfloor n^\epsilon\rfloor$, $s=\lfloor n^{\epsilon^2}\rfloor$, and $k=\lceil m/w\rceil$. The probe model exposes the $L$ aligned $w$-bit input words separately, and any remaining bits occupy a final padded cell. Let $F=\mathrm{GF}(2^w)$ and assign the first $L$ distinct elements in polynomial-basis order, $\alpha_1,\ldots,\alpha_L$, to the complete words $x_j\in F$. When $1\le k\le L$, define the field elements

$$
M_h(x)=\sum_{j=1}^{L}x_j\alpha_j^h,\qquad 0\le h<k.
$$

Here $\alpha_j^0=1$ includes $\alpha_j=0$. Form $H(x)$ from the first $m$ bits of $M_0,\ldots,M_{k-1}$, with each symbol written low coefficient first. Every $C_x:\{0,1\}^s\to\{0,1\}^m$ outputs just $H(x)$, ignoring the seed and the final padded cell. For exceptional lengths failing $1\le k\le L$, use the constant $0^m$; at length zero use the empty output. The displayed condition holds at every sufficiently large length.

A deterministic bit evaluator counts the input length, computes the parameters by integer arithmetic on fixed powers, and constructs $F$ using the first monic irreducible of degree $w$ over $\mathrm{GF}(2)$. Trial division by every monic polynomial of degree $1$ through $\lfloor w/2\rfloor$ tests each candidate with $O(w)$-bit polynomial registers. The two loops together use $2^{O(w)}=n^{O(1)}$ time. For a requested output bit the evaluator computes its one moment by repeated squaring and a scan of the complete words. These operations take polynomial time and $O(\operatorname{polylog} n)$ bits of workspace, hence $O(n^{\epsilon^2})$ bits for fixed $\epsilon$. A read-only tape suffices for the index.

## Exact threshold for an adaptive algorithm

Fix the values of any $L-t$ complete words, leaving $t$ free. The image of $H$ on these completions has exactly $2^{\min(m,tw)}$ elements. When $t\ge k$, any $k$ free positions give an invertible square Vandermonde matrix on rows $0,\ldots,k-1$. Their values can prescribe all $k$ moments, hence all $m$ retained bits. When $1\le t<k$, the first $t$ whole output symbols are retained. The Vandermonde matrix on those rows and all free positions is invertible, so distinct completions give distinct retained outputs. For $t=0$ there is one completion of the complete words and one output.

Suppose a deterministic algorithm returns an $m$-bit string $y$ on an input $x$ after leaving at least $k$ complete words unread. Change just those unread words to get $H(x')=y$. Every read on the original run has the same value, so induction on the executed instructions gives the same run and output on $x'$. Thus $A(x')\in\operatorname{Range}(C_{x'})$. This gives a hit at every length admitting even one such run. An algorithm that avoids the range on all inputs at that length must read at least $L-k+1$ distinct complete words on **each** input. The argument allows arbitrarily much computation and workspace between reads.

There is a matching algorithm. Leave any fixed set $U$ of $k-1$ complete words unread. Let $R(X)=\prod_{j\in U}(X-\alpha_j)=\sum_{h=0}^{k-1}r_hX^h$, taking $R=1$ for $U=\varnothing$. Read each other word once and compute $v=\sum_{j\notin U}x_j R(\alpha_j)$. Every completion satisfies

$$
\sum_{h=0}^{k-1}r_hM_h=v.
$$

Since $R$ is monic, completions with $M_0=\cdots=M_{k-2}=0$ must have $M_{k-1}=v$. Output $k-1$ zero symbols followed by the first $m-(k-1)w$ bits of $v+1$ (field addition). At least one bit of that last symbol is retained, and its low coefficient differs from that of $v$. The output avoids the range for every completion. Taking $U$ to consist of the last $k-1$ positions lets the algorithm compute each $R(\alpha_j)$ by iterating over those known addresses. This uses polynomial time and $O(\operatorname{polylog} n)$ workspace.

For this family a full scan also gives a fast avoider. XOR all complete input words to obtain $M_0$, output the complement of its low bit, and fill the remaining output bits with zeros. This takes $O(n/\log n)$ word operations with packed output, including its initialization. The unrestricted SAT time bound and the [infinitely-many-lengths avoidance premise](near-linear-sat-and-uniform-low-space-range-avoidance.md) for algorithms that inspect the entire input remain open. The [finite audit](unread_word_avoidance_audit.py) checks all fixed observations over four $\mathrm{GF}(4)$ symbols, all output lengths from one to eight bits, and the matching algorithm for every choice of unread set of size $k-1$.
