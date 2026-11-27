# How many distinct small addresses can shifts and multiplication supply?

Consider the first-producer argument for a fixed program on the homogeneous physical DIMACS files. Put $U=2^w$, choose $\ell$ so that the positive marked interval $I$ is contained in $[0,2^\ell)$, and write $D_0=2^\ell=\Theta(m)$. Here $m\le O(U/w)$, $w=\Theta(\log m)$ and $w-\ell\to\infty$. The following estimates bound numerical *values*, so a covered address accounts for at most one chosen first-production instruction. [Machine, construction, and first-use charging](generating-fresh-addresses-on-one-native-sat-file.md)

## A count that avoids three positions

Choose the shift count $r=A\bmod w$ at circular distance at least $\delta w$ from each of $0$, $w/2$ and $w-\ell$, for a fixed $\delta>0$. This is feasible within the physical record. For example, offer digits $d\in\{6,7,8,9\}$ at the same byte $k$. Pin the selected digit and its companion 1 false, 4 true, and 5 false, using auxiliaries 2 and 3. Choose $w/32768<256^k\le w/128$ and $k\ge1$ at large widths. As $d$ ranges over the four options their residues differ by integer multiples of $256^k$. They lie in a circular arc of length at most $3w/128$ and have pairwise circular distances greater than $w/32768$. With $\delta=1/100000$, each of the three excluded arcs can remove at most one choice, leaving at least one. All prescribed names and public clauses are constant in number. The remaining bytes are the original space-filled template.

The forward rotations are cyclic left shifts. For every fixed $y$ let $S=y\mathbin{\texttt{>>}}r$ be its unsigned logical right shift, and let $P,Q$ be its left and right rotations by $r$. Arithmetic right shift supplies the same result as $S$ on nonnegative words; on negative words its result is negative and too large to be in $I$. Say an address is small if its top $w-\ell$ bits vanish. There is a set $Z$ of $o(m)$ values, independent of $y$, such that **at most one distinct value among $S,P,Q$ is both small and outside $Z$**.

1. If both $P$ and $Q$ are small, one is a rotation of the other by $2r$. The high zero intervals before and after that latter rotation require at least $s=\min(\ell,w-\ell,\operatorname{dist}(2r,w\mathbb Z))$ extra fixed positions beyond the first interval. There are at most $2^{\ell-s}$ possible assignments. Both outputs together have at most $2\cdot 2^{\ell-s}=o(m)$ possible values, since $r$ avoids $0$ and $w/2$.
2. If $r>w-\ell$, then $S<2^{w-r}\le 2^{\ell-\delta w}$. All these $S$ belong in $Z$. Otherwise $r\le w-\ell-\delta w$. When $Q$ is small, all bits that right rotation wraps from below $r$ into positions starting at $w-r\ge\ell$ must be zero. Hence $Q=S$.
3. Remain in $r\le w-\ell-\delta w$, and suppose $S,P$ are small. Number bits from zero. Small $S$ forces $y$ to vanish from position $\ell+r$ through $w-1$. Small $P$ restricts the possible nonzero bits of $y$ to $J=[-r,\ell-r)\pmod w$. If $r<\ell$, $J$ contains the final interval $[w-r,w)$, of which at least $\min(r,w-\ell-r)\ge\delta w$ bits must vanish. Thus the possible $P$ have cardinality at most $2^{\ell-\delta w}$. If $r\ge\ell$, then $J=[w-r,w-r+\ell)$. For $r<w/2$, its intersection with $[\ell+r,w)$ has size $\min(\ell,w-2r)$, tending to infinity, so the possible $P$ again belong to an $o(m)$ set. For $r>w/2$, all of $y$ is below bit $w-r+\ell$, so $S<2^{\max(0,\ell-(2r-w))}$, putting these $S$ in $Z$. Rounding any displayed real cutoff to integers changes constants only.

Taking the union of the indicated sparse sets proves the claim. Left shifts by $r$ into $I$ supply multiples of $2^r$ and add only $o(m)$ values. Shifting raw $A$ as the data rather than as the count gives $O(w)$ values, and the full-count operations with $A$ in the count position saturate equally at $A$ and $B$.

## The modular product on each short interval

The raw word has low byte space and high byte the digit $\texttt{4}$. All other bytes are spaces except for the fixed string beginning at byte $k$, namely a digit $d$, a space, the digit $\texttt{1}$, a space, the digit $\texttt{0}$, and newline. With a zero-based byte index and little-endian interpretation, write

$$
 A=32\frac{256^{W}-1}{255}+(52-32)256^{W-1}+256^k v_d,\qquad W=w/8.
$$

Here $v_d$ is the signed integer difference between that six-byte string and six space bytes; it is nonzero since the highest changed byte is newline. With $D=255\cdot256$ this gives $DA=aU+e$, where $a=52\cdot255+32$ and $e=D256^k v_d-8192$. In particular $|e|=\Theta(w)$ uniformly for our finitely many digits and $e\ne0$ at large widths.

Fix any interval $K$ of at most $C m$ consecutive word values for fixed $C$. If $Ay\bmod U=t$ is small, then $ey\equiv Dt\pmod U$ and $0\le Dt< D2^\ell$. As $y$ ranges in $K$, the segment of integers $ey$ spans $O(|e|m)=O(U)$. It meets only $O(1)$ of the translated intervals $jU+[0,D2^\ell)$ for all sufficiently large widths, since $D2^\ell=o(U)$. Each meets the progression $ey$ in at most $1+D2^\ell/|e|=o(m)$ values. Thus only $o(m)$ multiplications land at small outputs across *all* $y$ in $K$. This includes the case where $e$ is negative. An interval wrapping modulo $U$ can be split into two.

## Applying both estimates to the same outside operand

Small OR is impossible because it retains $A$'s high set bit. AND can yield at most $2^{\operatorname{popcount}(A\bmod 2^\ell)}=o(m)$ small values globally; all ASCII bytes have their high bit zero. If $A\mathbin{\texttt{xor}}y$, either subtraction, or the modular sum lies below $2^\ell$, then $y$ lies within $2^\ell$ of $A$ or $-A$ modulo $U$. Treat $I$ and these two neighborhoods separately, each an interval or union of a bounded number of intervals of length $O(m)$.

In each of those intervals the preceding product bound is $o(m)$. Ordinary right shift of the interval gives $O(1+m/2^r)=o(m)$ distinct values. For a rotation, cover the interval by constantly many aligned blocks of length $2^\ell$. Each such block fixes the high $w-\ell$ bits to one specific pattern. Requiring the rotated output to be small fixes another cyclic interval of that length. Consistent assignments have at least $\min(r,w-r,\ell,w-\ell)$ additional fixed bits. Consequently the small rotated outputs from these intervals contribute only $o(m)$ distinct values, even when the fixed pattern of their input block contains ones. For $y\in I$ the ordinary arithmetic results are large or insensitive. For $y$ in the neighborhood of $A$, small XOR and at most one direction of subtraction remain possible. For $y$ in the neighborhood of $-A$, only addition can be small. The neighborhoods are disjoint for large $w$ since $A/U\to(52+32/255)/256$ stays away from zero and one half.

For every remaining outside partner $y$, the ordinary addition, subtraction, and XOR outputs are large. Modulo shifts and rotations with $A$ as the count supply at most one distinct small address outside the fixed $o(m)$ exceptions, by the first section. Multiplication $Ay$ supplies at most one more small address for this $y$. Altogether each outside partner gives at most two distinct first-produced addresses in addition to $o(m)$ exceptional addresses shared by the entire execution. Each selected first producer receives at most one effective-source charge except for the $O(1)$ results $f(A,A)$.

If $E$ counts the instructions outside the $m$ original loads and the first producers of previously unavailable marked addresses, and $h$ the number of genuinely new outside numerical values, then $h\le E$. The $E$ slots receive at most $2E-h+O(1)$ charges, and the $h+O_P(1)$ outside partners give the inequality

$$
 m\le 2E-h+2h+o(m)+O_P(1)\le3E+o(m)+O_P(1).
$$

Therefore **every fixed correct program takes at least $(7/3-o(1))m$ native instructions** on this ordinary well-formed DIMACS family, under the specified separate-operation model and logarithmic word-width conventions. The count is per packed word and the same promise has a uniform $(3+\epsilon)m+o(m)$ upper bound for every fixed $\epsilon>0$. [Finite cyclic-interval and product audit](small_address_image_audit.py)
