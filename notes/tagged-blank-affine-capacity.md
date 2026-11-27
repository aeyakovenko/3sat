# Exact affine capacity of tables with a tagged blank

Take $Q=2^w$ real labels whose physical binary encodings fill an affine $w$-flat. The blank is one physical codeword outside this flat. Each table has $m$ ordered slots. A real label may occur at most $D$ times and blanks may repeat freely. Assume $D\ge1$ and put $H=DQ$. For $Q\ge2$ the largest dimension of a binary affine subspace of valid physical tables is

$$
\begin{cases}
\displaystyle \sum_{j=1}^w\min(m,H/2^j), & 0\le m\le H/2,\\[2mm]
H-2D+\lfloor 2m/Q\rfloor, & H/2\le m\le H,\\
H, & m\ge H.
\end{cases}
$$

The expressions at the endpoints agree. For $Q=1$ the answer is $\min(m,D)$. Without a blank the exact dimension is $\sum_{j=1}^w\min(m,H/2^j)$ for all $0\le m\le H$. These bounds concern affine subspaces of the physical table; arbitrary nonlinear encoders can have different capacities. [Injective-table result used for the matching construction](affine-injections-and-one-sided-validity.md)

## Real slots alone

More generally suppose the labels have integer capacities $D_y\ge0$ with total $L$. In an affine family on $n$ real slots, fix any table. At slot $i$ the labels available while holding every other slot fixed form an affine set of size $2^{d_i}$. Here $d_i$ is the dimension lost on deleting slot $i$. Each label $y$ belongs to at most $D_y$ such sets. Otherwise add to the fixed table all the single-slot changes which install $y$ in those slots. They have disjoint supports and belong to the translation space, producing an invalid table. Thus $\sum_i 2^{d_i}\le L$. Some slot costs at most $\min(w,\lfloor\log_2(L/n)\rfloor)$ dimensions to delete. The image has the same alphabet and capacities. Iterating and counting the pairs $(t,j)$ with $1\le t\le n$, $1\le j\le w$ and $2^jt\le L$ proves the upper bound

$$R_w(L,n)=\sum_{j=1}^w\min(n,\lfloor L/2^j\rfloor).$$

The case $n=0$ has dimension zero. For uniform capacities $D$, split $m$ slots as evenly as possible among $D$ independent injective tables, each drawing from all $Q$ labels. Each table on $k$ slots can attain $\sum_j\min(k,Q/2^j)$ using the binary tree construction in the linked note. For each integer cutoff $Q/2^j$, the group sizes all lie weakly on the same side of the cutoff, so their capped sizes sum to $\min(m,DQ/2^j)$. Independent table directions give the sum of the ranks. [Construction of the injective families](affine-injections-and-one-sided-validity.md)

## Which slots can be blank

Project the affine family onto one slot. Its image is affine. If the image contains both the blank and a real label, it consists of exactly those two points. Indeed an affine functional separating the blank from the entire flat of real labels takes the blank value on half the image. Only one allowed word has that value, so the image has size two. Such a slot carries one affine Boolean activity bit for its own fixed real label. All other slots either always hold a real label or are constant blanks.

Let $n$ slots always hold real labels. Project onto them and let $o$ be the dimension lost. The remaining varying coordinates are the optional activity bits. On the linear kernel of the projection choose $o$ of these bits that form a dual basis. Conditional on **any** fixed real table in the projected family, these bits run through all $2^o$ patterns. Set all of them to active simultaneously. If the chosen bits name label $y$ a total of $p_y$ times, every real table in the image respects the reduced capacity $D-p_y$. In particular $p_y\le D$, $o\le H$, and the reduced capacities total $H-o$. Applying the preceding real-slot argument to the image gives

$$\dim U\le o+\sum_{j=1}^w\min\left(n,\left\lfloor\frac{H-o}{2^j}\right\rfloor\right),\qquad n+o\le m.$$

If $m\le H/2$, the marginal increase of $R_w(H,t)$ is at least one for every integer $1\le t\le m$, due to its first summand. Hence $o+R_w(H-o,n)\le o+R_w(H,m-o)\le R_w(H,m)$. For any $m$, bounding the first minimum by the convex combination $(2/Q)n+(1-2/Q)(H-o)/2$, and the later ones by $(H-o)/2^j$, yields

$$\dim U\le o+\frac{2n}{Q}+(1-2/Q)(H-o)\le H-2D+2m/Q.$$

Bounding every minimum by $(H-o)/2^j$ also gives $\dim U\le H$. For $Q=1$ every variable slot is optional, so the simultaneous activation argument gives $o\le\min(m,D)$.

## Attainment in each range

For $m\le H/2$, use the real-slot construction. In the middle range put $s=\lfloor 2m/Q\rfloor-D$. Of $D$ independent groups, take $s$ groups with $Q$ slots toggling independently between blank and their own distinct real labels. Each other group uses $Q/2$ always-real slots and attains injective dimension $Q-1$. The groups together use $H/2+sQ/2\le m$ slots and supply dimension $sQ+(D-s)(Q-1)=H-2D+\lfloor2m/Q\rfloor$. Fill spare slots with constant blanks. If $m\ge H$, take $D$ entirely optional groups, giving $H$ independent bits. For $Q=1$ take $\min(m,D)$ optional slots.

If the physical label encoding has a different geometry, the row-image argument needs rechecking. For any embedding of $Q$ real words and one blank, singleton-slot changes still give $\sum_i(2^{d_i}-1)\le H$. At most one label per single-slot image is the blank. Successively deleting the cheapest slot gives the embedding-independent upper bound $\sum_{j\ge1}\min(m,\lfloor H/(2^j-1)\rfloor)$ by counting $(t,j)$ with $t(2^j-1)\le H$. In particular the bound is less than $1.607H$ for $H>0$ regardless of slot count. For the numerical constant sum through $j=12$ and bound the tail by $\sum_{j\ge13}2^{-j}/(1-2^{-13})$. The sharp formula above uses the tagged realization.

The audit exhausts all small affine flats up to a row permutation in 25 parameter triples and compares their largest dimensions with the formula. Its three checks for $Q=4$, $D=1$ around the transition give dimensions $3,3,4$ on two, three and four slots. It also checks 5,115 integer envelopes and the ranks of the matching group allocations through $Q=128$. The proof is independent of the enumeration. Priority for the exact tagged-blank capacity is unestablished. [Executable audit](../audits/tagged_blank_capacity_audit.py)
