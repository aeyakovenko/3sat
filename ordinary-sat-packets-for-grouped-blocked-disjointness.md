# Ordinary SAT packets for a grouped blocked-disjointness query

Take a Boolean database $A$ with $L$ rows of $B$ bits, and partition the rows into $Q$ consecutive groups of $P=L/Q$ rows. Here $L,Q,B$ are powers of two, $1\le Q\le L$, and $B\ge2$. A query gives a group $j$ and a column $v_p$ for each of its $P$ positions. Define
$$
             H(A,j,v)=\bigvee_{p=0}^{P-1} A_{jP+p,v_p}.
$$
The construction produces proper ordinary DIMACS 3-CNFs of one public length. The file with tag $t$ is satisfiable exactly when $H(A,j,v)=t$. The two possible files for each database and query differ in one physical bit. Every aligned word, including the header word, can carry that tag, any query packet, or any data packet.

Let $m=\log_2 Q+P\log_2 B$. Choose an integer block width $1\le b\le m$, and set $R=\lceil m/b\rceil$. There are exactly $LB$ distinct actual database packets and $R$ independent query packets. One packet suffices for the tag. The proper-clause count is
$$
                     O(LB+R2^b b).
$$
All variables, headers, public program clauses, word widths, packet counts and admissible slot addresses are determined from $L,Q,B,b$. In particular neither row sparsity nor the answer changes the file length. [Physical compiler and finite tests](grouped_blsd_sat_packets.py)

## The Boolean relation and both signs

Three distinct anchors numbered 1, 2 and 3 are forced false by the seven proper clauses excluding each other assignment to their triple. Data bit $i$ has its own variable $D_i$ and movable clause $(D_i,1,2)$ or $(-D_i,1,2)$. One such clause fixes its actual Boolean value. Distinct bit positions always have distinct packets.

Write the group bits first, least significant first, then the $P$ separate column indices in the same bit order. For each consecutive block $r$ of $b_r\le b$ bits give each possible value $u<2^{b_r}$ a unique token variable $K_{r,u}$. Its public clauses imply all $b_r$ designated bit literals when $K_{r,u}$ is true. An implication is a binary clause padded by a false anchor. The one movable packet for this block is the positive clause $(K_{r,u},1,2)$. All other tokens of the block may be assigned false. All combinations of values in different blocks are legal, including blocks that cross two fields. No query-bit occurrence is printed twice in private words.

For each position $p$ in a group, decode its column bits by a binary tree into $B$ one-hot masks. At the first bit the two masks are just its opposite literals. Each additional bit splits every previous mask by a conjunction with either sign of the new bit. These $P$ mask libraries are shared across **all** $Q$ groups. Fewer than $2PB$ conjunction gates suffice. For each actual data bit take its AND with the appropriate position mask. In each group OR its $PB$ terms in a binary tree. Finally select one resulting group bit by a binary multiplexer tree controlled by the group bits. This adds $LB$ pairwise ANDs, $LB-Q$ ORs, and $Q-1$ multiplexers. Falsity padding gives three proper clauses per AND or OR; a binary multiplexer has four proper ternaries. The public packet-to-bit implications add $\sum_r b_r2^{b_r}$ clauses.

Force variable 4 equivalent to the negation of the selected output, and 5 equivalent to that output. The movable tag is $(4,1,2)$ or $(5,1,2)$. Given the forced input bits, every data gate and the two aliases have their intended values in every model. If the sign matches, setting the chosen tokens true and all other tokens false gives a satisfying extension by evaluating the gates. For the opposite sign the chosen alias is forced both true and false. This argument covers both $H=0$ and $H=1$, arbitrary database rows, and $Q=1$.

## Physical layout, including the header

Write $C$ for the number of public clauses. Set the slot count to
$$
         s=\max\{LB+R+1,\lceil C/24\rceil\}.
$$
For any excess slots add distinct always-satisfied movable clauses $(z,-1,2)$ with fresh markers $z$. They are additional public-value packets and carry no row bits. This convention supports oversized token libraries too.

Each physical slot has room for up to 24 complete public clauses and one movable clause. Slot zero also contains the actual DIMACS header, declaring the common maximum identifier and $C+s$ clauses. Put the public lines in fixed consecutive groups at their slot starts. Follow them by the chosen movable clause, padding with spaces before its final newline. Any permutation of the same movable inventory is legal.

Let $\ell$ be the least positive integer for which $2^\ell\ge1024\ell s+2$. Each word has $w=1024\ell$ bits and the encoded file length is $N=ws$. Minimality gives $\ell=\lceil\log_2(N+2)\rceil$. All allocated identifiers occur in the layout, so the maximum is at most $3(C+s)\le75s$; the clause count is at most $25s$. Their decimal spellings use at most $\ell$ characters. With the header included, 25 proper clauses need at most $77\ell+210$ bytes, within the available $128\ell$ bytes on these layouts. The file consists solely of complete aligned words. Switching the tag replaces ASCII `4` by `5` in the same literal field at the same byte offset. The padding and all other bits are identical.

On the scales $Q=L^\alpha$, $B=L^\beta$, $b=\lfloor\kappa\log_2 L\rfloor$ for fixed $0<\kappa<\alpha\le1$, $\beta>0$, with integral scales or the usual power-of-two rounding, the token library has
$$
 R2^b b=O((\log Q+P\log B+b)L^\kappa)=o(LB).
$$
For large $L$ there are at most $6PB+6LB+4Q+O(1)$ other public clauses. The cap 24 suffices with $s=LB+R+1$ and **zero filler packets**. Thus $N=\Theta(LB\log(LB))$ and, when $\alpha<1$, $R=\Theta(L^{1-\alpha})$ for fixed positive $\beta,\kappa$. These are encoded bits and actual unqueried words, respectively.

## Adaptive placement and the full disjointness predicate

Fix a database. As a deterministic correct SAT program first requests previously untouched slots, install the data packets in any fixed logical order, using the public prefix of the particular requested address. Include any filler in this data inventory. The first request after that inventory is used can receive the tag. Assign the remaining $R$ sorted physical slots to query blocks in order. This defines genuine complete files supplied at entry. On any partial prefix, a specified still-unread slot could carry the tag, with the other positions completed identically and arbitrary selected column indices. Its two tag values force opposite verdicts. A correct program cannot halt or destroy that unread slot before receiving its original value. Apply the last observation to the first attempted such write. Previously exposed values and their actual later overwrites remain part of the ordinary computation. The argument concerns a single prescribed execution ordering; simultaneous arrangements for several programs need their own proof.

For a full blocked-set query $v_0,\ldots,v_{L-1}$, restrict it to each consecutive group. The OR over the $Q$ grouped answers equals the full intersection predicate $\bigvee_i A_{i,v_i}$. Its complement is ordinary blocked set disjointness with one chosen element in each block. There is no assumption that the same group or columns work for all databases. The physical encoding gives this identity for every query, and it gives the two complementary tags separately for each group.

The audit compared 4,940 full queries with the OR of their group queries. It parsed 1,400 one-bit opposite-tag pairs, independently checked 160 physical verdicts with CaDiCaL, and exercised an adaptive placement including a tag in the header word. The layout is a reduction to the standard blocked set disjointness relation. [Pătraşcu, definition of Blocked-LSD and section 5](https://arxiv.org/pdf/1010.3783)
