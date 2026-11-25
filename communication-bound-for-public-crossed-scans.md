# A direct SAT lower bound for a public scan with indirect writes

Consider a fixed deterministic controller with a constant number of logarithmic-width registers and arbitrary register computation. Its mutable memory has all $2^w$ addresses, including its input. Its successive memory operations have the following form. It reads $x_i=M[p_i]$ at $p_i=p_0+i d\pmod{2^w}$ for a fixed nonzero integer $d$. It may then write $M[x_i]\gets p_{i+\delta_i}$ for any adaptively selected $\delta_i\in\{0,\ldots,r\}$, or skip the write. The lookahead bound $r$ is fixed. The controller may branch, halt, and spend additional time computing in its registers. These reads and optional writes are its only access to the input and working memory. Public initial registers may depend on the length. A fixed number of preliminary arbitrary accesses is harmless if their addresses and payloads, along with the resulting register state, are communicated.

**Theorem.** Take the word-aligned little-endian DIMACS model with $w=16\lceil D\log_2(N+2)/16\rceil$ and fixed $D\ge1$. For every fixed correct controller of the specified type and every sufficiently large byte-aligned length $N$, there is a valid ASCII 3-CNF of length $N$ on which that controller takes at least

$$
\Omega_{D,d,r,\mathrm{controller}}\left(\frac{N^{D+1/2}}{(\log N)^{3/2}}\right)
$$

steps. All clauses have exactly three distinct variables. The grammar permits unused declared variables and whitespace between tokens. The decimal identifiers in the construction can have $O(\log^2 N)$ digits. A polynomial-identifier variant appears below. Adaptive offsets and skipped writes can depend on the data. The restriction on the RAM occurs at both the address of every read and the value of every write. [DIMACS Challenge suggested format, §2.1](https://www.cs.ubc.ca/~babic/doc/dimacs_cnf.pdf)

## Read pairs of an adaptive scan

Let $S$ be the address permutation $S(a)=a+d$, let $L$ be the period of the scan, and suppose a finite run performs $m>0$ reads. Write $P=\lceil m/L\rceil$ and let $H$ be the image of memory at scan initialization, of size $h$. Put

$$
B=rP,\qquad U=\bigcup_{s=0}^{rP} S^s(H).
$$

Call a read pair $(p_i,x_i)$ local when $x_i=S^b(p_i)$ for some integer $b$ with $|b|\le B$. Every pair is local or has an endpoint in $U$.

Indeed, a read whose word was last written by event $j<i$ has pair $F_j(p_j,x_j)$ for $F_j(a,b)=(b,S^{\delta_j}(a))$. A pair with no writer is $(a,h')$ for $h'\in H$. Follow the chain backwards and group links in twos from its current end. In a two-link group $u<j<v$,

$$
(p_v,x_v)=(S^{\delta_u}(p_u),S^{\delta_j}(x_u)),\qquad x_u=p_j.
$$

Call the group short when $v-u<L$. The positive integer $v-u$ is then the least nonnegative residue of $\delta_u$ modulo $L$, hence $v-u\le r$. The signed displacement of $x_v$ from $p_v$ has representative $\delta_j-(v-j)\in[-r,r]$. Each following two-link group changes a representative displacement by $\delta_j-\delta_u\in[-r,r]$ with that group's indices. After the most recent short group all groups are long. At most $P-1$ long groups fit, since their durations sum to at most $m-1<PL$. The current pair is therefore local. If there was no short group, there are at most $P-1$ two-link groups and possibly one unmatched link at the root. The root's coordinate in $H$ advances by at most $r$ per group and by at most $r$ on the unmatched link. It is still an endpoint, now in $U$. This also proves the dichotomy for targets outside the scan orbit. [Earlier zero- and one-offset ancestry bounds](ancestry-of-crossed-stores.md)

## Distributed simulation

Give Alice a physical address interval and Bob its complement. Each owns the initial words and the current contents at their addresses. In one complete orbit the owner changes at most $J=2|d|$ times, since the unwrapped sequence traverses the physical circle $|d|/\gcd(|d|,2^w)$ times and can cross each interval endpoint at most that often. This counting applies in both directions for all sufficiently large $w$. Partition the run into at most $JP+1$ maximal phases of one owner. If the scan orbit has one owner throughout, there is just one phase.

The active party simulates the controller and updates local memory. It buffers the last value written to each foreign address during that phase. Since every read until handoff is local, this exactly simulates the guest. At handoff send the registers, the next scan address, the control state, and the buffered address-value pairs. The other party applies these writes before resuming. A continuation bit delimits each record and the final answer costs one bit. The protocol communicates by bits only. Local running times convey no information. Computation, local storage, and preprocessing of the public layout are free in a deterministic communication protocol.

For a local pair that writes across the ownership cut, the destination lies within $B$ orbit steps of a change of owner. The union of these neighborhoods contains at most $(2B+2)J$ orbit addresses on a complete circle. Thus local writes cause $O_d(P(B+1))$ distinct phase-address records in total. For other pairs with destination in $U$ there are at most $(JP+1)|U|$ such records. All remaining pairs have their scan address in $U$, which accounts for at most $P|U|$ reads because each address is read at most once per pass. The protocol need not know $H,U,B$ to batch its messages. Including the registers, its bit cost is at most

$$
O_d\big((r+1)(P+1)^2(h+1)w\big).
$$

If a controller fails to halt on a valid input its worst-case time is already unbounded. For halting controllers one can use the maximum pass count for the public length family to bound this protocol on every pair of private inputs.

## A constant word alphabet for deterministic equality

Fix a sufficiently large byte-aligned target length $N$ and let $W=w/8$. Set $k=\lfloor N/(C_D(\log_2 N)^2)\rfloor$ with a sufficiently large fixed $C_D$. Use $K=\lceil\log_2(k+3)\rceil$ binary digits per index. Reserve distinct identifiers for $x_1,\ldots,x_k,u,v$ in $[1,2^K-1]$. The decimal name of an index begins with the digit `1` and appends, for each binary digit $b$, a string of $W-1$ zero digits followed by $b$. The name is positive and the map is injective. Declare the image of the all-ones index in the header.

After the public header pad with whitespace up to a word boundary. Each literal starts on a word boundary with one block of $W-2$ spaces, its sign (a space or minus), and the initial digit `1`. Each selected binary digit then contributes one aligned block. Adjacent literals are separated by the next literal's leading whitespace. End a clause with a block containing a space, `0`, a newline, and enough spaces to finish the block. For large lengths $W\ge3$. The header contains the repeated digit block of the largest identifier. All fully interior aligned header words in that repeated region are identical, even when its first digit block is unaligned. The clause count, fixed prefix, and two ends of that region affect only $O_D(1)$ other words since the clause count has $O(\log N)$ decimal digits. Padding and uninitialized memory add only constantly many words. Consequently the image of the entire initial memory has $h=O_D(1)$ independent of $k$ and both private strings.

For Alice's $k$-bit string $a$, let $\ell_i$ be $x_i$ if $a_i=1$ and $\neg x_i$ otherwise. Use four clauses per index, all forms $(\ell_i\lor (\pm u)\lor(\pm v))$. Their conjunction forces exactly $\ell_i$ on this variable. Bob's half uses the same construction on its string $b$. The resulting $8k$ proper clauses are jointly satisfiable exactly when $a=b$. The fixed stride places the boundary between the parties at a publicly known word boundary. Extra trailing whitespace pads the file to the target length. Make its last byte a newline for a line-terminated file. The body uses $8k(3(K+1)+1)W$ bytes, and the header uses $O(KW+\log k)$. Thus the construction fits in $N/8$ bytes for the declared choice of $C_D$. Give Alice the word-address interval from zero through her half, and Bob every other address. They can initialize their stores independently.

Every deterministic equality protocol has worst-case communication at least $k$ bits. Indeed each transcript defines a rectangle, and an accepting rectangle containing two distinct diagonal pairs would contain an unequal pair. Thus the protocol has at least $2^k$ accepting leaves. With $h=O_D(1)$ the simulation gives $P_{\max}=\Omega(\sqrt{k/w})=\Omega_D(\sqrt N/(\log N)^{3/2})$. The run attaining this pass count makes more than $(P_{\max}-1)L$ reads, and $L=2^w/\gcd(2^w,|d|)\ge N^D/|d|$. This proves the theorem. Checking the full equality matrix is unnecessary since the diagonal rectangle argument works for every $k$.

If one imposes polynomially bounded variable identifiers, fix an integer spacing $t$ in place of $W$ in the name. Use the fixed-stride clause layout in the sparse-decimal note, fill excess whitespace, and let $k=\Theta(N/\log N)$. Move the party boundary to the nearest word boundary by inserting fewer than $W$ spaces. Then $h\le N^{D/(8t)+o(1)}$, and the same proof excludes time $O(N^c)$ for every fixed $c<D+1/2$ by choosing sufficiently large fixed $t$. The polynomial bound on identifiers may depend on $t$. [Sparse decimal renaming](sparse-decimal-names-in-dimacs.md)

Streaming lower bounds via communication predate this application. Prior work also studies sequential read/write streams and the cost of reversing or sorting them. The crossed scan here reads in public order and may write anywhere using the value just read as its address. The pass bound above uses the last-writer dichotomy for that indirect operation. Priority of this specific result is undetermined. [François, Jain and Magniez, unidirectional streaming](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX-RANDOM.2014.654)

The Lean file verifies root-coordinate transport through arbitrary bounded offsets, the signed displacement after a short group, its growth through subsequent groups, and the count of disjoint long groups. The communication protocol and the equality reduction have manuscript proofs. The executable checks 10,125 exhaustive small traces, 3,000 additional adaptive runs with positive and negative strides, and satisfiability of 252 explicit properly ternary formulas against equality. [Lean arithmetic and ancestry lemmas](AdaptiveCrossedCommunication.lean) · [Executable independent checks](public_crossed_communication_audit.py)

## A control experiment when arbitrary words can be written

Even with the same public read order and the same indirect destination $M[x_i]$, two passes can transmit $k$ bits of deterministic equality if the **payload** is unrestricted. On this abstract memory test put $(A_i,\beta_i,\gamma_i)$ in consecutive triples on Alice's side, where $A_i$ is an original bit and the Greek letters denote physical scratch addresses. Bob has consecutive pairs consisting of his original bit and scratch address $\delta_i$. Give the first $\beta$ cell the public initial value $\gamma_1$. Other scratch starts at zero, so the original word alphabet has constant size. The orbit is scanned by increments of one, with unused positions skipped for writing.

In pass one, when reading $\beta_i$ the returned value is $\gamma_i$. Write $\beta_{i+1}$ into that cell. When reading $\gamma_i$, write $\gamma_{i+1}$ into $\beta_{i+1}$. Stop this construction at the last pair; it leaves $M[\beta_i]=\gamma_i$ for every $i$ and preserves the private data. In pass two remember $A_i$ in a register. At $\beta_i$ write $\delta_i$ into $\gamma_i$, and at $\gamma_i$ write $A_i$ into $\delta_i$. Later in the same pass compare Bob's bits with the delivered ones. All physical indices are fixed-stride functions of $i$, so a constant-register controller suffices. This example has constant pass count and $k$ bits of communication despite a constant initial alphabet. It refutes the proposed extension of the communication bound to arbitrary STORE payloads. The example is an equality layout, not a general DIMACS solver.
