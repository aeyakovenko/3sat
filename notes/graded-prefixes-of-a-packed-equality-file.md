# One packed SAT pair at every prefix with many unread query words

A single pair of opposite proper 3-CNF files has a lower bound on its remaining processing at **every** prefix of every program in a polynomial roster. Use the [packed equality construction](a-common-sat-pair-with-a-name-across-each-word-boundary.md). It has two aligned words per coordinate holding symbols of a database $a$ and query $x$ in a decimal identifier that crosses their boundary. There are $m$ coordinates, $K=10^{\lfloor\alpha\log_{10}m\rfloor}$ symbols, $0<\alpha<1/2$, and $N=\Theta(m\log m)$ physical bits. Equality and inequality tags differ in one bit. The database on both files is identical, and both queries are $x=a$. The tag address $T$ may be fixed in advance or chosen by the joint quota construction in the linked proof.

At a cut let $j$ be the number of original query words $X_i$ that a particular program has still not inspected. Data words $A_i$ may already have been inspected and processed arbitrarily. Take the unread query words as the holes in the native replay charge. Their direct read and subsequent use in register arithmetic can be free. Let $t$ count marked-operand arithmetic and branches, marked stores, and the distinct address or payload values of the remaining stores, exactly as in the [writable-memory replay](processing-after-the-database-packets-of-a-sat-file.md). Let $h$ bound the controller size, including the program counter, in words. Assume the linked roster's word width $W=\Theta(\log m)$, bounded instruction arity, $r=m^{O(1)}$ publicly known programs, and $h=\log^{O(1)}m$.

Put
$$
 \Delta_j=j\log_2 K-\log_2\binom mj.
$$
There are absolute positive constants $A,B$ for the fixed model such that, for a common choice of the pair, at **every** such prefix on both signs for every program,
$$
 t\ \ge\ \max\left\{0,\;\frac{\Delta_j}{A\log_2(m+2)}
       -B\left(K+h+1+\frac{\log_2(r+2)}{\log_2(m+2)}\right)\right\}.
$$
The same applies to every pair in a set containing at least half the database diagonals. It bounds the entire remaining continuation, even when a program is allowed unlimited time and storage before the chosen prefix.

Two ranges illustrate the bound. Fix $0<\delta<\alpha$. If $j\ge m^{1-\alpha+\delta}$, the remaining charge is $\Omega(j)$. Already at $j\ge(e+\epsilon)m/K$, for any fixed $\epsilon>0$, it is $\Omega(j/\log m)$. Here $e$ is Euler's number. Indeed $\log_2\binom mj\le j\log_2(em/j)$, so $\Delta_j\ge j\log_2(jK/(em))$. In the first range this is at least $j(\delta\log_2m-O(1))$; in the second it is at least $j\log_2(1+\epsilon/e)$. The overhead $(K+h)\log m$ is $o(m/K)$ since $\alpha<1/2$.

## Charging a cut even when the cut itself depends on the database

If a database violates the displayed bound anywhere, choose one witnessing program, tag and step on its diagonal. This choice can be different for each database. Write $H$ for the $j$ unread query sites at this prefix, $V=[m]\setminus H$. Global SAT correctness forces each $X_i$ to be read before it is overwritten on either diagonal. Changing one decimal digit there by a one-bit physical flip reverses the SAT answer while preserving the tag and other words. All of $H$ is therefore still original. With the actual $A$ and $X_V=a_V$ fixed, *every* replacement $x_H$ preserving the tag replays the chosen prefix exactly. The first read at its boundary may be counted in the continuation.

Construct the static index for this particular witness's cut memory with $H$ cleared. Its address and cell sizes are $O(\log m)$ even after unrestricted prefix work, because the native universe has $2^W$ words. On charge $t$ the original diagonal continuation can be replayed with $O(1+h+t+p)$ probes. The number of distinct raw hole replies subsequently used as unmodified addresses is $p\le\min(j,3K)$ since a query word has three possible tag formats per symbol. [First-hole replay theorem](processing-after-the-database-packets-of-a-sat-file.md)

Record the program index, sign, $T$, $j$, the combinatorial index of $H$, and the symbols $a_V$ in their coordinate order. **Pack the symbols as one base-$K$ integer**, at cost $\lceil (m-j)\log_2 K\rceil$ bits. Rounding the cost separately at each symbol could lose the conclusion near $j\asymp m/K$. Append the addresses and contents of the applied probes, including the controller. Including fixed boundaries or a stop marker, the bit cost is at most
$$
 m\log_2 K-\Delta_j+O\big((1+h+K+t)\log(m+2)+\log(r+2)\big).
$$
No elapsed step number is sent.

If two such descriptions agree, the programs, tags, $T$ and frozen symbols agree. On the index built at the **second database's own chosen prefix**, run the first database's query $x=a$. It agrees with that prefix on $V$, and the tag location and all replacements on $H$ are known. It is therefore an actual completion of that prefix. Transcript agreement reproduces the first database's normalized verdict of equality. The second database must also equal $x=a$. This proves injectivity even when neither the times nor the surrounding cut memories agree. The choice of a witness step need never be enumerated or encoded. [Adaptive transcript transport](../lean/ErasedCodeRosterEquality.lean)

Restricting attention to violations where the displayed lower estimate is positive, choose the constants so that every such record fits a single padded field of length at most $\lfloor m\log_2 K\rfloor-2$. Fixed directory lengths are known after $j$ is decoded and probe tuples can use a reserved stop symbol. At most one fourth of the databases have violating records. Relaxing the fraction to one half accommodates any larger fixed rounding allowance. The retained databases work for all suffixes simultaneously.

## How much information a deliberately chosen set of holes can convey

Consider the static decoder which is given $H$ in advance at no probe cost. A preprocessing stage can read the entire database and choose which $j$ query words to leave unread, comparing the other query words with the database first. There is a scheme using
$$
 O\left(1+\frac{\max(\Delta_j,0)}{W}\right)
$$
additional probes for **every** subsequent query. The decoder needs the query symbols only in $H$, a seed and one retained bit saying whether all earlier comparisons succeeded.

For each seed $s$ and hole set $H$ publish one prediction $B(s,H)\in[K]^H$. A prediction on $H$ agrees with precisely $K^{m-j}$ full database strings. For an explicit existence argument, cycle through all $\binom mj$ sets repeatedly. At each set $H$ choose a most frequent restriction $a_H$ amongst the as-yet-uncovered databases, then remove those databases. This leaves at most a $(1-K^{-j})$ fraction of the previous survivors. One cycle supplies all predictions for one seed. After
$$
 S=\max\left(1,\left\lceil (m\ln K+1)\,K^j/\binom mj\right\rceil\right)
$$
cycles the number of survivors is below one, by $1-u\le e^{-u}$. This is a deterministic public table, with ties broken lexicographically. For each $a$, choose $s,H$ with $B(s,H)=a_H$. The retained comparison bit and the test $x_H=B(s,H)$ give equality on any completion. Sending $s$ takes at most $\max(0,\Delta_j)+O(\log(m+2))$ bits. Conversely any collection of such predictions covering all strings requires $S\binom mj K^{m-j}\ge K^m$, so the seed lower bound in this model is $\max(0,\Delta_j)$ bits. When $j\le\lceil m/K\rceil$, one can simply leave $j$ copies of a most frequent database symbol and retain that symbol in one word.

For comparison, an exact threshold follows when the decoder may read the entire query locally and its frozen positions already agreed with the database. Form a bipartite graph on the $K^m$ databases and their possible partial words with exactly $j$ stars. Each left vertex has degree $\binom mj$ and each right vertex has degree $K^j$. If $\binom mj\ge K^j$, counting incident edges for each left subset gives at least as many neighbors as members, so Hall's theorem gives a matching covering every database. Conversely there are too few partial words if $\binom mj<K^j$. In the matching range, the stars and the unstarred *query symbols* identify the database on the frozen-equality promise. The prediction construction above also works when just the query symbols in the holes are supplied. [Hall's original theorem](https://doi.org/10.1112/jlms/s1-10.37.26)

These static decoders receive the chosen directory as part of their local query information, and the covering table may take extraordinary time to compute. A native solver must implement its own addressing and comparison. No claim about the native cost of these erasure schemes is used in the lower bound.

## Why the bounds at different prefixes cannot be added

There is a globally correct RAM program deciding every file in this constructed family in $O(m)$ native steps under the stated word operations. For a canonical fixed-template layout it validates public clauses with tables of packed decimal spellings and lengths. Starting at one digit, form the spelling of $10u+d$ by appending ASCII digit $d$ to the already packed spelling of $u$. This takes $O(m+K^2)$ operations for a consecutive range of $O(m+K^2)$ public wire numbers including the decimal table names (the fixed prefix has constant length). A padded clause with a bounded number of names is then assembled with $O(1)$ shifts and masks. Generate the $K$ legal fixed-width symbol blocks once. On each data or query word, mask out its fixed-width digit block, look it up in that table and validate the remaining fixed bytes. The $d$ ASCII bytes fit in $8d$ bits, safely smaller than the fixed large native width, so a disjoint scratch bank can be used for these keys. Check a single valid tag and compare each adjacent pair of digit blocks. The compiler uses $D=7m+2K^2+9$ total words and $c=D-m-1$ clauses. Its header thus yields $m=D-c-1$ and $2K^2=c-6m-8$ before any allocation; checking the integer square root once has negligible cost on this family. A mismatch with the promised format transfers to an exhaustive complete solver on the untouched original file. The [physical compiler](../audits/mixed_decimal_equality_packets.py) specifies the canonical layout. Thus the $\Omega(j)$ remaining charges at successive prefixes can account for the same comparisons. They cannot yield a superlinear clock on one run of this family.

The finite audit checks 37 exact matching thresholds, 37 prediction covers and 72,366 cross queries, with only a prefix comparison bit supplied to the suffix decoder. It also checks 330 variable-cut address/value descriptions. Lean checks the regular incidence count giving Hall's neighborhood inequality and the correctness of the prediction decoder. The native replay, matching existence theorem, asymptotic entropy and word-clock arguments above remain manuscript proofs. [Erasure and transcript audit](../audits/graded_erasure_cuts_audit.py) · [Lean incidence and decoder lemmas](../lean/GradedErasureCuts.lean)
