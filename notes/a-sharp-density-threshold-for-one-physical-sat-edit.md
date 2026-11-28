# A sharp model-density threshold for one physical edit of a 3-CNF file

Let $E$ be a proper ternary CNF. Its model density $\mu(E)$ is the fraction of all assignments satisfying it, and $\tau(E)$ is the fewest variables meeting every clause. Unused names can be included or omitted in the density. Change one literal in one clause by substituting a different variable name. Require that the three variables of each clause remain distinct. Write $F$ for the edited formula, $q=7/8$, and $D(E)=\mu(E)/q^{\tau(E)}$.

**Theorem.** If $D(E)>(4/7)^4$, then $F$ is satisfiable. At **exact equality**, deciding $F$ can encode any ordinary proper 3-SAT instance by a deterministic linear-time, linear-length reduction. The constructed files differ in a single physical bit. Their easy-side density and transversal number are exact for every source verdict. The hard-side models project bijectively to the source models on occurring variables. A satisfying assignment of the easy side is explicit.

## Why four variables enter the bound

Fix $j$ distinct variables of $E$ to any specified values. The ternary clauses avoiding these variables have transversal number at least $\tau(E)-j$, since a transversal for them and the $j$ variables together hit $E$. The [transversal density inequality](model-density-and-a-transversal-of-ternary-sat-clauses.md) bounds the mass of models in this particular subcube by
$$
2^{-j} q^{\tau(E)-j}=(4/7)^j q^{\tau(E)}.
$$
If $j>\tau(E)$ the same upper bound follows from the subcube mass $2^{-j}$.

Suppose $F$ is unsatisfiable. Every model of $E$ must falsify the new clause while satisfying the old clause. Thus the two shared literals must be false, the old changed literal true, and the new changed literal false. The four underlying variables are distinct, fixing one four-variable subcube. It contains every model of $E$. More generally, if $j$ variables have fixed values in all models of $E$, the same subcube argument gives $D(E)\le(4/7)^j$. Thus a file at the threshold can have at most four such backbone variables. The four-variable edit proves $D(E)\le(4/7)^4$. The implication above the threshold concerns promised verdicts. It does not give a procedure to certify the density promise from the edited file.

For canonical proper ASCII DIMACS this also covers **every other well-formed file at physical Hamming distance one**. The convention is a single header, one space between fields, one LF-terminated clause per line and canonical decimal spellings. If the header is unchanged, the body has a fixed number of LF and space bytes. One changed bit therefore preserves these delimiters. A minus is no decimal digit’s one-bit neighbor. A changed literal hence gives a distinct identifier at the same position, with its sign fixed. A change confined to a valid header preserves the verdict. Thus above the threshold an entire one-bit neighborhood of proper files is satisfiable. [Physical edit proof and grammar](the-physical-size-of-a-parity-face-of-sat.md)

## Reaching equality on both target verdicts

Start with a proper source 3-CNF $S$. Remove duplicate clauses, leaving $m$, and keep a representative bit $z_i$ for each occurring source variable. Make three fresh *occurrence* variables $y_{j,1},y_{j,2},y_{j,3}$ per clause. Print one positive clause on each of these disjoint triples. Use guard $b$. For each occurrence with source literal $\ell$, print
$$
(\neg b\lor\neg y\lor\ell)\land(\neg b\lor y\lor\neg\ell).
$$
When $b=1$, $y$ equals the truth value of $\ell$. When $b=0$, the occurrence variables and the source representatives are independent except for the positive clauses.

Use four controls $a,b,f,g$. Force $f=0$ with the four clauses $\neg f\lor(\pm a)\lor(\pm b)$ over both choices of signs, and force $g=0$ in the same way. Enforce $a=\neg b$ with $(a\lor b\lor f)$ and $(\neg a\lor\neg b\lor f)$. The edited clause is $a\lor f\lor g$ in $E$ and $b\lor f\lor g$ in $F$.

For each literal in the list $a,\neg b,\neg f,\neg g$, add one clause consisting of that literal and two fresh positive private variables, using eight private variables in total. In the hard file, pin every private variable $u$ to true with $\neg b\lor u\lor f$. These pinning clauses are common to both files and impose no condition at $b=0$. All printed clauses contain three distinct variables.

On $E$, exactly one assignment of the four controls is possible. The original representatives and eight private variables are unrestricted. Each disjoint positive occurrence clause independently accepts seven of its eight assignments. Consequently
$$
\mu(E)=2^{-4}(7/8)^m .
$$
The $m$ occurrence clauses and the four clauses on private pairs have mutually disjoint supports. A transversal of size $m+4$ is given by the four controls and one variable in each occurrence clause. This proves $\tau(E)=m+4$ and hence $D(E)=(4/7)^4$. Taking all occurrence variables true gives a known model. Keeping the controls fixed, changing up to two other coordinates of that model still satisfies $E$.

On $F$, the controls take their other allowed assignment and all eight private bits are forced true. Each $y$ is uniquely determined by the $z_i$. The positive clauses then express exactly $S$. This gives the claimed bijection. If a DIMACS header declares unused identifiers, they are free on both sides of the density calculation. Counts in the bijection refer to occurring names. The empty source conjunction gives one model on the empty set of occurring names and satisfies the same formulas at $m=0$.

The description of the entire easy model set uses only the four fixed controls and the disjoint positive occurrence clauses. All other data variables are free. That description can be supplied with every edited instance in linear length. It is identical for sources with the same occurring names and the same number of distinct clauses. For an explicit pair, take all eight signed triples on source names 1, 2, 3, together with the positive triple on 1, 2, 7. This source is unsatisfiable. Replacing just the negative literal on name 3 in the all-negative clause by the negative literal on name 7 leaves one model. Both sources yield the same complete easy model set on identical variable names.

## Encoded cost and verification

Use decimal names 1 and 3 for $b$ and $a$ and 5 and 7 for the pads. Reserve eight further names 80 through 87 for the private variables. Prefix source canonical decimal names with 6 for their representatives and prefix occurrence indices with 9. The final clauses on the two files are the bytes for `3 5 7 0` and `1 5 7 0`. The header and every other byte agree. ASCII 3 and 1 differ in one bit. The extra cost of writing the occurrence names is $O(m\log(m+2))=O(N)$, where $N$ is the physical source length. The distinct normalized source clauses have distinct fixed-alphabet spellings with total length $O(N)$. They can be interned in deterministic linear time by a digit trie with separators after sorting the three literals within each clause. Each old identifier is copied a bounded number of times per retained occurrence. Header maxima can be tracked as decimal strings by length and lexicographic comparison. These operations give linear time even with repeated clauses, sparse identifiers and long spellings. [Related one-bit reduction and width conventions](affine-insertion-at-a-clause-of-an-ordinary-3cnf.md)

The [Lean lemmas](../lean/OneBitClauseDensityThreshold.lean) verify the transversal lift under any pins, normalization of the residual upper bound, the four pinned literal values, the control and occurrence truth tables, the hard pinning of the private bits, and the exact density arithmetic. The [ordinary DIMACS audit](../audits/one_bit_clause_density_threshold.py) builds actual byte strings, reparses both files, counts models, and checks explicit matching and transversal witnesses. The general transversal theorem, algorithmic cost and bijection are proved above. No historical priority is claimed.
