# Four individually harmless bit edits can jointly encode arbitrary 3-SAT

Let $E$ be a proper ternary CNF with model fraction $\mu(E)$, and let $\tau(E)$ be the minimum number of variables meeting every clause. Put $q=7/8$, $D(E)=\mu(E)/q^{\tau(E)}$, and $K=(4/7)^4$. Make $r$ proper name substitutions, in different clauses, producing $F$. These results use $N$ encoded input bits on a deterministic logarithmic-word RAM.

* If $D(E)>rK$, then $F$ is satisfiable.
* For $r=1,2,3,4$ the bound is sharp. At equality, a linear-time, linear-length reduction from arbitrary proper 3-SAT gives an easy file with a known model. Every strict subset of the designated edits leaves it satisfiable. Applying all the edits gives the source verdict and exactly its number of models on the occurring names. The edits are individual physical bit flips. A compact description of the complete easy model set is independent of the source signs and incidence pattern once the occurring names and the number of distinct clauses are fixed.
* For each of these four values of $r$, a globally correct solver has time $O_\delta(N)$ on edited files with $D(E)\ge rK+\delta$, for every fixed $\delta>0$, even when given only $F$. Requiring one uniform $O(N)$ bound over **all** positive margins, however small, is equivalent to linear-time ordinary 3-SAT. The same equivalence holds with quadratic or cubic deadlines.

For every fixed $r\ge5$, a globally correct solver runs in linear time throughout a fixed neighborhood of the threshold on the high side and below it, even given only $F$. The proof uses the [three largest normalized ternary model densities](the-first-three-normalized-densities-of-ternary-sat.md).

The timeout equivalences distinguish a growth guarantee for a solver correct on all files from a promise on which returning YES always suffices. No separation of RAM time classes is assumed or obtained here.

## Upper bound and fixed margins

Any model lost in a name substitution assigns fixed values to four distinct variables. The two shared literals and the new literal are false, and the old replaced literal is true. The model mass in any such codimension-four subcube is at most $Kq^{\tau(E)}$, by restricting the disjoint-from-these-variables clauses and adding back the four pins to a transversal. A union bound gives $\mu(F)\ge q^{\tau(E)}(D(E)-rK)$. Replacing $r$ clauses changes the minimum transversal by at most $r$, so $D(F)\ge q^r\delta$ at the stated positive margin. The constructive algorithm that finds two models of a formula of positive normalized density therefore succeeds on $F$ alone. [One-edit upper bound](a-sharp-density-threshold-for-one-physical-sat-edit.md) · [Constructing models and vanishing margins](two-models-from-positive-normalized-density.md)

## Data common to the constructions

Deduplicate source clauses. For $m$ distinct proper triples use $m$ disjoint triples of occurrence variables, one positive clause per triple. Keep one variable for each occurring source name. Use the two proper ternaries $\neg b\lor\neg y\lor\ell$ and $\neg b\lor y\lor\neg\ell$ to identify each occurrence $y$ with its source literal $\ell$ at $b=1$. At $b=0$ the occurrence triples independently admit seven assignments each, and the source variables are free. The fresh decimal identifiers cost $O(m\log(m+2))=O(N)$ because the retained source triples have distinct spellings. The constant-size controls below use separate names. All other auxiliary indicators occur only in this constant-size wrapper. [Physical encoding and the construction for one edit](a-sharp-density-threshold-for-one-physical-sat-edit.md)

## Two edits

Use a selector $t$. Let $g_0=t$ and $g_1=\neg t$, so that $g_i$ is false in mode $t=i$. In each mode impose $f_i=0$ and $a_i=\neg b$ only when $g_i$ is false. These are the clauses $g_i\lor\neg f_i$, $g_i\lor a_i\lor b$, $g_i\lor\neg a_i\lor\neg b$. Pad the binary clause with both signs of a third variable. The two selected clauses change as follows:
$$
 g_i\lor a_i\lor f_i\quad\longrightarrow\quad g_i\lor b\lor f_i,\qquad i=0,1 .
$$
Give $b,a_0,a_1$ the decimal names 1, 3, 5. Thus the locations and bits of both edits are prescribed. Before editing, the control models form two disjoint subcubes. Each fixes $t=i$, $b=0$, $a_i=1$, $f_i=0$, leaving the other mode's variables free. Any still-unedited mode supplies an easy model. After both edits $b=1$ is required.

The following always-true-on-the-easy-file clauses make the transversal number exact. Let $L_i$ contain the four signed literals forced true by easy mode $i$. For each choice of one literal from each $L_i$ with no opposite pair, take their disjunction, counting a repeated literal once. Pad it to length three with fresh positive private variables. Use four copies with mutually disjoint private fillers. All these clauses are true on either easy subcube.

No set of at most three variables hits this family. If $b$ is absent, four copies based on the common literal $\neg b$ defeat three private choices. If $b$ is selected, at most two other names are selected. In each $L_i$ there is an available literal other than $\neg b$. The only conflict across the modes is the opposite pair on $t$. It cannot be the only available pair since that would require selecting all four names $a_0,f_0,a_1,f_1$. A compatible choice therefore avoids the selected names, and some copy avoids the selected private fillers. Conversely the four pins of either easy mode hit all the control clauses. The $m$ occurrence supports are disjoint from this family, and one name from each, together with the four pins, meets the whole file. Hence $\tau(E)=m+4$.

At $b=1$ fix $t=0$, both inactive-mode variables to zero, and all private fillers to one. Gate these pins by $\neg b$ and pad with opposite signs of a distinct variable. They are vacuous in both easy modes. The hard controls are now unique and satisfy the added clauses via their private fillers. Each source model has exactly one hard extension. On the easy side the model density is $2\cdot2^{-4}q^m$, giving $D(E)=2K$.

## Three edits

Take two selector bits $s,t$ and allow patterns $00,10,01$ in that order, using the binary restriction $\neg s\lor\neg t$ padded by opposite signs. For mode $i$, write $g_i,g'_i$ for the two literals simultaneously false exactly on its pattern. Change the variable $a_i$ to $b$ in the clause $g_i\lor g'_i\lor a_i$. Decimal names $3,5,9$ are each one bit from $b$'s name 1. At $b=1$ fix $s=t=0$, $a_0=0$, $a_1=a_2=1$ and all private fillers to one, using proper ternary gated pins. At $b=0$ the unedited file accepts exactly the three control subcubes fixing $b,s,t,a_i$ with $a_i=1$ in mode $i$. The two inactive $a$ variables remain free.

Add four copies of the true-on-the-easy-side literal $\neg b$ padded with disjoint positive private pairs. Also add the following six constraints, padding each binary with four distinct positive fillers in separate copies:
$$
\neg s\lor\neg t,\quad
\neg s\lor a_1,\quad \neg t\lor a_2,\quad
s\lor a_0\lor a_2,\quad t\lor a_0\lor a_1,\quad a_0\lor a_1\lor a_2.
$$
They hold throughout each easy mode and at the prescribed hard control assignment. No two variables meet all six underlying supports. A set hitting $\{s,t\}$ must contain $s$ or $t$. If it contains both, it misses the last triple. If it contains only $s$ of these two, its other member must be $a_2$ to hit $\{t,a_2\}$, and it then misses $\{t,a_0,a_1\}$. The case with only $t$ is symmetric. The private copies force four control hits in total as before. The four pins of a single easy mode and one variable per occurrence triple suffice.

Every strict subset of edits again leaves an unedited easy mode. All three together give the source verdict with a bijection on models. The disjoint three-box easy side has density $3\cdot 2^{-4}q^m$ and transversal number $m+4$, attaining $3K$.

## Four edits

For this construction use $d=1$ for the easy branch and $d=0$ for the source branch, so the occurrence identifications now use positive $d$ as their guard. Use six other controls $x,y,z,A,B,C$. Each row gives the old clause and its replacement.

| Row | Before | After |
| --- | --- | --- |
| 1 | $d\lor\neg y\lor\neg z$ | $\neg x\lor\neg y\lor\neg z$ |
| 2 | $A\lor x\lor\neg y$ | $\neg d\lor x\lor\neg y$ |
| 3 | $B\lor\neg x\lor z$ | $\neg d\lor\neg x\lor z$ |
| 4 | $C\lor y\lor\neg z$ | $\neg d\lor y\lor\neg z$ |

Include the four common clauses
$$
 x\lor y\lor z,\qquad x\lor A\lor C,\qquad
 y\lor B\lor C,\qquad z\lor A\lor B.
$$
At $d=1$ the unedited file has exactly the following four disjoint sets of control assignments. In addition to $d$, each row pins three literals to true.
$$
 (x,y,z),\qquad (\neg x,y,A),\qquad
 (x,\neg z,B),\qquad (\neg y,z,C).
$$
The triple $000$ violates the first common clause. Apart from $111$, each of the six remaining selector triples has exactly one transition $x=0,y=1$ or $x=1,z=0$ or $y=0,z=1$. That transition requires the leaf literal in the corresponding row. Every other common clause is true throughout each of these four sets. The replacement in row $i$ is false throughout set $i$ and true throughout the other three sets. This proves that every proper subset of the edits preserves an entire easy set.

At $d=0$ pin $(x,y,z,A,B,C)=(0,0,1,1,1,0)$. For every required literal $u$ use $d\lor u\lor t$ and $d\lor u\lor\neg t$ for some distinct existing control $t\ne d$. Add four copies of $d$ padded with disjoint pairs of fresh positive variables, and pin these eight variables true at $d=0$ in the same manner. The hard assignment satisfies the common clauses and all four replacements. It falsifies old row 4. Thus the unedited side accepts only the easy sets, and after all four edits each source model has exactly one extension.

To check the control transversal, a set avoiding $d$ must meet four disjoint private pairs. A set containing $d$ must also meet the seven supports
$$
 xyA,\quad xzB,\quad yzC,\quad xyz,\quad xAC,\quad yBC,\quad zAB .
$$
No two names suffice. Two leaf names miss $xyz$. Two selector names miss the remaining selector's clause with two leaves. If just one selector is used, for instance $x$, the uncovered triples $yzC,yBC,zAB$ have empty intersection. Cyclically rotating the directed selector cycle gives the other two cases. The four names $d,x,y,z$ and one name per occurrence triple meet every clause. The opposite bound follows by counting the control hits separately from the $m$ disjoint occurrence triples. Consequently $\tau(E)=m+4$, $\mu(E)=4\cdot2^{-4}q^m$, and $D(E)=4K$.

For literal names on disk take $x=\neg X$, $A=\neg A'$, $B=\neg B'$, $C=\neg C'$. Give $d,X,A',B',C'$ the decimal identifiers $11,10,13,15,19$. All four edits now preserve the literal sign. Each flips one bit in the units digit of an actual identifier without changing any delimiter, length or header.

## Trying a fifth edit

The four-edit construction uses the common guard as the *old* variable in row 1 and the *new* variable in the other three rows. This distinction emerged from a failed enumeration. With a common new guard in all four rows, each row has two shared literals that by themselves must make its edited clause true on all other easy sets. Of 9,039 normalized ordered configurations of four disjoint three-pin subcubes, 4,980 meet that additional condition. In every one, two names already meet all guard-free clauses true throughout the four subcubes. Together with the guard this saves one transversal hit and misses the proposed equality.

Allowing both guard roles leaves 72 configurations in which two names do not suffice. Every one of their 720 normalized fifth extensions restores a two-name transversal. Any four-prefix already admitting a pair keeps that pair when a fifth subcube is added. Thus four is the maximum for this construction with a shared guard, unrestricted remaining wrapper coordinates in each geometrically disjoint easy subcube, and the same independent occurrence constraints in every subcube. The census examines all possible clauses through their pinned true literals. The general case with different residual constraints requires a separate [density spectrum and algorithm](the-first-three-normalized-densities-of-ternary-sat.md). [Enumerating and normalizing the subcubes](../audits/four_shared_guard_boxes.py) · [Finite checks in Lean](../lean/FourSharedGuardBoxes.lean)

## Why strict inequality without a uniform margin still tests ordinary SAT time

Make a second version of each construction. In the one-edit gadget replace the clauses enforcing $a=\neg b$ with $a\lor b\lor f$ and $a\lor\neg b\lor f$, so $a$ is always true. For two edits enforce $a_i=1$ in the active mode for either value of $b$, by changing the second gated sign. For three edits change the hard pin to $a_0=1$. For four edits change the hard pin on $C$ to one, so the fourth old clause is now true too. Leave the hard pins on all remaining coordinates in place. These replacements preserve the transversal witnesses.

On the easy branch the slices are exactly the original ones. On the hard branch both the original and fully edited files now have exactly one extension per source model. Writing $v$ for the number of occurring target variables and $M$ for the number of source models gives
$$
         D(E)=rK+\frac{M}{2^v q^{m+4}},\qquad
         \#\operatorname{models}(F)=M .
$$
The known easy assignment is available in either case. If a globally correct solver finishes within $C(N+1)^k$ on all edited files with any strictly positive margin, run it with that timeout on the constructed $F$ and accept only a returned YES. Every satisfiable source is in the fast promise. On an unsatisfiable source a globally correct solver cannot return YES, even if its run times out. This gives an ordinary $O(N^k)$ SAT solver for $k=1,2,3$ with the respective hypothesis. Existence of a fixed integer clock multiplier suffices. A globally correct ordinary solver immediately yields the converse. A promise-only program allowed to return false positives outside its promise does not have this consequence.

## Verification

The [Lean checks](../lean/TwoEditsAtTheDensityThreshold.lean) verify the control patterns, finite transversal witnesses and density identities. The [byte-level audit](../audits/two_edits_at_the_density_threshold.py) constructs two-edit squares and three-edit cubes, checks that each edge changes one physical bit, and checks both ordinary threshold and no-margin versions. The four-edit construction has separate [finite control checks](../lean/FourEditsAtTheDensityThreshold.lean) and an [audit of encoded files](../audits/four_edits_at_the_density_threshold.py). The general density argument and the running-time transfers are manuscript proofs. The literature on model-density tests for bounded-width CNF includes Akmal and Williams's deterministic algorithms for fixed absolute thresholds. The threshold here normalizes by a clause transversal and concerns the file after specified edits. Priority has not been established. [Akmal and Williams](https://arxiv.org/abs/2107.02748)
