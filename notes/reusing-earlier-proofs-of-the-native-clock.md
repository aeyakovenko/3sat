# Reusing proofs at earlier widths of the native clock

Fix the tagged program, finite arithmetic theory $A$, and literal Hilbert proof encoding of the [elapsed-time witness construction](proof-length-and-the-next-sat-clock-witness.md). Write $J_h$ for quietness of that program at width $h$, $L_h$ for its shortest proof length in bits, and $b(h)=h^4$. The assumption that a group decides SAT correctly throughout the image of a fixed tag implies $L_h>h^4$ at all sufficiently large widths on that tag's progression. All the proof comparisons below use this same $A$ and program.

## One proof for every width through $H$

There is an $A$-proof of

\[
                        U_H=\forall u\le\bar H\;J(u)
\]

of length $O_A(1+H^4)$, unconditionally. The variable $u$ ranges over the widths through $H$, across all tags and including the program's silent defaults. The proof uses a single partial satisfaction predicate.

To see this, set $B=H^4$, let $j(u)$ construct the code of the closed sentence $J_{u}$, and express $\operatorname{Pr}_{A,\le B}(j(u))$ using literal proof length. The end sentences have bounded quantifier depth for every $u$, since the entire varying input is a closed binary numeral. The shortest-proof shortening lemma is uniform for all end sentences of that fixed depth, with constants depending on the fixed calculus and axioms. In $A$, any such sentence provable within $B$ has a proof within $B$ of depth at most $m=C_A(1+H^2)$. Pudlák's partial satisfaction construction proves soundness through length $B$ at that depth in $O_A(m^2+m\log^2(B+2))$ symbols. This assertion ranges over codes of proofs and their end sentences.

Disquote the fixed formula $J(x)$ with a variable parameter for the numeral code, using the numeral evaluation identity and the compositional satisfaction clauses for its fixed logical nodes. Generalization gives

\[
 A\ \vdash\ \forall u\,[\operatorname{Pr}_{A,\le\bar B}(j(u))\ \longrightarrow\ J(u)]
\]

within $O_A(m^2+m\log^2(B+2)+\operatorname{polylog}(H+2))$ bits. The numeral for $B$ is fixed in this proof. This is the uniform-parameter form of the [fixed-cap proof, including the choice of calculus and the syntactic axioms](fixed-cap-reflection-on-the-native-program.md). The original lengths for partial satisfaction and finite iteration are in [Pudlák, Lemmas 3.2 and 3.4–3.6 and Theorem 3.7](https://users.math.cas.cz/~pudlak/improved.pdf).

The program's syntactic axiom yields $\neg J(u)\to\operatorname{Pr}_{A,\le u^4}(j(u))$. For $u\le\bar H$ arithmetic gives $u^4\le\bar B$, so the two implications prove $U_H$. This last use of the bridge is uniform in $u$. The bound follows without writing $H+1$ separate finite-reflection arguments.

## Free access to earlier results

Let $L^{[H]}_h$ count literal proof bits after adding $J_0,\ldots,J_H$ as free nonlogical axioms. Each axiom can be used as a previously established formula. Keep the syntax of formulas, substitutions, and inference rules fixed. There is a constant $K$ independent of $h,H$ and the tag such that

\[
                 L_h\le L^{[H]}_h+K(1+H^4).
\]

Prepend the proof of $U_H$. For each distinct borrowed $J_i$, instantiate $U_H$ and prove the true comparison $i\le H$ on binary numerals. The fixed arithmetic presentation does this in $\operatorname{polylog}(H+2)$ bits per comparison. There are at most $H+1$ specializations. Keep each resulting formula available to every subsequent inference. The Hilbert encoding checks earlier formulas as premises and uses no line-number fields requiring renumbering. Drop duplicate stand-alone axiom lines in the borrower. If the final line itself is borrowed, place its specialization last or use its specialized proof alone. These operations cost $O_A(1+H^4+(H+1)\operatorname{polylog}(H+2))=O_A(1+H^4)$ bits beyond the borrower. The same additive accounting applies when earlier *proof lines* are provided by a specified set of ordinary $A$-derivations whose total written size is charged once.

On a fixed tag with a correct group this gives, for every sufficiently large width $h$ of the tag and any $H$,

\[
                    L^{[H]}_h>h^4-K(1+H^4).
\]

In particular $H=o(h)$ leaves a lower bound $(1-o(1))h^4$. At $H=\lfloor\alpha h\rfloor$ the bound is $(1-K\alpha^4-o(1))h^4$, useful for sufficiently small fixed $\alpha>0$. A finite collection of uniform retirement theorems from completed earlier budgets also costs only an additive constant once the collection is fixed. Each theorem already has a fixed $A$-derivation. Free abbreviations that change the syntax of intermediate formulas would require a separate translation bound.

## The cost of passing to the next width

At a fixed tag $j$ write $h_t=2^j(2t+1)$ and $d=2^{j+1}$, so $h_{t+1}=h_t+d$. Let $e_t$ be the least literal length of an $A$-proof of $J_{h_t}\to J_{h_{t+1}}$. These minima are finite since each closed instance has a finite proof. Starting from a fixed proof of $J_{h_0}$, concatenate the implication proofs and append the next instance by modus ponens at each step. All reused earlier premises remain available. Writing the new line costs $O_A(1+\log(h_{t+1}+2))$ bits. Thus

\[
 L_{h_m}\le L_{h_0}+\sum_{t<m}e_t+O_A\!\left(\sum_{t<m}(1+\log(h_{t+1}+2))\right).
\]

If a group is correct throughout the image, the left side exceeds $h_m^4$ eventually and the sum of line overheads is $o(h_m^4)$. Consequently

\[
 \liminf_{m\to\infty}\frac{\sum_{t<m}e_t}{h_m^4}\ge1,
 \qquad
 \limsup_{t\to\infty}\frac{e_t}{h_{t+1}^4-h_t^4}\ge1 .
\]

For the second inequality, an eventual ratio at most $1-\epsilon$ would telescope to at most $(1-\epsilon)h_m^4+O(1)$. The fourth-power increment is $4d h_t^3+O_j(h_t^2)$. Hence infinitely many forward implications require at least $(1-\epsilon)4d h_t^3$ literal bits for every fixed $0<\epsilon<1$. If every group at the tag is erroneous, its uniform retirement theorem gives $e_t=O_j(1+\log h_t)$ by instantiation and propositional weakening. An eventual $o_j(h_t^3)$ upper bound for these *forward* implication proofs therefore excludes a correct group at that tag. Establishing this for a fixed seed and unbounded eligible code budgets would exclude the proposed ordinary SAT clock.

The [Lean arithmetic lemma](../lean/NativeProofReuse.lean) proves the finite accumulated-cost inequality for every chain length and its strict consequence under a cap violation. The Hilbert translations, asymptotic estimates and arithmetic reflection construction above remain manuscript arguments.

## A nested arithmetic counterexample

There is a single arithmetic formula $D(x)$, obtained by the parameterized diagonal lemma in the same $A$, with

\[
 A\ \vdash\ D(x)\ \longleftrightarrow\
    \forall i\le x\;\neg\operatorname{Pr}_{A,\le i^4}(\ulcorner D(\bar i)\urcorner).
\]

For any standard $i$, an in-cap proof of $D(\bar i)$ would make the sentence true by soundness, and its instance at $i$ would exclude that very proof. Hence every $D(\bar H)$ is true and every proof of it exceeds $H^4$. If $h\le H$, $A$ proves $D(\bar H)\to D(\bar h)$ by restricting the bounded universal and using the fixed equivalence. The general backward implication has one fixed $A$-proof, and the closed numeric instances cost at most $\operatorname{polylog}(H+2)$ bits.

One $O_A(1+H^4)$-bit proof establishes $\forall i\le\bar H\,D(i)$. Apply the same finite reflection to the fixed template $D$ with cap $H^4$. An in-cap proof at any $i\le H$ would imply $D(i)$ and hence contradict its own existence. This gives the bounded universal in the defining equivalence, uniformly for every earlier index. The example has nested statements, cheap backward implications and a reusable proof covering all earlier indices, while every individual proof still exceeds its cap. This calibrates shortcuts relying on those three properties. A forward construction for the native program would have to use further information about its SAT computations.
