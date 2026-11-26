# Exhausting small advice tables on one block of widths

Fix $r\ge0$, and let $d=2^r$. A predictor for the padded forecast sees the ordinary file $x_W$ of length $M=2^{\lceil n/4\rceil}$, where $n=|\operatorname{bin} W|$. In addition it receives $s$ arbitrary advice bits shared by all $d$ widths with the same first $n-r$ bits. No computability restriction is placed on the assignment of advice to prefixes. Assume one uniform deterministic logarithmic-word RAM program is correct on all valid widths with the assigned advice.

* If $s<d$, every such program takes $\Omega_{P,r,s}(M^4/\log M)$ steps on at least one width in each sufficiently long block with a certain fixed binary prefix.
* If $s=d$, one uniform program decides the forecast on all valid files by indexing the advised truth table at the low $r$ bits. It can reject malformed files in $O(M)$ steps. This is below the displayed clock.

The lower bound is worst case over the widths in a block even given the correct advice for that block. For example two free bits give four inputs. Three advice bits can name eight proposed four-bit answer vectors. At least eight vectors remain available for the forecast. Four advice bits suffice outright. [Padded prediction problem and simulator](one-variable-delay-and-one-binary-product.md)

## Realizing a missing answer vector

The wider-word diagonal mode of the fixed recurrence takes a guest on the *entire* binary width. If it finishes in at most $c_Q W/n$ wide-word instructions, the final bit equals the complement of its reported bit. The constant $c_Q>0$ depends only on the guest and interpreter. This simulation guarantee holds even for a guest that gives wrong answers. Small finitely many widths can be omitted throughout.

Fix the proposed predictor $P$. Make a wide guest $Q$ using the following algorithm. After parsing its simulation header it reads a further self-delimiting nonnegative integer $b$. This is a tuning parameter from the input. Given a prefix $u$ of length $n-r$, let $W_0$ have binary spelling $u0^r$. On all $d$ widths $u v$, the guest simulates $P$ on all $d$ padded files and all $2^s$ trial advice strings. It charges each trial at most
$$
              t=\left\lfloor W_0/(2^b n)\right\rfloor
$$
guest instructions of $P$. It records an arbitrary default bit for a trial that has not returned a Boolean answer. Each advice string now proposes one $d$-bit vector. Choose the first $d$-bit vector $z$ absent from this list, and return $1-z_v$ for the actual low bits $v$.

For fixed $r,s$, the enumeration and selection outside the trials cost a constant plus $O(\operatorname{poly}(n))$ and the setup of the padded inputs costs $O_{r,s}(M)$. Each timed-out trial may discard its entire scratch region: use a separate region for each trial and account for its actual writes. A fixed wider word can hold the simulated word, input and counter addresses. Simulating a fixed instruction, including masking to $P$'s own word width, takes $O_P(1)$ instructions. Thus $Q$ uses at most $C_{P,r,s}\,2^{-b}W_0/n+O_{P,r,s}(M+\operatorname{poly}(n))$ instructions. Choose one fixed $b$ large enough **after** $Q$ and its interpreter constant have been fixed. At every sufficiently long prefix $u$ beginning with that guest header and this tuning field, all $d$ simulations of $Q$ finish soon enough to latch. Therefore the actual vector of forecast bits throughout the block equals the single vector $z$ selected by $Q$. If all runs with the assigned advice finished by $t$, their recorded vector would equal $z$, which the selection excludes. At least one actual run exceeds $t=\Omega_{P,r,s}(M^4/\log M)$.

The same argument counts how many slow inputs a block must contain. Write $K_2(d,e)$ for the minimum number of binary Hamming balls of radius $e$ covering $\{0,1\}^d$. If $2^s<K_2(d,e)$, choose $z$ outside the balls about all capped predictions. For an exactly correct advised predictor the displayed block now contains at least $e+1$ timeouts. If the aim is to answer fast throughout a block with up to $e$ errors, the exact advice threshold is $\lceil\log_2 K_2(d,e)\rceil$. The upper bound advises a nearest covering-code word to the genuine table. For instance with two free bits and one advice bit one can force at least two slow inputs for an exact predictor: two radius-one balls have total volume at most $2(1+4)<16$. The count requires no independence among the proposed answers.

## An algebraic extension that keeps every old answer

Let $Z(x)$ encode a frozen Boolean answer on all $x\in\mathbb F_2^r$. Regard each truth table as its unique multilinear polynomial over $\mathbb F_2$. Add a fresh bit $b$. Every extension of $Z$ has the form
$$
            E(x,b)=(1+b)Z(x)+bY(x)
$$
for a freely chosen $d$-bit table $Y$. For any new collection of candidate tables, discard all whose $b=0$ half differs from $Z$. An extension avoiding every candidate exists **exactly when** their distinct surviving $b=1$ halves number less than $2^d$. Duplicated advice responses are counted once. The criterion is sharp because an adversary can attach every $Y$ to $Z$. In particular $s+1<d$ suffices even if the new predictor reassigns every advised answer after the extension. Starting at $d=2,s=0$, one can preserve all frozen old values as $d$ doubles and $s$ increases by one at each stage. At $d=1,s=0$ the same first step can fail: two candidates can agree on the old value and cover both possible new values.

For each fixed finite stage the guest construction can hardwire $Z$, prescribe its low half, and select an omitted high half. This realizes the extension on the prediction source when the criterion holds. The recurrence interprets a guest specifically chosen for that stage. A single SAT formula whose running time has this preservation property would require a further construction. [Lean finite exhaustion and timeout lemma](AdviceTableExhaustion.lean) · [Exact extension census](forecast_advice_table_audit.py)
