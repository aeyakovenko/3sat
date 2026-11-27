# Four programs cover the eight-step native cohort

One correct program accepts 24 of the 64 complementary four-word targets by its eighth executed instruction. Four correct programs cover all 64 by that deadline. In the full instruction set, the minimum number of programs is between two and four. A direct enumeration gives an exact answer of four for programs that take the five-instruction indirect-read prefix below and then use comparisons until the deadline.

The native file has four nibbles in address order \(p,q,m,n\). Its SAT criterion is \(p\mathbin{\&}m=q\mathbin{\&}n=0\) and \((m,n)\ne(15,15)\). The cohort consists of \((p,q,15-p,15-q)\) for \(4\le p,q\le11\). Each memory load, word operation, and binary comparison costs one instruction. A terminal costs zero. In every program below, each failed fast path transfers to the complete nine-step decider. The prefix leaves input memory intact, so the fallback can reload all four cells. [Native semantics and the global nine-step optimum](exact-nine-step-clock-for-four-sat-words.md) · [The seven-step rows and the 36-target per-program upper bound](which-four-word-sat-targets-finish-in-seven-steps.md)

## A tree covering 24 targets

Load \(q,m,n\), compute \(j=q\mathbin{\&}n\) and load \(x=\operatorname{mem}[j]\). The following tree uses at most three further comparisons. Write \(<_s\) for signed four-bit order. Ordinary inequalities use unsigned order.

~~~text
if 9 < m:
    accept if m = 11 and x = 4
else:
    if m <_s j:
        accept if x = 6
    else:
        accept if x = 8
~~~

On the cohort, \(j=0\) and \(x=p\). The three accepting rows are \(p=4,6,8\). On arbitrary files, \(j=1\) or \(3\) returns an odd word, and \(j\ge4\) returns zero. If \(j=2\), then \(x=m\). In the first branch \(m=11\) precludes \(x=4\). In the second branch \(m=x=6\) precludes \(m<_s2\), and in the third branch \(m=x=8\) forces \(m<_s2\). Consequently every accepted file has \(j=0\) and \(x=p\). The second branch then forces \(m\in\{8,9\}\), both disjoint from six. The third branch forces \(0\le m\le7\), disjoint from eight. The first branch fixes the complementary pair \((4,11)\). The tree accepts 891 of the 65,536 files.

## A portfolio covering every target

Create one program for each even \(a\in\{4,6,8,10\}\). After the same five instructions use this tree. The immediates are compiled into the four programs.

~~~text
if m = 15-(a+1):
    accept if j = 0 and x = a+1
else:
    accept if m = 15-a and x = a
~~~

The first accepting branch directly checks the two disjoint pairs. In the second, \(a\) is even and nonzero. The indirect load can return \(a\) only at \(j=0\), since \(j=2\) would return \(15-a\ne a\). Thus the program accepts exactly the target rows \(a,a+1\), and all its 162 fast acceptances on the full catalog are SAT. The four programs give disjoint fast target sets. Two bits selecting a fixed program suffice on this cohort. Without advice the previously proved global upper of 36 fast targets per program implies at least two programs are required.

## Exact capacities for comparison continuations

After the specified five instructions the program can compare any pair from \(q,m,n,j,x\) and the sixteen literal values, in either operand order, using equality, signed order, unsigned order, or complementary outcomes. Unfold the remaining three comparisons into a tree. A leaf with no negative files can accept every target reaching it. A leaf with a negative must fall back or reject. The 58,976 negative files and 64 targets yield 251 distinct nonconstant guard partitions, identifying a split with its reversal. Constant splits can be omitted by skipping a redundant comparison.

Compute the maximum over all remaining first splits, adding the two child capacities. Use first unit weight on every target, then unit weight only on targets with odd \(p\). The resulting capacities at depth three are **24 overall and 8 on odd rows**. The first tree attains the total capacity. Each paired program attains the odd-row capacity. The 32 odd-row targets force at least four such trees. These are separate optimizations. Every branch can choose its own next comparison, and the audit allows independent fallback decisions at every leaf.

The upper bound of four programs in the full model follows from the explicit programs. Applying the four-program lower bound outside this comparison continuation would require bounding other prefixes and arithmetic, memory, or store instructions in the suffix. All of the capacities here concern a single fixed word width and selector encoding.

Run `python3 -B eight_step_guard_portfolios.py` and `lean NativeEightStepPortfolios.lean`. The standard-library Python audit checks all five explicit trees on all 65,536 files. Its upper-bound search first tests a small negative subcatalog and then checks every remaining prospective accepting leaf against all negatives. The Lean file proves global soundness and the exact cohort rows of each explicit tree via bit-vector reasoning. The comparison-tree maximum is executable enumeration. [Exhaustive audit](eight_step_guard_portfolios.py) · [Lean proofs of the explicit programs](NativeEightStepPortfolios.lean)
