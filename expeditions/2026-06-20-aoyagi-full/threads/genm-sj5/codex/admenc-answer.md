## Ranked verdict

1. **Definite failure: TOO-TIGHT.** “\(Z_{\mathrm{deep}}\) has full rank” is not equivalent to \(p=0\) and breaks peel closure.
2. **Base interface: GAP.** Divisorwise \(p=0\) does not by itself supply the single simultaneous generator required by `sjLoss_terminal`.
3. **Potential TOO-LOOSE variant.** Checking only the original component divisors misses exceptional divisors over their intersections.
4. **Redundancy.** For genuine binding-cut reachability, correct \(p=0\)-transversality should be proved from reachability, not carried separately.

### Exact algebra

For a critical divisor \(\eta\), let

\[
G_\eta=(q_1+s q_2)_j
\]

be the coordinate generators of \(H_1\). Define

\[
p_\eta=\nu_\eta(G_\eta):=\min_j\nu_\eta((q_1+s q_2)_j).
\]

Then

\[
p_\eta=0
\iff
\exists j,\ (q_1+s q_2)_j\notin\mathfrak p_\eta
\iff
(G_\eta)R_{\mathfrak p_\eta}=R_{\mathfrak p_\eta}.
\]

This is “some corank generator is a unit at \(\eta\).” It is not a full-rank assertion about \(Z_{\mathrm{deep}}\).

## Q1 — TOO-TIGHT

The stated equivalence with “\(Z_{\mathrm{deep}}\) enters at full rank” is false.

At the reduced \((2,2,2)\) zero-product locus, the component dimensions are governed by

\[
(2-r)^2+2r=(4,3,4),\qquad r=0,1,2.
\]

Thus the unique top component has

\[
\operatorname{rank}_{\mathrm{gen}}Z_{\mathrm{deep}}=1<2.
\]

This component occurs after the binding peel of \((3,3,2,2)\) at \(t=2\), where \(a=b=1\). Nevertheless,

\[
\operatorname{rank}_{\mathrm{gen}}(A_{\mathrm{cor}}Z_{\mathrm{deep}})
=\min(1,1)=1=b,
\]

so its single corank row is nonzero generically and \(p=0\). The peel genuinely produces this decoration, while the proposed full-rank predicate rejects it.

The correct clause is

\[
a=0\ \lor\ b=0\ \lor\
\forall\eta\in\operatorname{Crit}(D),\quad
\min_j\nu_\eta((q_1+s q_2)_j)=0.
\]

Equivalently, the corank-generator ideal is the unit ideal after localization at every critical divisor. The geometric sufficient condition furnished by F2 is only

\[
\operatorname{rank}_{\mathrm{gen},X} Z_{\mathrm{deep}}
\ge a+b-1\ge b,
\]

not full ambient rank. No condition on \(q=\nu_\eta(H_2)\) belongs in admissibility.

## Q2 — REDUNDANT after correction

For the actual binding-cut peel relation, reachability already implies the correct transversality:

- trivial decoration: no critical exceptional divisor;
- \(a=0\) or \(b=0\): vacuous by F3;
- \(a,b\ge1\): F2 gives \(p=0\) for the new critical component;
- earlier certified divisors are retained in the decoration history.

Hence, by induction on a legal peel history,

\[
\operatorname{Reachable}(D)\Longrightarrow\operatorname{Transverse}_{p=0}(D).
\]

There is no reachable non-transverse decoration at a binding divisor under F2–F3. Thus

\[
\operatorname{Reachable}(D)\wedge\operatorname{Transverse}_{p=0}(D)
\]

is logically just `Reachable(D)`. Transversality should be a theorem about the exact peel constructor.

Caveat: “reachable” must mean produced by the genuine algebraic peel, including its carrier and context—not merely having a syntactically plausible support matrix. Intersection refinements require the additional check below.

## Q3 — GAP

For terminal support \(e(i,\ell)\), write

\[
k_\ell=\min_i e(i,\ell).
\]

The actual `sjLoss_terminal` hypothesis is

\[
\exists i_0\ \forall\ell,\qquad e(i_0,\ell)=k_\ell.
\tag{T}
\]

This gives one residual generator identically equal to \(1\).

Divisorwise \(p=0\) normally gives only

\[
\forall\ell\ \exists i_\ell,\qquad e(i_\ell,\ell)=k_\ell.
\tag{P}
\]

The quantifiers cannot be exchanged. For example, take two generators

\[
g_1=x,\qquad g_2=y,
\]

with support vectors \((1,0)\) and \((0,1)\). Each coordinate divisor has a unit generator, but there is no single generator with support \((0,0)\). Indeed,

\[
g_1^2+g_2^2=x^2+y^2
\]

still vanishes at the intersection, and

\[
\int (x^2+y^2)^{-c'}\,dx\,dy
\]

diverges for \(c'\ge1\). Blowing up the intersection creates an exceptional divisor \(E\) with

\[
\nu_E(x)=\nu_E(y)=1,
\]

so \(p_E=1\). On the \(x\)-chart, however,

\[
x^2+y^2=x^2(1+v^2),
\]

and the residual generator \(1\) supplies (T).

Therefore:

- If “every critical divisor” includes all relevant combined/intersection valuations, the example is rejected and F1 gives mathematical finiteness.
- If only the original component divisors are checked, the predicate is TOO LOOSE.
- To invoke the present `sjLoss_terminal` lemma, one must additionally prove that terminal reachable charts have been refined enough to satisfy (T), or replace it with a terminal theorem using the full Newton/all-ray criterion.

There is no special \(b>2\) obstruction: \(p=\min_j\nu(g_j)\) is width-independent. Wide \(b\) only requires a finite entry/minor chart cover to select a uniformly nonvanishing generator. Generic full rank alone does not provide that uniform chart bound.

Also, \(p=0\) does not imply \(H_2\) is a unit; fortunately it need not. A unit \(H_1\) already makes \(H_1^2+v^2H_2^2\) bounded below.

## Q4

- **TOO-TIGHT: yes, definitively.** The \((3,3,2,2)\), \(t=2\) peel produces the reduced \((2,2,2)\) rank-one component described above. It has \(p=0\) but fails “\(Z_{\mathrm{deep}}\) full rank.”

- **TOO-LOOSE: no, if encoded correctly.** If the predicate really requires \(p_\eta=0\) for every critical divisorial valuation, including combined exceptional rays, F1 rules out a false base case.

- **GAP / potentially TOO-LOOSE as currently phrased.** Component-generic full rank does not quantify over intersection divisors and does not imply the simultaneous terminal hypothesis (T). The \(x,y\) support matrix is the minimal countertest.

## Clean encoding

The cleanest definition is the least family generated by the actual operations:

\[
\boxed{\operatorname{adm}(n,M,D):\Longleftrightarrow
D\text{ is reachable from }\operatorname{trivial}
\text{ by legal decorated peels and required chart refinements}.}
\]

Then prove, rather than store:

\[
\operatorname{adm}(D)\Rightarrow
\forall\eta\in\operatorname{Crit}(D),\ p_\eta=0,
\]

and

\[
\operatorname{adm}(D)\land D\text{ terminal}
\Rightarrow\text{terminal dehomogenisation or the all-ray terminal criterion}.
\]

The cheapest peel-closure regression test is the \((3,3,2,2)\to(2,2,2)\) rank-one component. The cheapest base-soundness test is the support matrix \(\{(1,0),(0,1)\}\); it catches the invalid \(\forall\eta\exists i\Rightarrow\exists i\forall\eta\) step immediately.