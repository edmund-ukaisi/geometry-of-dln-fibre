Bottom line: the recursion is well-founded after adding two natural transition rules, but it is not fully rigorous exactly as stated. The missing pieces are the precise Case 1(1) label update and the empty-residual boundary \(J=\min(\mu_S,M^{(S+1)})\). Case 2 is also described too aggressively if one blow-up is claimed to advance \(S\) immediately.

Write

\[
m_s:=M^{(s)},\qquad
\mu_S:=\min_{r\le S}m_r,\qquad
K_S:=\min(\mu_S,m_{S+1})=\mu_{S+1}.
\]

## Q1. A decreasing measure

Let \(U\) be the finite set of currently live exceptional coordinates and define

\[
N(S,J):=\#\{u\in U:\widetilde t(u)>J\}.
\]

The required Case 1(1) transition rule is:

- the selected coordinate has \(\widetilde t=h=J+J_1\);
- it is relabelled \(\widetilde t=J\);
- no new exceptional coordinate is introduced and no other label above \(J\) is created.

Then the lexicographic measure

\[
\Phi(S,J,U)
   :=\bigl(L+1-S,\ K_S-J,\ N(S,J)\bigr)\in\mathbb N^3
\]

strictly decreases:

| Branch | Decreasing component |
|---|---|
| Case 1(1) | \(N\mapsto N-1\) |
| Case 1(2), same \(S\) | \(K_S-J\mapsto K_S-J-1\) |
| Case 1(2), layer completed | \(L+1-S\) decreases |
| Case 2 as a macro-step | \(L+1-S\) decreases |
| Case 2 as one-pivot local step | \(K_S-J\) decreases, until the layer boundary |

Equivalently, use the ordinal

\[
\omega^2(L+1-S)+\omega(K_S-J)+N(S,J).
\]

The bounds on \(S\) and \(J\) control only the outer recursion. They do not by themselves exclude infinitely many Case 1(1) steps at fixed \((S,J)\). Finiteness and strict decrease of \(N\) are essential.

A warning: the statement “the count at the current slot decreases” is not alone sufficient, because after that slot empties the first nonempty slot may move. Counting all labels above \(J\) fixes this, provided the selected label really moves down to \(J\).

## Q2. Case 1(1) termination

For \(h=J+J_1\), the initial count is

\[
c_h=\#\{u:\widetilde t(u)=h\}.
\]

It is history-dependent; the dimensions do not determine its exact value. Case 1 guarantees \(c_h\ge1\), since

\[
\frac{b_{h+1}}{b_h}
 =\prod_{\widetilde t(u)=h}u
\]

is nontrivial.

It is finite because only finitely many exceptional coordinates have been introduced. With coordinates indexed as \(u_{s,k}\), a safe global bound is

\[
\#U\le \sum_{s=1}^L m_{s+1},
\]

and the sharper pivot-indexed bound is \(\sum_s K_s\). At fixed \((S,J)\), all Case 1(1) repetitions together are bounded by \(N(S,J)\), not merely by the count at one slot.

Thus it cannot fire unboundedly once “no new \(u\) in Case 1(1), and the chosen label moves to \(J\)” is explicitly included. Without that clause, termination is under-specified.

## Q3. Exhaustiveness and boundary cases

For an active state \(J<K_S\), the dichotomy is exhaustive:

- If the remaining \(b\)'s are all equal, Case 2 applies.
- Otherwise let \(h\) be the first index with \(b_{h+1}\ne b_h\). Then \(J_1=h-J\), uniquely, and Case 1 applies.

The \(J_1=1\) case is valid. The equal run consists of the single term \(b_{J+1}\); the intermediate empty-level condition is vacuous, and the break supplies a coordinate with \(\widetilde t=J+1\).

The problematic state is \(J=K_S\):

- if \(K_S=\mu_S\), the residual block has zero rows;
- if \(K_S=m_{S+1}<\mu_S\), it has zero columns.

No nontrivial blow-up should occur there. One needs an explicit boundary transition

\[
(S,K_S)\longrightarrow(S+1,0),
\]

or should advance \(S\) immediately when the last pivot is extracted. Treating an empty residual block as Case 2 would mean blowing up an empty coordinate ideal or the whole space.

In particular, \(J=\mu_S\) is not an ordinary Case-2 state: the list \(b_{J+1},\ldots,b_{\mu_S}\) is empty.

There is also a base-state indexing defect: \(\mu_0\) is undefined, and taking \(D_0=\prod C^{(s)}\) while retaining the displayed tail product duplicates the product. The clean formulation starts at \(S=1,J=0\) with \(D_0=C^{(1)}\) and tail \(C^{(2)}\cdots C^{(L)}\), or declares \(S=0\) as a separate exceptional base convention.

## Q4. Comparability

Comparability is not part of the decreasing measure. Scalar labels and their finite downward movement suffice for termination of a suitably modified algorithm.

It is nevertheless used by the stated construction: Case 1 should choose a coordinate whose vector \(T\) is least among those with the same \(\widetilde t\). A finite totally ordered set has such a least element. Without comparability, a finite partial order may have several incomparable minimal elements and no element below all the others.

Therefore:

- geometrically, one could likely choose an arbitrary \(u\), perform the coordinate blow-up, and retain termination;
- formally, the stated recursive invariant would no longer be closed, and the specified least-choice step could become unavailable;
- the label-chain description and subsequent RLCT candidate formula would require a new proof.

So comparability is not merely decorative RLCT bookkeeping, although it is not what makes the numerical recursion well-founded.

## Q5. Under-specified steps

### (a) Choice of \(u_{s,k}\)

Existence follows from the break in the \(b\)-sequence. To preserve the vector invariant, the choice should be:

\[
T_{s,k}\le T_{s',k'}
\quad\text{for every }u_{s',k'}\text{ at the same slot}.
\]

Total comparability supplies this least element. One still needs a lemma proving that the Case 1(1) and Case 1(2) label updates preserve total comparability. “Choose any \(u\)” is not sufficient.

The \(d\)-pivot charts also form a finite family—one for each center coordinate. Saying “one \(d\)-entry becomes \(1\)” should be accompanied by the row/column permutations showing that these charts have the same normal form.

### (b) Advancing through Case 2

A single radial blow-up of the full residual matrix produces one unit pivot and, after regular elimination,

\[
D_J'\sim
\begin{pmatrix}
1&0\\0&D_{J+1}
\end{pmatrix}.
\]

That ordinarily advances \(J\) by one; it does not resolve an arbitrary residual block in one operation. Thus “Case 2 advances \(S\)” must mean the finite iteration of this pivot step until \(J=K_S\), or it is incomplete.

After layer completion, the new effective free matrix has dimensions

\[
\mu_{S+1}\times m_{S+2},
\]

not necessarily \(m_{S+1}\times m_{S+2}\). When \(\mu_{S+1}<m_{S+1}\), the unused rows of the original \(C^{(S+1)}\) are smooth nuisance variables. Their separation and their differentials must be recorded.

### (c) Monomial and Jacobian preservation

This is not automatic and needs chart calculations.

For Case 1, the center contains

\[
q=J_1(m_{S+1}-J)
\]

matrix entries plus the old \(u\). In the \(u\)-chart the Jacobian gains \(u^q\). In a \(d\)-pivot chart, substitution of the old Jacobian power and the radial Jacobian gives the advertised accumulated exponent.

For Case 2, if the actual residual block is \((\mu_S-J)\times(m_{S+1}-J)\), then

\[
q=(\mu_S-J)(m_{S+1}-J)
\]

and the radial chart contributes \(u^{q-1}\).

The subsequent \(P,Q\) operations must separately be shown to be invertible regular transformations with unit determinant. Regularity of entries such as \(b_i/b_{J+1}\) follows from the divisibility chain \(b_{J+1}\mid b_i\), but that argument should be stated.

## Q6. Actual width versus prefix minimum

There is a notation collision: in the setup \(M(S)\) already means the prefix minimum. Reading “actual width” as \(m_S=M^{(S)}\), the two proposed exponents are

\[
q_{\mathrm{actual}}=(m_S-J)(m_{S+1}-J),
\qquad
q_{\mathrm{prefix}}=(\mu_S-J)(m_{S+1}-J).
\]

Their difference is

\[
q_{\mathrm{actual}}-q_{\mathrm{prefix}}
=(m_S-\mu_S)(m_{S+1}-J).
\]

For active states \(J<K_S\), they diverge exactly when \(m_S>\mu_S\): an earlier layer was a strict bottleneck and the current width has risen above it. This includes monotone increasing chains; it is not limited to globally nonmonotone chains. Example:

\[
(m_1,m_2,m_3)=(2,4,4),\quad S=2,\quad J=0:
\qquad 16\ \text{versus}\ 8.
\]

Effects:

1. Termination: unaffected; the exponent is not used by the measure.
2. Normal-crossing monomialization: unaffected if the coordinate map really blows up the effective \(\mu_S\)-row block. The actual Jacobian remains monomial.
3. Numerical exponents/RLCT: affected. The actual-width formula overcounts by the displayed difference and can change the minimum candidate or its multiplicity. Harmlessness for the final RLCT would require a separate proof that these Case-2 divisors never minimize.

If the actual-width expression is meant literally as the dimension of the blow-up center, rather than merely being a printed bookkeeping formula, it is more serious: it refers to rows that are absent after an earlier bottleneck, so the coordinate construction itself is not defined.

Thus the termination argument is repairable and cleanly well-founded, but the supplied account does not yet constitute a fully specified recursive proof.