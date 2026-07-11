The proposed recursion is false as stated. A deeper rank drop can be the unique minimum-codimension degeneration. However, at a nondegenerate binding cut, a weaker transversality statement still forces the corank block to have generic full row rank.

## Q1

FALSE

- [DERIVED] For the reduced three-width chain \((u,m,n)\), write \(U\in\operatorname{Mat}_{u\times m}\), \(Z\in\operatorname{Mat}_{m\times n}\). On the rank-\(r\) stratum of \(Z\),

\[
\operatorname{codim}\{UZ=0,\ \operatorname{rank}Z=r\}
=(m-r)(n-r)+ur.
\]

The first term is the determinantal codimension; the second says that each of the \(u\) rows of \(U\) must lie in the \((m-r)\)-dimensional left kernel of \(Z\).

- [DERIVED] Take the reduced width

\[
(u,m,n)=(2,2,2).
\]

Then the rank-stratum codimensions are

\[
\begin{array}{c|ccc}
r=\operatorname{rank}Z&0&1&2\\ \hline
(2-r)^2+2r&4&3&4.
\end{array}
\]

Thus

\[
\minAdm(2,2,2)=3,
\]

and its unique top-dimensional component has

\[
\operatorname{rank}U=\operatorname{rank}Z=1.
\]

The deeper matrix necessarily rank-drops from generic rank \(2\) to rank \(1\).

- [DERIVED] This occurs at an actual binding cut. For

\[
M=(3,3,2,2),
\]

the four peel values are

\[
9,\quad 4+\minAdm(1,2,2)=6,\quad
1+\minAdm(2,2,2)=4,\quad
\minAdm(3,2,2)=4.
\]

Hence \(t^*=2\) is binding, with \(a=b=1\), and its reduced top component is precisely the rank-\((1,1)\) component above.

- [DERIVED] A rank drop does not itself force \(p>0\). If the generic deeper rank is \(r\), then for free \(A_{\mathrm{cor}}\),

\[
\operatorname{rank}(A_{\mathrm{cor}}Z)
=\min(b,r)
\]

generically. In the example \(b=r=1\), so the corank row remains nonzero and has valuation \(0\).

Therefore (i) and (iii) are false, as is the implication “deeper rank drop \(\Rightarrow p>0\).”

## Q2

CONDITIONAL

- [DERIVED] Theta multiplicity can include deeper-rank-drop components. For the reduced chain \((1,2,2)\), the two top-dimensional components are:

  - \(U=0\), with \(Z\) generically invertible, codimension \(2\);
  - \(\operatorname{rank}U=\operatorname{rank}Z=1\) and \(UZ=0\), also codimension \(2\).

Thus \(\theta_{\mathrm{red}}=2\), and one top component is a genuine deeper-rank-drop component.

- [DERIVED] Nevertheless, theta does not destroy generic corank transversality at a nondegenerate binding cut. Put

\[
C_t=\minAdm(t,M_2,\ldots,M_L).
\]

Let \(X\) be any top-dimensional component of \(Z_t\), and let \(r_X\) be the generic rank of \(Z_{\mathrm{deep}}\) on \(X\). Adding one new pivot row constrained by \(uZ_{\mathrm{deep}}=0\) costs exactly \(r_X\) equations, hence

\[
C_{t+1}\le C_t+r_X.
\]

If \(t\) is binding and \(a=M_0-t>0,\ b=M_1-t>0\), comparison with the admissible cut \(t+1\) gives

\[
ab+C_t\le(a-1)(b-1)+C_{t+1},
\]

so

\[
C_{t+1}-C_t\ge a+b-1.
\]

Consequently, on every top component,

\[
r_X\ge a+b-1\ge b.
\]

Therefore

\[
\operatorname{rank}(A_{\mathrm{cor}}Z_{\mathrm{deep}})=b
\]

generically on every top-dimensional component. Theta may introduce rank-drop components, but not component-generic \(p>0\), provided \(a>0\).

- [DERIVED] The hypothesis \(a>0\) is essential. For

\[
M=(2,3,2,1),\qquad t^*=2,
\]

we have \(a=0,b=1\), while the reduced chain \((2,2,1)\) has a top component \(Z=0\) of codimension \(2\). On that component \(A_{\mathrm{cor}}Z=0\) identically.

- [INFERRED] Generic full rank on every top component only proves \(p=0\) for divisors dominating those components. It does not automatically control exceptional divisors centered over proper rank-drop intersections; that requires the joint decorated resolution.

## Q3

FALSE

- [DERIVED] The numerical recursion for \(\minAdm\) is a valid arity descent and terminates. But geometrically it branches over all minimizing rank profiles. It cannot be replaced by the single branch “front block vanishes and the tail stays generic.”

- [DERIVED] The counterexample \((2,2,2)\) already stops the proposed induction: its first reduced top component is necessarily a simultaneous rank drop, not a pivot-vanishing component with generic tail.

- [DERIVED] The arity-two base itself is consistent. For \((u,n)\),

\[
\minAdm(u,n)=un,
\]

and the zero-product locus is the linear subspace where the sole \(u\times n\) matrix vanishes. In a parent peel, the complementary corank block is free and is generically full row rank when \(b\le n\).

- [DERIVED] At a nondegenerate binding base cut this capacity is automatic:

\[
n=C_{t+1}-C_t\ge a+b-1\ge b.
\]

Thus the useful \(p=0\) statement can be re-established at each nondegenerate binding step, but not by the proposed “generic deeper product at every level” argument.

## Q4

CONDITIONAL

- [DERIVED] The exact sufficient—and essentially necessary—condition is a strict rank-gap condition. For a reduced chain

\[
N=(u,n_1,\ldots,n_k),
\]

let

\[
d=\min_{1\le j\le k}n_j
\]

be the generic rank of the deeper product. Notice that in general this is not merely \(\min(n_1,n_k)\); internal bottlenecks matter.

For \(r<d\), the rank-shift formula gives

\[
D(r):=\operatorname{codim}\{\operatorname{rank}Z_{\mathrm{deep}}\le r\}
=\minAdm(n_1-r,\ldots,n_k-r).
\]

The incidence stratum with deeper rank \(r\) has codimension

\[
D(r)+ur.
\]

Hence every top component has generic deeper rank \(d\) exactly when

\[
\boxed{
D(r)>u(d-r)\qquad\text{for every }0\le r<d.
}
\]

Equality produces a theta-tied deeper-rank-drop component; reversal makes a deeper rank drop strictly dominant.

- [DERIVED] For a two-factor reduced locus \((u,m,n)\), this condition becomes

\[
(m-r)(n-r)>u(d-r)\quad(r<d),
\]

which simplifies to

\[
\boxed{|m-n|\ge u.}
\]

If one also wants the literal conclusion \(U=0\), rather than merely \(U\) annihilating a generic image, one needs the expanding case

\[
\boxed{n\ge m+u.}
\]

- [DERIVED] Mere monotonicity is insufficient. Even the strictly expanding chain \((2,2,3)\) has a tie: both generic rank \(2\) and rank \(1\) give codimension \(4\).

- [DERIVED] The supplied anchor \((1,3,4)\) satisfies \(4\ge3+1\). General DLN widths do not: \((2,2,2)\), and also the binding reduction \((2,4,4)\) inside \(M=(4,4,4,4)\), violate the condition.

## Lemma I would certify

At a binding cut \(t\) with \(a=M_0-t>0\) and \(b=M_1-t>0\), every top-dimensional component \(X\) of the reduced zero-product locus satisfies

\[
\operatorname{rank}_{\mathrm{gen},X}(Z_{\mathrm{deep}})
\ge a+b-1\ge b.
\]

Consequently, for free \(A_{\mathrm{cor}}\), the block \(A_{\mathrm{cor}}Z_{\mathrm{deep}}\) has generic row rank \(b\) on every such component, so its maximal-minor ideal has valuation \(0\) at the component’s generic point. No assertion that \(Z_{\mathrm{deep}}\) itself has generic full rank is valid in general.

The cheapest breaking computation is the table

\[
(2-r)^2+2r=(4,3,4),\qquad r=0,1,2,
\]

for the reduced chain \((2,2,2)\). It disproves the proposed strong recursion immediately.