Let \(B_j\) denote the chart at node \(j\), and put
\[
S_j=C_j\setminus\{\pi_j\},\qquad
y_j=B_{j+1}\circ\cdots\circ B_m(w),
\]
so \(y_m=w\).

## Q1. Pulling an intermediate pivot back to the source

For any cell \(c\),
\[
z_c(y_j)
=
z_c(w)\prod_{\substack{\ell>j\\c\in S_\ell}}
z_{\pi_\ell}(y_\ell).
\tag{1}
\]

Thus
\[
\boxed{
z_{\pi_j}(y_j)
=
z_{\pi_j}(w)
\prod_{\substack{\ell>j\\\pi_j\in C_\ell\setminus\{\pi_\ell\}}}
z_{\pi_\ell}(y_\ell).
}
\tag{2}
\]

This becomes a source-coordinate monomial by recursively expanding every factor on the right. Explicitly,
\[
z_c(y_j)
=
z_c(w)
\prod_{\substack{
r\ge1,\ j<\ell_1<\cdots<\ell_r\le m\\
c\in S_{\ell_1}\\
\pi_{\ell_t}\in S_{\ell_{t+1}}\ (t<r)
}}
z_{\pi_{\ell_r}}(w).
\tag{3}
\]
If several chains end at the same source coordinate, its exponent is the number of such chains.

Under the usual freshness and coordinate-consistency assumptions:

- case-2 nodes do not alter existing divisor coordinates;
- case-1(1) merge nodes do not alter their referenced divisor coordinate because it is their pivot;
- case-1(2) split nodes do alter their parent coordinate:
  \[
  z_u\longmapsto z_ez_u.
  \]

Consequently, \(z_{\pi_j}(y_j)\) is \(z_{\pi_j}(w)\) times the source coordinates of all later split-descendants of that divisor. In the split tree each descendant occurs once.

## Q2. Comparison with the ledger monomial

The equality is true provided:

1. every fresh block is disjoint from all existing live-divisor cells except the explicitly included \(u\);
2. a divisor is always referenced by the same cell that was its actual birth pivot;
3. there are no unlisted divisor deletions;
4. the initial Jacobian and initial ledger agree, for example both are \(1\).

Let
\[
L=\prod_k z_{\operatorname{coord}_k}^{D_k-1}.
\]
Suppose the Jacobian before adding a deeper node equals \(L\). By the chain rule, adding chart \(B\) gives
\[
J_{\rm new}(w)=L(B(w))\,J_B(w).
\]

Writing \(b=\mathrm{runLen}\,\mathrm{resCols}\):

- Birth: existing ledger variables are spectators, and \(J_B=p^{b-1}\). This adds the factor \(p^{b-1}\).

- Merge: \(u\) is the pivot, so \(L(B(w))=L(w)\), while \(J_B=u^b\). Hence
  \[
  u^{D-1}u^b=u^{D+b-1}.
  \]

- Split: \(u\mapsto eu\) and \(J_B=e^b\). Therefore
  \[
  u^{D-1}\longmapsto (eu)^{D-1},
  \]
  and
  \[
  (eu)^{D-1}e^b
  =
  u^{D-1}e^{D+b-1},
  \]
  exactly matching the old divisor \(u\) and the new divisor \(e\) with exponent \(D+b\).

Hence the ledger identity follows inductively under these assumptions.

### Concrete \(2\times2\) birth followed by a \(1\times1\) split

Let the root block be \(\{A,B,C,D\}\), with pivot \(A\), and source variables \(a,b,c,d\). Let the deeper split have center \(\{A,E\}\), pivot \(E\), with source variable \(e\).

The composite map on these coordinates is
\[
(a,b,c,d,e)
\longmapsto
(ea,eab,eac,ead,e).
\]

The root atom is evaluated after the split:
\[
z_A(y_1)^3=(ea)^3.
\]
The split atom is \(e^{2-1}=e\). Thus
\[
\boxed{J_\Phi=a^3e^4.}
\]

The final ledger has
\[
D_A=4,\qquad D_E=4+1=5,
\]
so
\[
a^{D_A-1}e^{D_E-1}=a^3e^4.
\]

For a split block of general size \(b\), the same calculation gives
\[
J_\Phi=a^3e^{3+b}
      =a^{4-1}e^{(4+b)-1}.
\]

## Q3. Origin of the inherited exponent

The split node’s own atom contributes only
\[
e^b,
\]
because its center has size \(1+b\).

The inherited factor \(e^{D_A-1}\) comes from the older atoms containing \(A\), pulled back through
\[
A\longmapsto eA.
\]

In the \(2\times2\) example, the old case-2 atom is \(A^3\), and after the split it becomes
\[
(eA)^3=A^3e^3.
\]
Thus the root atom supplies \(e^3=D_A-1\), while the split atom supplies \(e^b\). The total is
\[
e^{D_A-1+b}=e^{D_A+b-1}.
\]

## Q4. Off-diagonal birth pivot versus diagonal reference

Let \(P\) be the off-diagonal birth pivot and \(D\neq P\) the diagonal cell later used as `mergeIdx`. Write
\[
p=z_P(w),\qquad d=z_D(w).
\]
Suppose the deeper merge adds a fresh block of size \(b\), with center
\[
\{D\}\cup F
\]
and pivot \(D\).

Because \(P\) is not in that merge center, it is a spectator:
\[
z_P(y_1)=p.
\]
Therefore
\[
\boxed{J_\Phi=p^3d^b.}
\]

But the ledger, naming \(P\) as the divisor coordinate and updating its exponent from \(4\) to \(4+b\), gives
\[
\boxed{L=p^{3+b}.}
\]

These are unequal monomials. The actual Jacobian replaces the expected factor \(p^b\) by \(d^b\):
\[
J_\Phi=L\left(\frac d p\right)^b
\]
formally on the coordinate torus. For the smallest merge, \(b=1\),
\[
J_\Phi=p^3d,\qquad L=p^4.
\]

Equality is restored precisely when the divisor’s actual birth pivot is the same cell later used as its canonical reference—e.g. all births choose the designated diagonal cell as pivot. Equivalently, later nodes may consistently reference the actual off-diagonal pivot instead.