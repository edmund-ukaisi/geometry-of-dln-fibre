Verdict: after the necessary compact localization, there is no strict tube-exponent wall:
\[
L=D.
\]
The pushforward can lower the exponent relative to Lebesgue measure on a free output matrix, but not below the algebraic codimension in factor space.

As written over the whole factor space, the tube has infinite Lebesgue volume because reciprocal rescalings of adjacent factors preserve the product. Below, “volume” means inside a fixed bounded neighborhood, or against a smooth compactly supported density bounded above and below there. Also, logs mean the correct statement is \(t^{L+o(1)}\), not always \(\sim Ct^L\).

## Q1 — PROVEN

Let \(b=\min_i m_i\). For \(0\le s\le b\),
\[
\boxed{
D=\operatorname{codim}\{\operatorname{rank}(A_1\cdots A_{L-1})\le s\}
=C(m_1-s,\ldots,m_L-s)
=\operatorname{minAdm}(m_1-s,\ldots,m_L-s).
}
\]

Thus the Core/type-\(A\) quiver codimension of the reduced chain is exactly \(D\).

Mechanism:

- The full-product rank is the multiplicity of the longest interval module.
- Remove \(s\) longest intervals. The remaining representation has widths \(m_i-s\) and zero full product.
- The longest interval is projective-injective, so adding or removing it preserves the normal slice and orbit codimension.
- Exact rank \(s\) is dense in the rank-\(\le s\) locus.

This is the paper’s [add-longest theorem](/home/ubuntu/workspace/geometry-of-dln-fibre/paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:682) and [rank-shift lemma](/home/ubuntu/workspace/geometry-of-dln-fibre/paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:816), together with the [QIP formula](/home/ubuntu/workspace/geometry-of-dln-fibre/paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1138).

If \(s\ge b\), rank \(P\le s\) identically, so
\[
\boxed{D=0.}
\]
For \(s>b\), ordinary reduced widths \(m_i-s\) can be negative and `minAdm` is not literally defined; extend the formula by the convention “zero once a bottleneck is exhausted.”

### \((3,3,4)\), \(s=1\)

Reduced widths are \((2,2,3)\). The QIP is
\[
e_1+e_2=2,\qquad
G=e_1^2+e_1e_2+e_2^2+e_2.
\]
At \((0,2),(1,1),(2,0)\), its values are \(6,4,4\). Hence
\[
\boxed{D=C(2,2,3)=4.}
\]

There are two top-dimensional components.

### \((3,3,3,4)\), \(s=1\)

Reduced widths are \((2,2,2,3)\). With \(e_1+e_2+e_3=2\),
\[
G=\frac{4+e_1^2+e_2^2+e_3^2}{2}+e_3.
\]
The six values are \(6,4,4,4,3,4\); the unique minimum is at \((1,1,0)\). Therefore
\[
\boxed{D=C(2,2,2,3)=3.}
\]

## Q2 — DERIVED: no strict power reduction

Define \(T(m_1,\ldots,m_L;s)\) as the inverse-moment threshold for \(\sigma_{s+1}(P)\) on bounded factor sets. The exact rank-flag peeling identity is
\[
T(m_1,\ldots,m_L;s)
=
\min_{j=s,\ldots,r}
\left[(m_1-s)(j-s)+T(m_2,\ldots,m_L;j)\right],
\]
where \(r=\min(m_2,\ldots,m_L)\).

Here is the multiscale argument that rules out fractional walls.

Write the positive singular values of the tail product \(Q\) on a dyadic shell as
\[
\sigma_i(Q)\asymp t^{\beta_i},
\qquad
0\le\beta_1\le\cdots\le\beta_r\le1.
\]
A simultaneous rank-flag pivot decomposition gives the uniform shell exponent
\[
I_Q(\beta)
=
\sum_{j=0}^{r-1}
T(m_2,\ldots,m_L;j)(\beta_{j+1}-\beta_j),
\qquad \beta_0=0.
\]

This is stronger than knowing the marginal rank-tube exponents. It is proved simultaneously by induction on the number of factors:

- For one free matrix it is the ordinary SVD Jacobian.
- On each dominant pivot chart, Gaussian elimination splits pivot coordinates from transverse coordinates.
- If a pivot degenerates, one passes to the corresponding lower-rank chart; hence angular alignment costs are included rather than discarded.
- A finite union supplies the uniform upper estimate, while a dominant chart supplies the matching lower estimate. Pivot ties contribute at most logarithms.

Conditioned on this tail shell, multiplying by a free \(m_1\times m_2\) factor costs
\[
(m_1-s)\sum_{i=s+1}^r(1-\beta_i).
\]
Indeed, after choosing an \(s\)-column pivot, every remaining column has \(m_1-s\) transverse coordinates that must be \(O(t^{1-\beta_i})\).

The total exponent is affine on the ordered \(\beta\)-simplex. Its vertices are precisely
\[
(\beta_1,\ldots,\beta_r)=(0,\ldots,0,1,\ldots,1),
\]
indexed by an integer effective rank \(j\). At that vertex the exponent is
\[
T(m_2,\ldots,m_L;j)+(m_1-s)(j-s).
\]
Thus an interior multiscale configuration cannot produce a smaller power; a flat minimizing face produces only logarithms.

Substituting the induction hypothesis
\[
T(m_2,\ldots,m_L;j)
=C(m_2-j,\ldots,m_L-j)
\]
and putting \(k=j-s\) gives
\[
T
=
\min_k\left[
(m_1-s)k+
C(m_2-s-k,\ldots,m_L-s-k)
\right].
\]
This is exactly the front-peel formula for \(C(m_1-s,\ldots,m_L-s)\). Therefore
\[
\boxed{L=T=D.}
\]

So the answer to the wall question is:

\[
\boxed{\textbf{NO: }L\text{ cannot be strictly smaller than }D.}
\]

Logs can occur. For \((3,3,4),s=1\), the reduced model is \(X_{2\times2}Y_{2\times3}\), and the two minimizing cuts tie:
\[
\operatorname{vol}\{\sigma_2(A_1A_2)\le t\}
\asymp t^4\log(1/t).
\]
Thus \(L=4=D\), although a literal \(Ct^4\) asymptotic is false.

For \((3,3,3,4),s=1\),
\[
\boxed{L=D=3.}
\]

For the narrow example \((3,1,3)\):

- \(s=1\): \(\sigma_2(P)\equiv0\), hence \(D=L=0\).
- \(s=0\): \(P=uv^\top\), so \(\sigma_1(P)=\|u\|\|v\|\), and
  \[
  \operatorname{vol}\{\sigma_1(P)\le t\}
  \asymp t^3\log(1/t).
  \]
  Hence \(D=L=3\).

Multiple algebraic components do not by themselves determine the logarithmic power; the log is controlled by tied resolution/scale candidates.

## Q3 — YES relative to a free output matrix; NO relative to \(D\)

A free \(m_1\times m_L\) matrix has rank-\(\le s\) tube exponent
\[
(m_1-s)(m_L-s).
\]

The product pushforward instead has
\[
\boxed{L=C(m_1-s,\ldots,m_L-s),}
\]
which can be strictly smaller.

For example, with \((3,3,4)\), \(s=1\),
\[
L_{\mathrm{free}}=(3-1)(4-1)=6,
\qquad
L_{\mathrm{product}}=4.
\]

Thus the pushforward really does concentrate mass near the determinantal locus. But it lowers the power exactly to the factor-space codimension \(D\), not below it.

## Q4 — DERIVED

Let \(t=\min_{i\ge1}m_i\). The exact front-peel identity is
\[
\boxed{
\operatorname{minAdm}(m_0,m_1,\ldots,m_L)
=
\min_{0\le j\le t}
\left[
m_0j+\operatorname{minAdm}(m_1-j,\ldots,m_L-j)
\right].
}
\]

Geometrically, on the tail-rank-\(j\) stratum:

- the tail contributes codimension \(C(m_1-j,\ldots,m_L-j)\);
- \(A_0P=0\) imposes exactly \(m_0j\) independent linear conditions.

Therefore, when \(s=q-1\le t\),
\[
\boxed{
\operatorname{minAdm}(m_0,\ldots,m_L)
\le D+m_0(q-1).
}
\]
It is precisely the \(j=q-1\) competitor.

It is tight exactly when \(j=q-1\) is a minimizing cut, not universally. For
\[
(m_0,m_1,m_2,m_3)=(3,3,3,4),
\]
the charges for \(j=0,1,2,3\) are
\[
8,\ 7,\ 7,\ 9.
\]
Thus \(q=2\) is tight:
\[
7=3+4,
\]
while \(q=1\) is strict:
\[
7<8.
\]

If \(s>t\), then \(D=0\) and \(j=s\) is inadmissible; choosing \(j=t\) gives
\[
\operatorname{minAdm}(m_0,\ldots,m_L)
\le m_0t\le m_0s.
\]