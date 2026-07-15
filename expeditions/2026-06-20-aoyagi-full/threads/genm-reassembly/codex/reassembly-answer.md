### Q1

**FACT — the coarea Jacobian is \(\operatorname{pdet}(ZZ^{T})^{-b/2}\), but a fixed-box integral is not a determinant-only function of \(Z\).**

Write the rank-\(k\) SVD
\[
Z=U_k D V_k^{T},\qquad D=\operatorname{diag}(s_1,\ldots,s_k),
\]
and define
\[
\Delta_k(Z):=\operatorname{pdet}(ZZ^{T})
 =\det(D^2)=\prod_{i=1}^k s_i^2.
\]
When \(M_2>k\), the full determinant \(\det(ZZ^T)\) is identically zero and must not be used.

For the rowwise map
\[
L_Z:A\in\mathbb R^{b\times M_2}\longmapsto AZ\in\mathbb R^{b\times k},
\]
the normal Jacobian is
\[
J(L_Z)=\Delta_k(Z)^{b/2}.
\]
Thus, exactly,
\[
I_\Omega(Z)
=\Delta_k(Z)^{-b/2}
 \int_{\mathbb R^{b\times k}}
 \det(XX^T)^{-a/2}\,\rho_{\Omega,Z}(X)\,dX,
\]
where \(\rho_{\Omega,Z}(X)\) is the \((M_2-k)b\)-dimensional volume of the corresponding fibre inside the original box.

Consequently:

- The exact coarea prefactor is \(\boxed{\Delta_k(Z)^{-b/2}}\).
- The remaining integral still depends on the singular values, singular subspaces, and transformed box through \(\rho_{\Omega,Z}\).
- Therefore, for a fixed box,
  \[
  I_\Omega(Z)\ne C\,\Delta_k(Z)^{-b/2}
  \]
  in general.

The scalar-scaling identity makes this unavoidable:
\[
I_\Omega(tZ)=|t|^{-ab}I_\Omega(Z),
\]
whereas
\[
\Delta_k(tZ)^{-b/2}=|t|^{-bk}\Delta_k(Z)^{-b/2}.
\]
The transformed-domain/fibre integral supplies the difference \(t^{b(k-a)}\).

The singular-value/Selberg density for \(X\in\mathbb R^{b\times k}\) gives
\[
dX\asymp
\prod_{i=1}^b\lambda_i^{(k-b-1)/2}
\prod_{i<j}|\lambda_i-\lambda_j|\,d\lambda\,d\mu,
\]
while
\[
\det(XX^T)^{-a/2}=\prod_i\lambda_i^{-a/2}.
\]
Hence, for a box meeting the rank-deficient locus,
\[
\boxed{b\le k,\qquad a<k-b+1}
\]
is the exact convergence criterion. Equivalently,
\[
\frac a2<\operatorname{lct}\det(XX^T)
=\frac{k-b+1}{2}.
\]
Equality gives logarithmic divergence. If \(a>0\) and \(b>k\), the Gram determinant vanishes identically. The case \(a=0\) is separately trivial.

---

### Q2

**FACT — after row-space coarea and a \(Z\)-uniform leaf estimate, an uncompensated**
\[
\boxed{\Delta_k(Z)^{-b/2}}
\]
**remains.**

Let
\[
h_q(Q_p,Q_b)
=\det(Q_bQ_b^T)^{-a/2}\operatorname{frontLoss}(Q_p,Q_b).
\]
Changing both \(A_0'\) and \(A_{\rm cor}\) to row-\(Z\) coordinates gives
\[
G_Z
=\Delta_k(Z)^{-(u+b)/2}
 \int h_q(X_pV_k^T,X_bV_k^T)\,
 \rho_{0,Z}(X_p)\rho_{b,Z}(X_b)\,dX_p\,dX_b.
\]
By comparison,
\[
\int_{A_0'}\|A_0'Z\|^{-2q}\,dA_0'
=\Delta_k(Z)^{-u/2}
 \int\|X_p\|^{-2q}\rho_{0,Z}(X_p)\,dX_p.
\]

Equivalently, changing only \(A_{\rm cor}\), and then applying the asserted leaf bound,
\[
\int_{X_b,\mathrm{front}}
 h_q(Q_p,X_bV_k^T)\rho_{b,Z}(X_b)
 \le C_q\|Q_p\|^{-2q},
\]
gives
\[
\boxed{
G_Z\le
C_q\,\Delta_k(Z)^{-b/2}
\int_{A_0'}\|A_0'Z\|^{-2q}\,dA_0'.
}
\]

The exact box-domain identity can contain partial compensation through its shrinking image, but once the leaf integral is standardized or extended uniformly, the coarea factor above survives. There is no general cancellation against the \(A_0'\) Jacobian.

A useful obstruction is \(Z=tZ_0\):
\[
G_{tZ_0}=|t|^{-ab-2q}G_{Z_0},\qquad
\mathrm{Comp}_{tZ_0}=|t|^{-2q}\mathrm{Comp}_{Z_0}.
\]
Thus, when \(ab>0\), their slice ratio grows as \(|t|^{-ab}\). No \(Z\)-uniform unweighted comparison can hold near \(Z=0\).

**FACT — the residual is option (ii): integrable for some geometries and not others.** It is harmless only if \(b=0\), or \(\Delta_k(Z)\) is uniformly bounded below, as for a fixed identity factor.

For a general product map \(Z=\Phi(\theta)\), its exact local criterion is
\[
\boxed{
\frac b2<
\operatorname{lct}_{\theta}
\bigl(\Delta_k(\Phi(\theta))\bigr).
}
\]
This depends on the entire deep chain, not merely on \(a,b,k\). The parameter \(a\) does not enter this residual criterion.

For a single free \(m\times n\) matrix \(Z\), \(k=\min(m,n)\), and
\[
\operatorname{lct}\Delta_k(Z)=\frac{|m-n|+1}{2}.
\]
Therefore
\[
\boxed{b<|m-n|+1}
\]
is necessary and sufficient; equality is logarithmically divergent. In particular, for square \(k\times k\) \(Z\), every positive integer \(b\) fails.

At a width-\(k\) bottleneck, \(Z=LR\) with \(L\in\mathbb R^{m\times k}\) and \(R\in\mathbb R^{k\times n}\),
\[
\boxed{
\Delta_k(LR)=\det(L^TL)\det(RR^T).
}
\]
Hence square \(k\times k\) factors produce the usual determinant threshold \(b<1\), showing explicitly why genuine products can make the residual nonintegrable.

**INFERENCE — the supplied induction hypothesis does not constructively prove \(G<\infty\) for a genuine deep product.**

Finiteness of
\[
\int \|A_0'Z\|^{-2q}
\]
does not imply finiteness after multiplication by the unbounded fixed-exponent weight \(\Delta_k(Z)^{-b/2}\). A separate weighted local-zeta estimate would be needed.

The safe corrected comparator is
\[
\boxed{
\int_{\mathrm{deep},A_0',v_0}
|v_0|^{\minAdm(M')-1-2q}\,
\Delta_k(Z)^{-b/2}\,
\bigl(\|A_0'Z\|_F^2\bigr)^{-q}.
}
\]
For \(q>0\), the combined \(q\)-dependent loss can equivalently be written as
\[
\left[
\Delta_k(Z)^{\,b/(2q)}
\|A_0'Z\|_F^2
\right]^{-q},
\]
but the determinant exponent itself is the fixed charge \(-b/2\), independent of \(q\).

If the deep product is trivial, \(Z=I_n\) or another fixed nonsingular matrix, \(\Delta_k(Z)^{-b/2}\) is a constant and the original comparator is adequate. A variable scalar factor is not harmless.

---

### Q3

**FACT — frame DROPPABLE, provided \(d_v\) is the intrinsically controlled slice of \(Y\), not all entries of \(Y\).**

Let
\[
W\in\mathbb R^{s\times t},\qquad
Y\in\mathbb R^{r\times s},\qquad
\sigma=\|W\|_F,
\]
and let \(\tau_1\) be the largest singular value of \(W\). With
\[
p=\min(s,t),
\qquad
\tau_1^2\ge \frac{\sigma^2}{p}.
\]
Choose an intrinsic leading left singular vector \(e_1(W)\). Then
\[
\boxed{
\|YW\|_F^2
=\operatorname{tr}(YWW^TY^T)
\ge\tau_1^2\|Ye_1\|^2
\ge\frac{\sigma^2}{p}\|Ye_1\|^2.
}
\]
The change \(Y\mapsto(Ye_1,Y_\perp)\) is orthogonal and has Jacobian one. The \(Y_\perp\) variables contribute only bounded volume. No externally supplied pivot frame or Loewner floor is required.

Thus the two-block lemma applies with
\[
\boxed{
d_u=\dim\widetilde H,\qquad
d_v=r=\dim(Ye_1),
}
\]
not \(d_v=rs=\dim Y\). Using all \(rs\) variables would require a uniform Loewner bound \(WW^T\gtrsim\sigma^2I_s\).

Since \(d_W=st\), choose
\[
\boxed{
\max(0,2q-d_u)<\alpha'<\min(d_v,d_W).
}
\]
The bank yields \(C\sigma^{-\alpha'}\), and intrinsic polar coordinates in \(W\) give
\[
\int_0^\varepsilon
\sigma^{d_W-1-\alpha'}\,d\sigma<\infty
\quad\Longleftrightarrow\quad
\alpha'<d_W.
\]
Equivalently, such an \(\alpha'\) exists precisely when
\[
2q<d_u+\min(d_v,d_W).
\]

So the corner closes by the bank plus outer \(W\)-radial integration, using only the leading singular direction supplied intrinsically by \(W\).