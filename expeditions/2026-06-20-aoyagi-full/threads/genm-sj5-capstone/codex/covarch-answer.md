The clean decomposition is fibrewise leaf reduction plus a genuinely joint incidence resolution. Two cautions are load-bearing: generic full rank of \(Z_{\mathrm{deep}}\) does not make its Jacobian a bounded unit, and `chart5_bigcell_cov` is only a Schur shear—not yet the radial blow-up producing \(C_{\ell,s}\).

### Q1. Absorbing \(Z_{\mathrm{deep}}\)

Let
\[
G=ZZ^\top,\qquad S=G^{1/2},\qquad O=S^{-1}Z.
\]
Then \(OO^\top=I_{M_2}\) and \(Z=SO\). Define
\[
\widehat z_0=z_0S,\qquad \widehat A=A_{\rm cor}S.
\]
For \(\widehat\Pi=\widehat A^\top(\widehat A\widehat A^\top)^{-1}\widehat A\),
\[
\Pi_{Q_b}=O^\top\widehat\Pi O.
\]
Consequently, exactly:
\[
\det(Q_bQ_b^\top)=\det(\widehat A\widehat A^\top),
\]
\[
E_{\rm top}=\|P\widehat z_0+B_{12}\widehat A\|_F^2,
\]
and
\[
E_{\rm tr}
=\left\|C\bigl(\widehat z_0+P^{-1}B_{12}\widehat A\bigr)(I-\widehat\Pi)\right\|_F^2.
\]
Thus the \(n\)-column geometry disappears exactly.

The volume change is
\[
dz_0\,dA_{\rm cor}
=(\det G)^{-(u+b)/2}\,d\widehat z_0\,d\widehat A.
\]
There are no further \(\det G\) powers: the Gram charge and both energies transform exactly.

This is not a global bounded-unit reduction under merely generic full rank. The transformed boxes depend on \(G\), and \((\det G)^{-(u+b)/2}\) can blow up near the tail rank-drop locus. Generic full rank a.e. does not control integrability near that null set.

So:

- If \(G\ge\varepsilon I\) uniformly on the tail cell, the leaf reduction is valid up to bounded factors.
- Otherwise, retain \((\det G)^{-(u+b)/2}\) and the shrinking transformed boxes, and resolve them jointly with the tail variables.

A Lean-friendlier alternative to the square root is a dominant \(M_2\)-column minor:
\[
Z=T[I\mid X_Z],\qquad \widehat R=RT.
\]
Then the Jacobian is \(|\det T|^{-(u+b)}\), while \(I+X_ZX_Z^\top\) is a bounded unit on a dominant-minor cell. The \(|\det T|\)-singularity still belongs to the tail recursion.

### Q2. Correct CoV sequence

First use Tonelli to regard the expression as one joint lintegral in
\[
(z_{\rm tail},z_0,A_{\rm cor},P,B_{12},C).
\]
Do not prove finiteness of the \(x\)-fibre first.

For a leaf or uniformly elliptic tail cell:

1. **Column permutation for the chosen \(Q_b\)-minor.**  
   Measure-preserving, Jacobian \(1\).

2. **Corank minor chart**
   \[
   A_{\rm cor}=D[I_b\mid X].
   \]
   Genuine CoV:
   \[
   dA_{\rm cor}=|\det D|^d\,dD\,dX,\qquad d=M_2-b.
   \]
   With the charge, this gives \(|\det D|^{d-a}\) times an \(X\)-unit.

3. **Pivot-row shear**
   \[
   Q_p=[U\mid UX+W].
   \]
   Measure-preserving shear, Jacobian \(1\). This uses `transverseSchurGram`.

4. **Front change**
   \[
   H=PU+B_{12}D.
   \]
   This is not measure-preserving as a \(B_{12}\)-change:
   \[
   dB_{12}=|\det D|^{-u}\,dH.
   \]
   Then
   \[
   \widetilde H
   =H+PWX^\top(I+XX^\top)^{-1}
   \]
   is a measure-preserving translation. The loss becomes, up to \(X\)-units,
   \[
   \|\widetilde H\|^2+\|YW\|^2,\qquad Y=\binom PC.
   \]

5. **\(W\)- and \(Y\)-big-cell Schur coordinates.**  
   Row/column permutations have Jacobian \(1\). The changes
   \[
   W_{22}\leftrightarrow E=W_{22}-W_{21}W_{11}^{-1}W_{12}
   \]
   and the analogous \(Y\)-Schur change are measure-preserving shears. This is where `chart5_bigcell_cov` belongs.

6. **Actual projective/radial blow-up.**  
   This is a genuine Jacobian CoV and is not supplied by `chart5_bigcell_cov`. It must turn the joint normal blocks into radial variables with density \(r^{C_{\ell,s}-1}\).

7. **\(\widetilde H\)-scaling.**  
   If \(2q>ub\), use `chart4`:
   \[
   \widetilde H=\tau V,\qquad d\widetilde H=\tau^{ub}dV,
   \qquad \tau=\|YW\|.
   \]
   If \(2q<ub\), use a bounded-\(\widetilde H\) estimate instead. At \(2q=ub\), a logarithmic estimate or a small \(\varepsilon\)-loss is needed.

There is an additional obstruction: after step 4 the formal weight is
\[
|\det D|^{d-a-u}.
\]
Under the stated scope only \(d\ge a\), not \(d\ge a+u\). Hence enlarging the shrinking \(H\)-image to all of \(\mathbb R^{ub}\) can create a false divergence. A correct proof must retain the \(D\)-dependent \(H\)-image or perform a joint \(D\)-\(H\) tube resolution before `chart4`.

Thus the banked five charts do not yet constitute the full proof in the general scope.

### Q3. Codimension accounting

The conceptual normal blocks are:

| Contribution | Normal block |
|---|---|
| \(ub\) | the additive \(\widetilde H\)-block |
| \(M_0\ell\) | \(Y\) restricted to \(\operatorname{im}W\), which must vanish |
| \((M_0-s)(u-\ell-s)\) | Schur complement normal to rank \(s\) in the descended \(M_0\times(u-\ell)\) \(Y\)-block |
| \(s(d-\ell)\) | the part of the \(E\)-block detected linearly by the rank-\(s\) descended \(Y\) |

These sum to \(C_{\ell,s}\).

The determinant variables are separate. After restoring the shrinking \(H\)-volume, a triangular/SVD chart for \(D\) has schematic pivot densities
\[
\prod_{i=1}^b \delta_i^{\,d-a+2(i-1)}\,d\delta_i,
\]
which are finite because \(d\ge a\). If one discards the shrinking \(H\)-image, these exponents become \(d-a-u+2(i-1)\), which need not be integrable.

The four summands of \(C_{\ell,s}\) are dimensions of normal blocks, not four independent radial variables. Because \(\|YW\|^2\) is bilinear, the eventual resolution generally has several exceptional radii. In the corner \(u=a=b=1,d=2\),
\[
F\asymp \xi^2+\rho^2s^2,
\]
and one obtains two radial integrals, each governed by the same codimension \(C_{0,0}=3\). `chart5` alone does not produce these radii.

Also, `clsCodim_gate_genL` supplies the inequality
\[
q<C_{\ell,s}/2,
\]
which is all finiteness needs. An asserted equality of minima requires extra feasibility/tail hypotheses beyond that theorem.

### Q4. Is there a shorter route?

Not in the full scope with the sharp threshold.

Crude bounds such as
\[
\|YW\|\ge \sigma_{\min}(Y)\|W\|
\]
separate the variables too aggressively and miss the incidence strata. Binding strata can be interior: for \((M_0,M_1,M_2)=(3,3,3)\), \(u=2\), the minimum is attained at \(s=1\) or \(2\), not only at a corner.

A shorter route exists in the extra regime
\[
d-a-u\ge0.
\]
Then the \(H\)-image may safely be enlarged:

- \(2q<ub\): bounded \(H\)-fibre estimate;
- \(2q=ub\): logarithmic estimate;
- \(2q>ub\): `chart4`, followed by a pre-existing depth-two \(YW\) integrability theorem.

Outside that regime, either the full incidence/tube resolution or a theorem already encapsulating it is necessary.

### Q5. Lean atlas and null coverage

Use finite types of injective minor selectors, allowing harmless duplicates:
```lean
structure MinorIdx (m n k : ℕ) where
  rows : Fin k ↪ Fin m
  cols : Fin k ↪ Fin n
```
Then use dependent finite sums over \(\ell,s\) and their range proofs.

For bounded chart coordinates, use dominant-minor cells with a least-index tie-break, rather than arbitrary nonzero-minor charts. The banked `dominanceCell` pattern gives an exact measurable partition and avoids null seam arguments.

For coverage:

- Algebraically, use `Core.exists_square_minor` or `rank_le_iff_forall_submatrix_det_eq_zero`.
- For the deficient complement, form the sum of squares of all maximal minors. Its zero set is exactly the rank-deficient locus.
- Prove that polynomial nonzero using an explicit identity-block witness.
- Apply `MvPolynomial.volume_zeroSet_eq_zero` or `ae_matrix_eval_ne_zero`, transported through the matrix flattening equivalence.

One warning: exact lower-rank strata are null, but their neighborhoods cannot be discarded—they determine integrability. The atlas must consist of open/tubular recursive cells with Schur variables \(E\), not merely the sets `{rank W = ℓ}`.