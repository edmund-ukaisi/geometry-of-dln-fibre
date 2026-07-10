**Math Correction**

The bound with
\[
w^{-(c'-pr/2)}
\]
is the **above-threshold residual-power atom**, so it requires
\[
c' > pr/2.
\]
It cannot hold below threshold. If \(c'<pr/2\), the box integral has a finite nonzero limit as \(w\to0\), while \(w^{pr/2-c'}\to0\).

So the right statement is piecewise:

- **Subcritical terminal bound:** \(c'<pk/2\): finite uniformly in \(w\), no residual power.
- **Residual-power peel:** \(c'>pk/2\): gives \(w^{-(c'-pk/2)}\).

Here \(k\) should mean **peeled stiff rank**, not necessarily algebraic rank.

**Box Corank Atom**

Let \(G=RR^t\), and choose an orthogonal Gram diagonalisation
\[
O\,G\,O^t=\operatorname{diag}(\sigma_1^2,\dots,\sigma_q^2).
\]
With \(Z=\Gamma O^t\),
\[
\|\Gamma R\|_F^2=\sum_{i=1}^q \sigma_i^2 \|Z_i\|_{\mathbb R^p}^2.
\]

Choose a stiff set \(J\subseteq\{1,\dots,q\}\), \(|J|=k\), with \(\sigma_i>0\) for \(i\in J\). Put \(B=\sqrt q\,T\), since the orthogonal rotation sends the original box into \([-B,B]^{p\times q}\). Then, for \(c'>pk/2\),
\[
\int_{\Gamma\in[-T,T]^{p\times q}}
(w+\|\Gamma R\|_F^2)^{-c'}\,d\Gamma
\le
(2B)^{p(q-k)}
\left(\prod_{i\in J}\sigma_i^{-p}\right)
C_{\mathrm{resid}}(pk,c')\,
w^{-(c'-pk/2)}.
\]

The soft directions \(i\notin J\) contribute only the box-volume factor \((2B)^{p(q-k)}\). No factor
\[
\det(RR^t)^{-p/2}
\]
appears. In particular, if \(\sigma_i\to0\) in a soft direction, the bound is unchanged.

If you only know \(\sigma_i\ge\delta\) on the stiff set, use the cruder Lean-friendly form
\[
(2B)^{p(q-k)}\delta^{-pk}
C_{\mathrm{resid}}(pk,c')w^{-(c'-pk/2)}.
\]

For \(c'<pk/2\), the correct endpoint is instead a finite box bound, e.g.
\[
I_R(w,T)\le (2B)^{p(q-k)}\delta^{-2c'}K_{pk,c',B},
\]
with no \(w\)-residual power.

**Lean Shape**

Do not start with full SVD. The clean proof should be split into two layers.

1. Prove a coordinate atom over already-split coordinates:
```lean
Γ : Fin p → (Fin k ⊕ Fin s) → ℝ
```
with stiff weights `σ : Fin k → ℝ` and a nonnegative soft energy that is dropped.

Target theorem shape:
```lean
theorem box_stiff_soft_residual_le
    (σ : Fin k → ℝ) (hσ : ∀ i, 0 < σ i)
    (hc : (p * k : ℝ) / 2 < c') (hw : 0 < w) :
  ∫⁻ Z in splitBox p k s B,
    ENNReal.ofReal ((w + stiffEnergy σ Z + softEnergy Z) ^ (-c'))
  ≤ ENNReal.ofReal
      ((2*B)^(p*s) *
       (∏ i : Fin k, (σ i ^ p)⁻¹) *
       Cresid (p*k) c' *
       w ^ (-(c' - (p*k : ℝ)/2)))
```

2. Wrap it for matrices using a Gram split:
```lean
structure GramStiffSplit (R : Matrix (Fin q) (Fin n) ℝ) where
  O : Matrix (Fin q) (Fin q) ℝ
  orth_left  : O * Oᵀ = 1
  orth_right : Oᵀ * O = 1
  e : Fin q ≃ Fin k ⊕ Fin s
  sigma : Fin k → ℝ
  soft : Fin s → ℝ
  diag :
    reindexed (O * (R * Rᵀ) * Oᵀ)
      = diagonal (Sum.elim (fun i => sigma i ^ 2) (fun j => soft j ^ 2))
```

Then prove the matrix theorem by `Γ ↦ Γ Oᵀ`, box enlargement, energy diagonalisation, and the coordinate atom.

**Bricks**

Use the local banked pieces:

- `Cresid`, `radial_morse_residual_power_le`: [RadialResidualPower.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RadialResidualPower.lean:26)
- `eMatFlat`, `matBox_corank_residual_le`: [RouteMSJCorankResidual.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankResidual.lean:53)
- `rightMulₚ`, determinant/Jacobian for right multiplication: [RouteMSJGammaAtom.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGammaAtom.lean:48)
- subcritical joint endpoint: [RouteMSJCorankPure.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankPure.lean:87)

Mathlib side: `Matrix.IsHermitian.spectral_theorem` is enough if you want exact \(\sigma_i\). Full SVD is unnecessary. For a lighter first implementation, assume the `GramStiffSplit` as data and later instantiate it from the spectral theorem.

**A′ Integration**

After the inner bound, the outer integral has the shape
\[
\int_{A'} \Pi_J(A')^{-p}\, w(A')^{-e}\,dA',
\qquad
e=c'-pk/2,
\]
where
\[
\Pi_J(A')=\prod_{i\in J}\sigma_i(Q_b(A')).
\]

Near a rank-drop locus of codimension \(D\), if locally
\[
\Pi_J(A')\sim \rho^\beta,\qquad w(A')\sim \rho^\gamma,
\]
then the radial normal integral is controlled by
\[
\int_0^\epsilon \rho^{D-1-p\beta-\gamma e}\,d\rho,
\]
so convergence needs
\[
p\beta+\gamma e < D.
\]

If \(w\) is bounded below, this reduces to \(p\beta<D\). The key improvement is that soft singular values are not in \(\Pi_J\), so collapsing directions do not create a full-Gram determinant pole.

**Uncertainties**

The exact singular-value wrapper at opaque `Fin q` rank `r` will be cast-heavy. I would first prove the split-index theorem over `Fin k ⊕ Fin s`, then add a `Fin q` reindexing wrapper. Exact box volume \((2B)^{p s}\) can also be deferred behind `volume (matBox p s B)` if needed.