/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartPsiDsigUnit

/-!
# `DLNFibre.Core.ChartPhiSubstitution` — the Φ-direction comorphism substitution (seam D, part 1)

Seam D of the route-β localized chart `AlgEquiv` (thread 31), Φ direction — the mirror of the Ψ
substitution (`ChartPsiSubstitution`). The comorphism of the **forward** chart map
`Φ(A) = (mult A, chartGauge(mult A) • A)`, as a `k`-algebra hom into the **source** localization
`Localization.Away dsig` (which localizes the chart-closure coordinate ring `O(Σ^r)`).

The construction is the exact mirror of the Ψ side (Codex `seam-d-architecture-answer`, route-β,
the independent-`aevalTower` shape):

- `sigmaCoordT : RepCoord d → Away dsig` — the source-coordinate embedding (mirror of `fibCoordT`):
  `X x ↦ algebraMap O(Σ^r) (Away dsig) (mk_Σ (X x))`.
- `chartPhiVarSub : SchurVar → Away dsig` — the var leg: each Schur generator maps to the
  corresponding block entry of the deep generic product `M = Matrix.of (multPoly d)` (Δ at the pivot
  rows/cols, `B12`/`B21` at the bordering rows/cols), pushed into `Away dsig`. The mirror of the
  Ψ-side's `map_chartPsiAeval_multPoly_eq` reading the Schur blocks off `L · E · H`.
- `chartPhiSchurAeval := aeval chartPhiVarSub : MvPolynomial SchurVar k →ₐ[k] Away dsig`, with
  `chartPhiSchurAeval detSchurS = algebraMap O(Σ^r) (Away dsig) dsig` (the deep pivot minor `ΔPdeep`
  is the determinant of the Δ-block of `M`, the inverted element — a unit).
- `schurToDsig : SchurLoc →ₐ[k] Away dsig` — the connecting map (mirror of `schurToGfib`), the
  `IsLocalization.liftAlgHom` of `chartPhiSchurAeval` (inverts `detSchurS` because its image is the
  unit `dsig`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

variable (k) in
/-- **The source-coordinate embedding** `sigmaCoordT : RepCoord d → Localization.Away dsig` (mirror
of `fibCoordT`): a coordinate `x` maps to the `O(Σ^r)`-class of `X x`, pushed into the source
localization. The image of the chart point's coordinates under the Φ comorphism's identity-on-`Σ`
leg. -/
noncomputable def sigmaCoordT (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    RepCoord d → Localization.Away (chartDsig k d r hp hq) :=
  fun x ↦ algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
    (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)) (X x))

variable (k) in
/-- **The Φ var leg** `chartPhiVarSub : SchurVar → Localization.Away dsig`: each Schur generator maps
to the corresponding block entry of the deep generic product `M = Matrix.of (multPoly d)`, pushed
into `Away dsig`. Δ-block (`Sum.inl`) at pivot rows/cols (`castLE`), `B12` (`Sum.inr ∘ Sum.inl`) at
pivot row / bordering col, `B21` (`Sum.inr ∘ Sum.inr`) at bordering row / pivot col. -/
noncomputable def chartPhiVarSub (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    SchurVar (d 0) (d (Fin.last (N + 1))) r → Localization.Away (chartDsig k d r hp hq) :=
  fun s ↦ algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
    (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r))
      (match s with
        | Sum.inl (i, j) => multPoly d (Fin.castLE hp i) (Fin.castLE hq j)
        | Sum.inr (Sum.inl (i, b)) =>
            multPoly d (Fin.castLE hp i)
              (Fin.cast (show r + (d 0 - r) = d 0 by omega) (Fin.natAdd r b))
        | Sum.inr (Sum.inr (a, j)) =>
            multPoly d (Fin.cast (show r + (d (Fin.last (N + 1)) - r) = d (Fin.last (N + 1)) by omega)
              (Fin.natAdd r a)) (Fin.castLE hq j)))

variable (k) in
/-- The var leg on a Δ-block generator `Sum.inl (i, j)` is the pivot-block entry
`mk_Σ (multPoly (castLE i) (castLE j))` pushed into `Away dsig`. -/
theorem chartPhiVarSub_inl (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (i j : Fin r) :
    chartPhiVarSub k d r hp hq (Sum.inl (i, j))
      = algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
          (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r))
            (multPoly d (Fin.castLE hp i) (Fin.castLE hq j))) := rfl

variable (k) in
/-- **The Φ Schur comorphism** `chartPhiSchurAeval : MvPolynomial SchurVar k →ₐ[k] Away dsig`:
`aeval` of the var leg. Carries the Schur-variable polynomials to the corresponding products of
generic-product block entries (over `Away dsig`). -/
noncomputable def chartPhiSchurAeval (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    MvPolynomial (SchurVar (d 0) (d (Fin.last (N + 1))) r) k →ₐ[k]
      Localization.Away (chartDsig k d r hp hq) :=
  MvPolynomial.aeval (chartPhiVarSub k d r hp hq)

variable (k) in
/-- **The Φ Schur comorphism carries `detSchurS` to the inverted element `dsig`.** `detSchurS` is the
determinant of the Δ-coordinate matrix; under `chartPhiSchurAeval` (= `aeval chartPhiVarSub`) each
`Δ`-coordinate `Sum.inl (i, j)` reads the `(castLE i, castLE j)` entry of the deep generic product
`M`, so the matrix is the `algebraMap`-image of the `castLE`-submatrix of `M`, whose determinant is
`mk_Σ ΔPdeep = dsig` (the deep pivot minor). Hence `chartPhiSchurAeval detSchurS = algebraMap dsig`,
a unit (the inverted element of the source localization). -/
theorem chartPhiSchurAeval_detSchurS (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    chartPhiSchurAeval k d r hp hq (detSchurS (d 0) (d (Fin.last (N + 1))) r)
      = algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
          (chartDsig k d r hp hq) := by
  -- the composite ring hom `g = algebraMap ∘ mk : MvPolynomial (RepCoord d) k → Away dsig`.
  set g : MvPolynomial (RepCoord d) k →+* Localization.Away (chartDsig k d r hp hq) :=
    (algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))).comp
      (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r))) with hg
  set Msub : Matrix (Fin r) (Fin r) (MvPolynomial (RepCoord d) k) :=
      ((Matrix.of (multPoly d)).submatrix
      (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last (N + 1)))))
      (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0)))) with hMsub
  -- RHS: `algebraMap dsig = g ΔPdeep` and `g ΔPdeep = det (Msub.map g)` (`g` commutes with `det`).
  have hRdsig : algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsig k d r hp hq))
        (chartDsig k d r hp hq) = g (ΔPdeep d r hp hq) := by
    rw [hg, RingHom.comp_apply, chartDsig]
  have hRmap : g (ΔPdeep d r hp hq) = (Msub.map g).det := by
    rw [ΔPdeep, ← hMsub]
    exact RingHom.map_det g Msub
  rw [hRdsig, hRmap]
  -- LHS `chartPhiSchurAeval detSchurS = det (var-leg Δ-matrix)`; compare the two matrices entrywise.
  rw [detSchurS, chartPhiSchurAeval, AlgHom.map_det]
  congr 1
  funext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, aeval_X, Matrix.map_apply,
    hMsub, Matrix.submatrix_apply, Matrix.of_apply, hg, RingHom.comp_apply, chartPhiVarSub_inl]

variable (k) in
/-- **The connecting map** `schurToDsig : SchurLoc →ₐ[k] Localization.Away dsig` (mirror of
`schurToGfib`): the `IsLocalization.liftAlgHom` of the Φ Schur comorphism `chartPhiSchurAeval`,
inverting `detSchurS` because its image `algebraMap dsig` is a unit (the inverted element of the
source localization). Carries the `SchurLoc`-coefficient gauge into the source target ring. -/
noncomputable def schurToDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
      Localization.Away (chartDsig k d r hp hq) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (detSchurS (d 0) (d (Fin.last (N + 1))) r))
    (f := chartPhiSchurAeval k d r hp hq)
    (by
      rintro ⟨y, n, rfl⟩
      rw [map_pow]
      rw [chartPhiSchurAeval_detSchurS]
      exact (isUnit_algebraMap_chartDsig d r hp hq).pow n)

end DLNFibre.Core
