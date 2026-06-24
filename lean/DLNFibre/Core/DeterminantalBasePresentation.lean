import DLNFibre.Core.DeterminantalBaseElimination
import DLNFibre.Core.DeterminantalChartRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.DeterminantalBasePresentation` — the localized base presentation `A_loc/Iad ≅ Sd`

The final identification of `G2-2`: the localized determinantal base ring `A_loc = Localization.Away
detΔ`, modulo its base ideal `Iad`, is the free Schur localization `Sd = Localization.Away detSchurS`
— a regular ring of dimension `δ`. The eliminated `B22` block (`B22 = B21 Δ⁻¹ B12`) is forced by the
Schur relation once `detΔ` is inverted.

**The route (Codex-vetted, thread-13 `codex-g22c-route` consult).** The localized block equivalence
`Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd` (localizing the LANDED `blockAlgEquiv` at `detΔ ↦
C detSchurS`) carries `Iad` to a prime of `MvPolynomial B22block Sd`. The forced-block graph ideal
`J = graphIdeal forcedB22` (the genuine forced value `B21 adjΔ B12 / detΔ ∈ Sd`) satisfies:

1. **`height J = C`** — the translation automorphism maps `J` to the coordinate ideal, whose height
   is `#B22block = C` (LANDED `height_coordIdeal_localization_eq`).
2. **`J ⊆ Ψ(Iad)`** — each generator `X_b − C(forcedB22 b)` is, up to the unit `C detSchurS`, the
   image under `Ψ` of the bordered `(r+1)`-minor (LANDED `det_submatrix_multPoly_mem_sigmaIdeal`),
   which lies in `Iad`. This carries the actual Schur content.
3. **`Iad = J`** — by `Ideal.height_strict_mono_of_is_prime` (both prime, `height Ψ(Iad) = height
   Iad = C = height J`, `J ⊆ Ψ(Iad)` ⟹ no strict containment ⟹ equal). This honestly **earns** the
   hard direction `Iad ⊆ J`.

Then `A_loc/Iad ≅ (MvPolynomial B22block Sd)/J ≅ Sd` via `graphIdealQuotientEquiv`. `J` stays
internal; the domain / dimension `δ` follow from `Sd` being a polynomial localization.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The localized block equivalence `Ψ`

`Sd := Localization.Away detSchurS`, `Q := MvPolynomial B22block Sd`. We use `Localization` (the
canonical localization) so the `k`-algebra instances on `Sd` and `Q` resolve automatically. -/

/-- The free Schur localization `Sd = Localization.Away detSchurS` — the downstream-composable base
ring (a regular ring of dimension `δ`). -/
abbrev SchurLoc (q p r : ℕ) : Type u :=
  Localization.Away (detSchurS (k := k) q p r)

/-- **The localized block equivalence** `Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd`, localizing the
LANDED `blockAlgEquiv` at `detΔ` (which maps to `C detSchurS`). `Sd = Localization.Away detSchurS`. -/
noncomputable def blockAlgEquivLoc (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Localization.Away (detPivotPoly (k := k) q p r hp hq)
      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
  -- the scalar tower `k → B → Q`
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) x
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) x) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]
    congr 1
  -- `Q` is the localization of `B` at `powers (C detSchurS)`
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r))
        (S := SchurLoc (k := k) q p r))
  have H : Submonoid.map (blockAlgEquiv (k := k) q p r hp hq)
        (Submonoid.powers (detPivotPoly q p r hp hq))
      = Submonoid.powers (C (detSchurS (k := k) q p r)) := by
    rw [Submonoid.map_powers, blockAlgEquiv_detPivot]
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (detPivotPoly (k := k) q p r hp hq))
    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
    (blockAlgEquiv q p r hp hq) H

/-! ## The bordered `(r+1)`-minor `m_b` and its `blockAlgEquiv` image `(*)`

For a `B22` entry `(a', b')` the bordered `(r+1)×(r+1)` minor `m_b` of the generic product (rows
`[pivots, r+a']`, columns `[pivots, r+b']`) lies in the base ideal (an `(r+1)`-minor), and under
`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
identity, transported). Dividing by the unit `C detSchurS` lands `X (a', b') − C (forcedB22 …)` in
`Ψ(Iad)`. -/

/-- The four blocks of the bordered minor at the `B22` entry `(a', b')` (entries are coordinate
variables of `multPoly`). Pivot block `Δ`, pivot-row × non-pivot-col `u`, non-pivot-row × pivot-col
`v`, corner `d`. The non-pivot index is the landed reindex form `Fin.cast (natAdd r ·)`. -/
noncomputable def borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin r) (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i j ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i) (Fin.castLE hq j)

noncomputable def borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i _ ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i)
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

noncomputable def borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ j ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')) (Fin.castLE hq j)

noncomputable def borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    Matrix Unit Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ _ ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a'))
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

/-- The `SchurVar`-side pivot block `ΔS` (whose determinant is `detSchurS`). -/
noncomputable def schurΔ (q p r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i j ↦ X (Sum.inl (i, j))

/-- The `SchurVar`-side `B12` column `uS` at non-pivot column `b'` (the `b'`-th column of `B12`). -/
noncomputable def schurU (q p r : ℕ) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i _ ↦ X (Sum.inr (Sum.inl (i, b')))

/-- The `SchurVar`-side `B21` row `vS` at non-pivot row `a'` (the `a'`-th row of `B21`). -/
noncomputable def schurV (q p r : ℕ) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun _ j ↦ X (Sum.inr (Sum.inr (a', j)))

/-- The bordered minor `m_b`: the determinant of the `multPoly` submatrix on rows `[pivots, r+a']`
and columns `[pivots, r+b']`. -/
noncomputable def borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) : MvPolynomial (RepCoord (dStratum q p)) k :=
  ((Matrix.of (multPoly (dStratum q p))).submatrix
    (Sum.elim (fun i : Fin r ↦ Fin.castLE hp i)
      (fun _ : Unit ↦ Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')))
    (Sum.elim (fun j : Fin r ↦ Fin.castLE hq j)
      (fun _ : Unit ↦ Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b')))).det

/-- The bordered minor is the determinant of `fromBlocks borderΔ borderU borderV borderD`. -/
theorem borderMinor_eq_fromBlocks (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    borderMinor (k := k) q p r hp hq a' b'
      = (Matrix.fromBlocks (borderΔ (k := k) q p r hp hq) (borderU q p r hp hq b')
          (borderV q p r hp hq a') (borderD q p r hp hq a' b')).det := by
  rw [borderMinor]
  congr 1
  refine Matrix.ext (fun i j ↦ ?_)
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr,
      borderΔ, borderU, borderV, borderD, Matrix.of_apply]

/-- **The bordered minor lies in the base ideal `sigmaIdeal`** (it is an `(r+1)`-minor of the generic
product, `det_submatrix_multPoly_mem_sigmaIdeal` after the `Fin r ⊕ Unit ≃ Fin (r+1)` reindex). -/
theorem borderMinor_mem_sigmaIdeal (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    borderMinor (k := k) q p r hp hq a' b' ∈ sigmaIdeal (k := k) (dStratum q p) r := by
  rw [borderMinor]
  set e : (Fin r ⊕ Unit) ≃ Fin (r + 1) :=
    (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv with he
  rw [← det_submatrix_equiv_self e.symm, submatrix_submatrix]
  exact det_submatrix_multPoly_mem_sigmaIdeal (dStratum q p) _ _

/-- Each bordered block maps under `blockAlgEquiv` to the `C`-image of its `SchurVar`-side block (the
landed coordinate-image lemmas), or to the `B22` corner variable. -/
theorem blockAlgEquiv_borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (borderΔ (k := k) q p r hp hq).map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurΔ (k := k) q p r).map C := by
  refine Matrix.ext (fun i j ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderΔ, Matrix.of_apply, multPoly_stratum_apply,
    schurΔ, Matrix.of_apply]
  exact blockAlgEquiv_X_pivot q p r hp hq i j

theorem blockAlgEquiv_borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    (borderU (k := k) q p r hp hq b').map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurU (k := k) q p r b').map C := by
  refine Matrix.ext (fun i u ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderU, Matrix.of_apply, multPoly_stratum_apply,
    schurU, Matrix.of_apply]
  exact blockAlgEquiv_X_b12 q p r hp hq i b'

theorem blockAlgEquiv_borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    (borderV (k := k) q p r hp hq a').map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurV (k := k) q p r a').map C := by
  refine Matrix.ext (fun u j ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderV, Matrix.of_apply, multPoly_stratum_apply,
    schurV, Matrix.of_apply]
  exact blockAlgEquiv_X_b21 q p r hp hq a' j

theorem blockAlgEquiv_borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    (borderD (k := k) q p r hp hq a' b').map (blockAlgEquiv (k := k) q p r hp hq)
      = Matrix.of fun _ _ : Unit ↦ (X (a', b') : MvPolynomial (B22block q p r)
          (MvPolynomial (SchurVar q p r) k)) := by
  refine Matrix.ext (fun u v ↦ ?_)
  rw [Matrix.map_apply, borderD, Matrix.of_apply, multPoly_stratum_apply, Matrix.of_apply]
  exact blockAlgEquiv_X_b22 q p r hp hq a' b'

/-- The numerator bridge: the bordered Schur numerator (row `a'` of `B21`, `adjugate Δ`, column `b'`
of `B12`) is the `(a', b')` entry of the full `forcedNum = B21 · adjugate Δ · B12`. -/
theorem schurNum_eq_forcedNum (q p r : ℕ) (a' : Fin (p - r)) (b' : Fin (q - r)) :
    (schurV (k := k) q p r a' * (schurΔ (k := k) q p r).adjugate * schurU (k := k) q p r b')
        default default
      = (forcedNum (k := k) q p r) a' b' := by
  rw [forcedNum, schurΔ, schurU, schurV]
  simp [Matrix.mul_apply]

/-- **`(*)` the bordered Schur minor identity, transported.** `blockAlgEquiv (m_b) =
C detSchurS · X (a', b') − C (forcedNum a' b')`. Via `AlgEquiv.map_det` + `Matrix.fromBlocks_map` +
`det_fromBlocks_scalar_eq` on the mapped (`SchurVar`-`C`) blocks; `det (ΔS.map C) = C detSchurS`,
the numerator collapses to `C (forcedNum a' b')` (`schurNum_eq_forcedNum`). -/
theorem blockAlgEquiv_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    blockAlgEquiv (k := k) q p r hp hq (borderMinor q p r hp hq a' b')
      = C (detSchurS (k := k) q p r) * X (a', b') - C ((forcedNum (k := k) q p r) a' b') := by
  rw [borderMinor_eq_fromBlocks, AlgEquiv.map_det, AlgEquiv.mapMatrix_apply,
    Matrix.fromBlocks_map, blockAlgEquiv_borderΔ, blockAlgEquiv_borderU, blockAlgEquiv_borderV,
    blockAlgEquiv_borderD, det_fromBlocks_scalar_eq, Matrix.of_apply,
    show ((schurΔ (k := k) q p r).map C).det = C (detSchurS (k := k) q p r) from
      (RingHom.map_det C (schurΔ (k := k) q p r)).symm,
    show ((schurΔ (k := k) q p r).map C).adjugate = ((schurΔ (k := k) q p r).adjugate).map C from
      (RingHom.map_adjugate _ _).symm,
    ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, schurNum_eq_forcedNum, mul_comm]

/-! ## Step (2): `J ⊆ Ψ(Iad)` — the localized inclusion

`Ψ` carries `algebraMap A_eng A_loc x` to `algebraMap B Q (blockAlgEquiv x)`
(`algEquivOfAlgEquiv_eq`). Each generator `X (a',b') − C (forcedB22 (a',b'))` of `J`, multiplied by
the unit `C (algebraMap detSchurS)`, is the `Ψ`-image of the bordered minor (in `Iad`), so it lies in
`Ψ(Iad)`; dividing by the unit gives the generator. -/

/-- `Ψ` intertwines the two localization maps: `Ψ (algebraMap A_eng A_loc x) = algebraMap B Q
(blockAlgEquiv x)`. (`Ψ = IsLocalization.algEquivOfAlgEquiv blockAlgEquiv`.) -/
theorem blockAlgEquivLoc_algebraMap (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (x : MvPolynomial (RepCoord (dStratum q p)) k) :
    blockAlgEquivLoc (k := k) q p r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
          (Localization.Away (detPivotPoly (k := k) q p r hp hq)) x)
      = algebraMap (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
          (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
          (blockAlgEquiv (k := k) q p r hp hq x) := by
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun y ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) y
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) y) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) y
        = C (algebraMap k (SchurLoc (k := k) q p r) y) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]; congr 1
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r)) (S := SchurLoc (k := k) q p r))
  exact IsLocalization.algEquivOfAlgEquiv_eq _ x

/-- The localized base ideal `Iad = (sigmaIdeal …).map (algebraMap A_eng A_loc)`: the determinantal
base ideal pushed into the localized base ring `A_loc = Localization.Away detΔ`. -/
noncomputable def Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Ideal (Localization.Away (detPivotPoly (k := k) q p r hp hq)) :=
  (sigmaIdeal (dStratum q p) r).map
    (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
      (Localization.Away (detPivotPoly (k := k) q p r hp hq)))

/-- **The cleared Schur relation in `Q = MvPolynomial B22block Sd`.** The unit `C (algebraMap
detSchurS)` times the graph generator `X (a',b') − C (forcedB22 (a',b'))` equals
`Ψ (algebraMap A_eng A_loc (borderMinor …))` — the `Ψ`-image of a bordered minor (hence in
`Ψ(Iad)`). The `mk'` denominator clears: `algebraMap detSchurS · forcedB22 = algebraMap forcedNum`. -/
theorem unit_mul_graphGen_eq_psi_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
          (detSchurS (k := k) q p r))
        * (X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b')))
      = blockAlgEquivLoc (k := k) q p r hp hq
          (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
            (Localization.Away (detPivotPoly (k := k) q p r hp hq))
            (borderMinor q p r hp hq a' b')) := by
  rw [blockAlgEquivLoc_algebraMap, blockAlgEquiv_borderMinor, map_sub, map_mul]
  simp only [algebraMap_def, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [mul_sub]
  congr 1
  rw [← C_mul]
  congr 1
  rw [forcedB22,
    IsLocalization.mk'_spec' (SchurLoc (k := k) q p r) ((forcedNum (k := k) q p r) a' b')
      (⟨detSchurS q p r, Submonoid.mem_powers _⟩ : Submonoid.powers (detSchurS (k := k) q p r))]

/-- **Step (2): `J ⊆ Ψ(Iad)`.** Each generator `X (a',b') − C (forcedB22 (a',b'))` of the forced
graph ideal lies in `Ψ(Iad)`: it is the unit `C (algebraMap detSchurS)⁻¹` times the `Ψ`-image of the
bordered minor (which is in `Iad`, `borderMinor_mem_sigmaIdeal`). -/
theorem graphIdeal_forcedB22_le_map_Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))
      ≤ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) := by
  rw [graphIdeal, Ideal.span_le]
  rintro _ ⟨ab, rfl⟩
  obtain ⟨a', b'⟩ := ab
  show X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b'))
      ∈ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
  -- the generator, times the unit `C (algebraMap detSchurS)`, is `Ψ (algebraMap borderMinor) ∈ Ψ(Iad)`
  have hunit : IsUnit (C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
      (detSchurS (k := k) q p r)) : MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) :=
    (IsLocalization.Away.algebraMap_isUnit (detSchurS (k := k) q p r)).map
      (C : SchurLoc (k := k) q p r →+* _)
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, unit_mul_graphGen_eq_psi_borderMinor q p r hp hq a' b']
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (borderMinor_mem_sigmaIdeal q p r hp hq a' b'))

/-! ## Step (3): the height squeeze `Iad = J` and the presentation `A_loc/Iad ≅ Sd`

Both `Ψ(Iad)` and `J = graphIdeal forcedB22` are prime of height `C`, and `J ⊆ Ψ(Iad)`
(step 2). `Ideal.height_strict_mono_of_is_prime` rules out `J ⊊ Ψ(Iad)`, so `J = Ψ(Iad)` — this
**earns** the hard direction `Iad ⊆ Ψ.symm J` (= injectivity). The presentation `A_loc/Iad ≅ Sd`
then follows from `graphIdealQuotientEquiv`. -/

/-- **`Ψ(Iad) = J`** (`[IsAlgClosed k] [CharZero k]`): the height squeeze. Both ideals are prime; the
landed `height Iad = C` (transported by `Ψ`) and `height J = C` are equal; `J ⊆ Ψ(Iad)` (step 2)
plus `height_strict_mono_of_is_prime` forces equality. This is the honest hard direction. -/
theorem map_Iad_eq_graphIdeal_forcedB22 [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
  set K : Ideal Q := ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) with hK
  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
  -- both ideals are prime
  haveI hsigmaPrime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
  haveI hIadPrime : ((Iad (k := k) q p r hp hq)).IsPrime := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem
        (detPivotPoly (k := k) q p r hp hq) hsigmaPrime.isRadical).2
      (detPivotPoly_notMem_sigmaIdeal q p r hp hq)
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (S := Localization.Away (detPivotPoly (k := k) q p r hp hq))
      (Submonoid.powers (detPivotPoly q p r hp hq))
      (sigmaIdeal (dStratum q p) r) hsigmaPrime hdisj
  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
  haveI : IsDomain (SchurLoc (k := k) q p r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (detSchurS_ne_zero (k := k) q p r))
  haveI hJprime : J.IsPrime := graphIdeal_isPrime _
  -- `height K = height Iad` (Ψ an equiv); `height Iad = C` (landed); `height J = C` (landed)
  have hKIad : K.height = ((Iad (k := k) q p r hp hq)).height :=
    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
  have hIadC : ((Iad (k := k) q p r hp hq)).height = ((q - r) * (p - r) : ℕ) := by
    rw [Iad, height_map_sigmaIdeal_away_eq_cCodim q p r hp hq
        (kostantPartitions_stratum_nonempty q p r hq hp), cCodim_stratum_eq q p r hq hp
        (kostantPartitions_stratum_nonempty q p r hq hp), Int.toNat_natCast]
  have hheightJ : J.height = ((p - r) * (q - r) : ℕ) :=
    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
  have hJK : J.height = K.height := by
    rw [hheightJ, hKIad, hIadC, Nat.mul_comm]
  -- the squeeze: `J ⊆ K`, equal finite heights, both prime ⟹ `J = K`
  refine (eq_of_le_of_not_lt (graphIdeal_forcedB22_le_map_Iad q p r hp hq) (fun hlt ↦ ?_)).symm
  haveI : J.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hheightJ]; exact ENat.coe_ne_top _
  exact absurd ((Ideal.height_strict_mono_of_is_prime hlt).trans_le hJK.ge)
    (lt_irrefl _)

/-- **The localized base presentation `A_loc / Iad ≅ₐ[k] Sd`** (`G2-2`). The localized determinantal
base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`. Via
the height squeeze `Ψ(Iad) = J` (`map_Iad_eq_graphIdeal_forcedB22`) and the graph-ideal quotient
`Q ⧸ J ≅ Sd` (`graphIdealQuotientEquiv`, the `B22`-block elimination). -/
noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] SchurLoc (k := k) q p r := by
  have e₁ : (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
    Ideal.quotientEquivAlg ((Iad (k := k) q p r hp hq))
      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      (blockAlgEquivLoc (k := k) q p r hp hq)
      (map_Iad_eq_graphIdeal_forcedB22 q p r hp hq).symm
  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      ≃ₐ[k] SchurLoc (k := k) q p r :=
    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
  exact e₁.trans e₂

end DLNFibre.Core
