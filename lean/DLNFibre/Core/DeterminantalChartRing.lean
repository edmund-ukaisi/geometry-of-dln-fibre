import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Rename
import DLNFibre.Core.RankLocusClosed
import DLNFibre.Core.MultComorphism
import DLNFibre.Core.SigmaComponents

/-!
# `DLNFibre.Core.DeterminantalChartRing` — the bordered Schur minor (G2-2 foundation)

The ring-level lift of G2-1's matrix Schur relation. The genuinely new piece is the **bordered
Schur minor identity**, valid over any commutative ring (no invertibility of the pivot block):

> `det [[Δ, u], [v, d]] = d · det Δ − (v · adjugate Δ · u)`  (the `r×r` block `Δ`, a column `u`,
> a row `v`, a scalar corner `d`).

This is the polynomial that, on the determinantal locus `Mat^{rk ≤ r}`, forces the Schur relation
`B22 = B21 Δ⁻¹ B12` once `det Δ` is inverted: each entry `d·B22_{ab} − (B21 adjΔ B12)_{ab}` is an
`(r+1)×(r+1)` minor, hence vanishes on `Σ̄^r` (rank `≤ r`). It is the generator-free handle on the
localized base presentation — it avoids any determinantal-ideal generating-set theory (absent in
Mathlib v4.29), reducing the base presentation to this single explicit minor + height comparison.

**The route to the identity (no `Invertible Δ`).** Both sides are integer-polynomial identities in
the entries: over the universal `MvPolynomial` matrix ring (a domain) the identity holds in the
fraction field, where `Δ` is invertible and `det_fromBlocks₁₁` applies; specialize back by the ring
hom into the target. We use the `mul_adjugate` form (`Δ · adjΔ = det Δ • 1`) so the statement makes
sense over any commutative ring.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {α : Type u} [CommRing α] {r : ℕ}

/-! ## The bordered Schur minor identity (over any commutative ring) -/

/-- The bordered Schur minor identity as a predicate on the four blocks, so it transfers along ring
homs (`fromBlocks`, `det`, `adjugate`, `*`, `-` all commute with `RingHom.mapMatrix`). -/
def BorderedId {β : Type*} [CommRing β] (Δ : Matrix (Fin r) (Fin r) β) (u : Matrix (Fin r) Unit β)
    (v : Matrix Unit (Fin r) β) (d : Matrix Unit Unit β) : Prop :=
  (fromBlocks Δ u v d).det = d () () * Δ.det - (v * Δ.adjugate * u) () ()

/-- `BorderedId` holds over a field when the pivot is nonsingular (`det Δ ≠ 0`), via the Mathlib
Schur determinant `det_fromBlocks₁₁` and the adjugate relation `det Δ • Δ⁻¹ = adjugate Δ`. -/
theorem borderedId_of_det_ne_zero {K : Type*} [Field K] (Δ : Matrix (Fin r) (Fin r) K)
    (u : Matrix (Fin r) Unit K) (v : Matrix Unit (Fin r) K) (d : Matrix Unit Unit K)
    (hΔ : Δ.det ≠ 0) : BorderedId Δ u v d := by
  haveI : Invertible Δ := Δ.invertibleOfIsUnitDet (Ne.isUnit hΔ)
  unfold BorderedId
  rw [det_fromBlocks₁₁,
    show (d - v * ⅟Δ * u).det = (d - v * ⅟Δ * u) () () from by simp [det_unique]]
  have hadj : Δ.det • (⅟Δ : Matrix (Fin r) (Fin r) K) = Δ.adjugate := by
    have h1 : Δ * Δ.adjugate = Δ.det • (1 : Matrix (Fin r) (Fin r) K) := mul_adjugate Δ
    have : (⅟Δ : Matrix (Fin r) (Fin r) K) * (Δ * Δ.adjugate) = ⅟Δ * (Δ.det • 1) := by rw [h1]
    rw [← mul_assoc, invOf_mul_self, one_mul, Matrix.mul_smul, Matrix.mul_one] at this
    exact this.symm
  have hvu : Δ.det • (v * ⅟Δ * u) = v * Δ.adjugate * u := by
    rw [← hadj, Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.sub_apply, mul_sub]
  congr 1
  · ring
  · have := congrArg (fun M : Matrix Unit Unit K => M () ()) hvu
    simpa [Matrix.smul_apply, mul_comm] using this

/-- `BorderedId` transfers along a ring hom `f : β →+* γ`: a polynomial identity in the entries,
built from `fromBlocks`, `det`, `adjugate`, `*`, `-`, all commuting with `RingHom.mapMatrix`. -/
theorem borderedId_map {β γ : Type*} [CommRing β] [CommRing γ] (f : β →+* γ)
    {Δ : Matrix (Fin r) (Fin r) β} {u : Matrix (Fin r) Unit β}
    {v : Matrix Unit (Fin r) β} {d : Matrix Unit Unit β}
    (h : BorderedId Δ u v d) :
    BorderedId (Δ.map f) (u.map f) (v.map f) (d.map f) := by
  unfold BorderedId at h ⊢
  -- both sides equal `f` applied to the corresponding un-mapped piece
  have hlhs : (fromBlocks (Δ.map f) (u.map f) (v.map f) (d.map f)).det
      = f (fromBlocks Δ u v d).det := by
    rw [← fromBlocks_map Δ u v d f]; exact (RingHom.map_det f (fromBlocks Δ u v d)).symm
  have hrhs : (d.map f) () () * (Δ.map f).det - (v.map f * (Δ.map f).adjugate * u.map f) () ()
      = f (d () () * Δ.det - (v * Δ.adjugate * u) () ()) := by
    have hadj : (Δ.map f).adjugate = (Δ.adjugate).map f := (RingHom.map_adjugate f Δ).symm
    have hdet : (Δ.map f).det = f Δ.det := (RingHom.map_det f Δ).symm
    rw [hadj, ← Matrix.map_mul, ← Matrix.map_mul, hdet]
    simp only [map_sub, map_mul, Matrix.map_apply]
  rw [hlhs, hrhs, h]

/-- `BorderedId` reflects along an injective ring hom: if it holds for the `f`-images of the blocks
and `f` is injective, it holds for the blocks. (Both sides of `BorderedId` are `f`-images of the
corresponding un-mapped pieces, so `f`-injectivity cancels.) -/
theorem borderedId_of_map {β γ : Type*} [CommRing β] [CommRing γ] (f : β →+* γ)
    (hf : Function.Injective f) {Δ : Matrix (Fin r) (Fin r) β} {u : Matrix (Fin r) Unit β}
    {v : Matrix Unit (Fin r) β} {d : Matrix Unit Unit β}
    (h : BorderedId (Δ.map f) (u.map f) (v.map f) (d.map f)) :
    BorderedId Δ u v d := by
  unfold BorderedId at h ⊢
  apply hf
  rw [map_sub, map_mul]
  rw [show f (fromBlocks Δ u v d).det
          = (fromBlocks (Δ.map f) (u.map f) (v.map f) (d.map f)).det from by
        rw [← fromBlocks_map Δ u v d f]; exact RingHom.map_det f (fromBlocks Δ u v d),
      show f Δ.det = (Δ.map f).det from RingHom.map_det f Δ,
      show f (d () ()) = (d.map f) () () from rfl,
      show f ((v * Δ.adjugate * u) () ())
          = (v.map f * (Δ.map f).adjugate * u.map f) () () from by
        rw [show (Δ.map f).adjugate = (Δ.adjugate).map f from (RingHom.map_adjugate f Δ).symm,
          ← Matrix.map_mul, ← Matrix.map_mul]; rfl]
  exact h

/-- **Bordered Schur minor identity (general commutative ring).** The determinant of the bordered
`(r+1)×(r+1)` matrix `[[Δ, u], [v, d]]` (`r×r` block `Δ`, column `u`, row `v`, scalar corner `d`) is
`d · det Δ − v ⬝ adjugate Δ ⬝ u`. Valid over any commutative ring — no invertibility of `Δ`. Proved
by the universal-coefficient route: the generic `(r+1)×(r+1)` matrix over `ℤ` is a domain whose
fraction field has the (nonzero) generic pivot `det Δ` invertible, where `det_fromBlocks₁₁` applies;
the identity then descends (injective `algebraMap`) and specialises (entry evaluation). -/
theorem det_fromBlocks_scalar_eq (Δ : Matrix (Fin r) (Fin r) α) (u : Matrix (Fin r) Unit α)
    (v : Matrix Unit (Fin r) α) (d : Matrix Unit Unit α) :
    BorderedId Δ u v d := by
  classical
  -- the generic (r+1)×(r+1) matrix `A'` over `ℤ`, and its four blocks
  set D := MvPolynomial ((Fin r ⊕ Unit) × (Fin r ⊕ Unit)) ℤ with hD
  set A' : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) D := mvPolynomialX _ _ ℤ with hA'
  set Δ' := A'.toBlocks₁₁ with hΔ'
  set u' := A'.toBlocks₁₂ with hu'
  set v' := A'.toBlocks₂₁ with hv'
  set d' := A'.toBlocks₂₂ with hd'
  -- Step 1: `BorderedId Δ' u' v' d'` over the domain `D`, via its fraction field `K`.
  have hgen : BorderedId Δ' u' v' d' := by
    have hinj : Function.Injective (algebraMap D (FractionRing D)) :=
      IsFractionRing.injective D (FractionRing D)
    refine borderedId_of_map (algebraMap D (FractionRing D)) hinj ?_
    -- over the field K, the mapped pivot `Δ'` is nonsingular
    apply borderedId_of_det_ne_zero
    -- det (Δ'.map (algebraMap D K)) = algebraMap _ _ (det Δ') ≠ 0, since det Δ' ≠ 0 in the domain D
    rw [show (Δ'.map (algebraMap D (FractionRing D))).det
          = algebraMap D (FractionRing D) Δ'.det from (RingHom.map_det _ Δ').symm]
    rw [Ne, IsFractionRing.to_map_eq_zero_iff (R := D) (K := FractionRing D)]
    -- det Δ' ≠ 0: `Δ'` is the top-left generic block = renamed generic `r×r` matrix.
    have hren : Δ' = (mvPolynomialX (Fin r) (Fin r) ℤ).map
        (rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2))) := by
      ext i j
      simp [hΔ', hA', Matrix.toBlocks₁₁, mvPolynomialX_apply, rename_X]
    rw [hren, show ((mvPolynomialX (Fin r) (Fin r) ℤ).map
          (rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2)))).det
        = rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2))
            (mvPolynomialX (Fin r) (Fin r) ℤ).det from
          (AlgHom.map_det (rename (fun p : Fin r × Fin r => (Sum.inl p.1, Sum.inl p.2))) _).symm]
    rw [rename_eq_zero_iff_of_injective]
    · exact det_mvPolynomialX_ne_zero (Fin r) ℤ
    · intro a b hab
      have h2 : a.1 = b.1 ∧ a.2 = b.2 := by simpa using hab
      exact Prod.ext h2.1 h2.2
  -- Step 2: specialise `A'` to the given blocks via the entry-evaluation ring hom.
  set e : D →+* α := MvPolynomial.eval₂Hom (Int.castRingHom α)
    (fun p : (Fin r ⊕ Unit) × (Fin r ⊕ Unit) => (fromBlocks Δ u v d) p.1 p.2) with he
  have hmap : A'.map e = fromBlocks Δ u v d := by
    have := mvPolynomialX_map_eval₂ (Int.castRingHom α)
      (S := α) (m := Fin r ⊕ Unit) (n := Fin r ⊕ Unit) (fromBlocks Δ u v d)
    simpa [hA', he, MvPolynomial.eval₂Hom, MvPolynomial.eval₂] using this
  -- the four blocks map correctly (each is a `toBlocks` of `A'`, and `A'.map e = fromBlocks …`)
  have hentry : ∀ x y, (A'.map e) x y = (fromBlocks Δ u v d) x y := fun x y => by rw [hmap]
  have hbΔ : Δ'.map e = Δ := by
    rw [hΔ']; ext i j; simpa [Matrix.toBlocks₁₁] using hentry (Sum.inl i) (Sum.inl j)
  have hbu : u'.map e = u := by
    rw [hu']; ext i j; simpa [Matrix.toBlocks₁₂] using hentry (Sum.inl i) (Sum.inr j)
  have hbv : v'.map e = v := by
    rw [hv']; ext i j; simpa [Matrix.toBlocks₂₁] using hentry (Sum.inr i) (Sum.inl j)
  have hbd : d'.map e = d := by
    rw [hd']; ext i j; simpa [Matrix.toBlocks₂₂] using hentry (Sum.inr i) (Sum.inr j)
  have := borderedId_map e hgen
  rwa [hbΔ, hbu, hbv, hbd] at this

/-! ## The Schur relation vanishes on the rank-`≤ r` locus (the bridge to the base ideal) -/

/-- **The Schur expression is an `(r+1)`-minor, hence vanishes on `Mat^{rk ≤ r}`.** For a matrix
`M : Mat_{p×q}` over a field with `rank M ≤ r`, any choice of pivot rows `pr`, pivot columns `pc`,
and one extra row `a`, column `b`, the Schur expression
`M a b · det (M[pr,pc]) − (M[a,−]ᵀ ⬝ adjugate M[pr,pc] ⬝ M[−,b])` is zero: it is (by the bordered
Schur minor identity) the determinant of the `(r+1)×(r+1)` bordered submatrix, which vanishes since
`rank M ≤ r`. This is the polynomial that, on the pivot chart (`det M[pr,pc]` inverted), forces the
Schur relation `B22 = B21 Δ⁻¹ B12`. -/
theorem schur_expr_eq_zero_of_rank_le {k : Type u} [Field k] {p q r : ℕ}
    {M : Matrix (Fin p) (Fin q) k} (hr : M.rank ≤ r)
    (pr : Fin r → Fin p) (pc : Fin r → Fin q) (a : Fin p) (b : Fin q) :
    (Matrix.of (fun _ _ : Unit ↦ M a b) : Matrix Unit Unit k) () ()
        * (M.submatrix pr pc).det
      - ((Matrix.of (fun _ : Unit ↦ fun j : Fin r ↦ M a (pc j)) : Matrix Unit (Fin r) k)
          * (M.submatrix pr pc).adjugate
          * (Matrix.of (fun i : Fin r ↦ fun _ : Unit ↦ M (pr i) b) : Matrix (Fin r) Unit k))
            () () = 0 := by
  -- the bordered submatrix over `Fin r ⊕ Unit`
  set Δ : Matrix (Fin r) (Fin r) k := M.submatrix pr pc with hΔ
  set u : Matrix (Fin r) Unit k := Matrix.of (fun i _ ↦ M (pr i) b) with hu
  set v : Matrix Unit (Fin r) k := Matrix.of (fun _ j ↦ M a (pc j)) with hv
  set d : Matrix Unit Unit k := Matrix.of (fun _ _ ↦ M a b) with hd
  -- `fromBlocks Δ u v d` is the bordered `(r+1)×(r+1)` submatrix of `M`
  have hborder : fromBlocks Δ u v d
      = M.submatrix (Sum.elim pr (fun _ ↦ a)) (Sum.elim pc (fun _ ↦ b)) := by
    ext i j; cases i <;> cases j <;> rfl
  -- its determinant is the Schur expression (bordered Schur minor identity)
  have hid : (fromBlocks Δ u v d).det = d () () * Δ.det - (v * Δ.adjugate * u) () () :=
    det_fromBlocks_scalar_eq Δ u v d
  -- and it vanishes, being an `(r+1)`-minor of a rank-`≤ r` matrix
  have hzero : (fromBlocks Δ u v d).det = 0 := by
    rw [hborder]
    -- reindex `Fin r ⊕ Unit ≃ Fin (r+1)` to apply `submatrix_det_eq_zero_of_rank_le`
    have e : (Fin r ⊕ Unit) ≃ Fin (r + 1) :=
      (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv
    rw [← det_submatrix_equiv_self e.symm, submatrix_submatrix]
    exact submatrix_det_eq_zero_of_rank_le hr _ _
  rw [hid] at hzero; exact hzero

/-! ## Step (a): the `(r+1)`-minor of the generic product lies in the base ideal `sigmaIdeal d r`

Lifting the per-point vanishing to the polynomial ring `MvPolynomial (RepCoord d) k`: the generic
product matrix `multPoly d` (`Core.MultComorphism`) evaluates at `canonicalCoord A` to `mult d A`
(`eval_multPoly`), so an `(r+1)`-minor of `multPoly d` evaluates to the corresponding minor of
`mult d A`, which vanishes on `Σ̄^r = productRankLocusLE d r` (rank `≤ r`). General in `N`. This is
the bridge feeding the localized Schur graph ideal `J`. -/

/-- Evaluating an `(r+1)`-minor of the generic product matrix `multPoly d` at the coordinates of a
tuple `A` gives the corresponding `(r+1)`-minor of the actual product `mult d A` (`eval_multPoly`
entrywise through `det`/`submatrix`). -/
theorem eval_det_submatrix_multPoly {k : Type u} [Field k] {N : ℕ} (d : Fin (N + 1) → ℕ)
    (A : Tuple (k := k) d) {r : ℕ} (br : Fin (r + 1) → Fin (d (Fin.last N)))
    (bc : Fin (r + 1) → Fin (d 0)) :
    eval (canonicalCoord d A) (((Matrix.of (multPoly d)).submatrix br bc).det)
      = ((mult d A).submatrix br bc).det := by
  rw [RingHom.map_det (eval (canonicalCoord d A))]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.of_apply]
  exact eval_multPoly d A (br i) (bc j)

/-- **Step (a): the determinantal base ideal contains every `(r+1)`-minor of the generic product.**
For any choice of `r+1` rows `br` and `r+1` columns `bc`, the `(r+1)×(r+1)` minor
`det ((multPoly d).submatrix br bc)` lies in `sigmaIdeal d r` (the vanishing ideal of
`Σ̄^r = productRankLocusLE d r`): it evaluates on every `A ∈ Σ̄^r` to an `(r+1)`-minor of the
rank-`≤ r` matrix `mult d A`, which is `0`. General in `N`. -/
theorem det_submatrix_multPoly_mem_sigmaIdeal {k : Type u} [Field k] {N : ℕ}
    (d : Fin (N + 1) → ℕ) {r : ℕ} (br : Fin (r + 1) → Fin (d (Fin.last N)))
    (bc : Fin (r + 1) → Fin (d 0)) :
    ((Matrix.of (multPoly d)).submatrix br bc).det ∈ sigmaIdeal (k := k) d r := by
  rw [sigmaIdeal, mem_vanishingIdeal_iff]
  rintro x ⟨A, hA, rfl⟩
  rw [mem_productRankLocusLE] at hA
  -- `aeval (canonicalCoord A) p = eval (canonicalCoord A) p` (pointwise)
  rw [show aeval (R := k) (canonicalCoord d A) ((Matrix.of (multPoly d)).submatrix br bc).det
        = eval (canonicalCoord d A) ((Matrix.of (multPoly d)).submatrix br bc).det from by
        rw [aeval_def, eval]; rfl]
  rw [eval_det_submatrix_multPoly d A br bc]
  exact submatrix_det_eq_zero_of_rank_le hA br bc

end DLNFibre.Core
