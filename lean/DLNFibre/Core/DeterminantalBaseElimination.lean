import DLNFibre.Core.DeterminantalChartRing
import DLNFibre.Core.GraphIdealHeight

/-!
# `DLNFibre.Core.DeterminantalBaseElimination` — the localized base presentation (`Iad = J`)

The localized determinantal base ring `A_loc = Localization.Away detΔ` of the rank-`≤ r` stratum, on
the pivot chart, eliminates the bottom-right `B22` block: the Schur relation forces
`B22 = B21 Δ⁻¹ B12`, so the localized base ideal `Iad` is the graph ideal `J` of that forced value.

This module reindexes the engine coordinate ring `A_eng = MvPolynomial (RepCoord (dStratum q p)) k`
along the block split `RepCoord ≃ B22block ⊕ SchurVar` (`B22block = Fin (p−r) × Fin (q−r)`,
`#B22block = (p−r)(q−r) = C`; `SchurVar = Δ ⊕ B12 ⊕ B21`, `#SchurVar = r(p+q−r) = δ`), so the pivot
minor `detΔ` lives in the `SchurVar` block. The forced-block graph ideal then has height `C`
(`Core.GraphIdealHeight`), which — with the LANDED `height Iad = C` and `J ⊆ Iad` — squeezes
`Iad = J` and exhibits `A_loc ⧸ Iad` as the free Schur localization (regular of dimension `δ`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

/-! ## The block coordinate types and the reindex equivalence -/

/-- The eliminated `B22` block: bottom-right `(p−r) × (q−r)` matrix coordinates. `#B22block = C`. -/
abbrev B22block (q p r : ℕ) : Type := Fin (p - r) × Fin (q - r)

/-- The free Schur coordinates `Δ ⊕ B12 ⊕ B21`: the top-left `r×r` pivot block `Δ`, the top-right
`r × (q−r)` block `B12`, the bottom-left `(p−r) × r` block `B21`. `#SchurVar = δ = r(p+q−r)`. -/
abbrev SchurVar (q p r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (q - r)) ⊕ (Fin (p - r) × Fin r))

/-- `#B22block = (p − r)(q − r) = C`. -/
theorem card_B22block (q p r : ℕ) : Nat.card (B22block q p r) = (p - r) * (q - r) := by
  simp [B22block, Nat.card_eq_fintype_card]

/-- `#SchurVar = r·r + (r·(q−r) + (p−r)·r) = r(p + q − r) = δ` (for `r ≤ p`, `r ≤ q`). -/
theorem card_SchurVar (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Nat.card (SchurVar q p r) = r * (p + q - r) := by
  simp only [SchurVar, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_sum]
  -- r*r + (r*(q−r) + (p−r)*r) = r(p+q−r), via `q = r+b`, `p = r+a`
  obtain ⟨a, rfl⟩ := Nat.le.dest hp
  obtain ⟨b, rfl⟩ := Nat.le.dest hq
  rw [show r + a + (r + b) - r = r + a + b by omega, Nat.add_sub_cancel_left,
    Nat.add_sub_cancel_left]
  ring

/-- The block reindex of the four products `(Δ ⊕ B12) ⊕ (B21 ⊕ B22)` into `B22block ⊕ SchurVar`
(B22 outermost for the elimination; `SchurVar = Δ ⊕ (B12 ⊕ B21)`). -/
def blockRearrange (q p r : ℕ) :
    (((Fin r × Fin r) ⊕ (Fin r × Fin (q - r))) ⊕
        ((Fin (p - r) × Fin r) ⊕ (Fin (p - r) × Fin (q - r))))
      ≃ B22block q p r ⊕ SchurVar q p r where
  toFun := fun x ↦ match x with
    | .inl (.inl d) => .inr (.inl d)
    | .inl (.inr b12) => .inr (.inr (.inl b12))
    | .inr (.inl b21) => .inr (.inr (.inr b21))
    | .inr (.inr b22) => .inl b22
  invFun := fun x ↦ match x with
    | .inr (.inl d) => .inl (.inl d)
    | .inr (.inr (.inl b12)) => .inl (.inr b12)
    | .inr (.inr (.inr b21)) => .inr (.inl b21)
    | .inl b22 => .inr (.inr b22)
  left_inv := by rintro (⟨d|b12⟩|⟨b21|b22⟩) <;> rfl
  right_inv := by rintro (b22|⟨d|⟨b12|b21⟩⟩) <;> rfl

/-- The pivot split `Fin n ≃ Fin r ⊕ Fin (n−r)` (first `r` ↦ left). -/
def finSplit {n r : ℕ} (h : r ≤ n) : Fin n ≃ Fin r ⊕ Fin (n - r) :=
  (finCongr (show n = r + (n - r) by omega)).trans finSumFinEquiv.symm

/-- `finSplit` sends a pivot index `castLE i` (`i < r`) to `Sum.inl i`. -/
@[simp] theorem finSplit_castLE {n r : ℕ} (h : r ≤ n) (i : Fin r) :
    finSplit h (Fin.castLE h i) = Sum.inl i := by
  rw [finSplit, Equiv.trans_apply,
    show (finCongr (show n = r + (n - r) by omega)) (Fin.castLE h i) = Fin.castAdd (n - r) i from by
      apply Fin.ext; simp [finCongr, Fin.castLE, Fin.castAdd],
    finSumFinEquiv_symm_apply_castAdd]

/-- The full block reindex `RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar`. Drops the `Σ _ : Fin 1`
(`Equiv.uniqueSigma`), splits `Fin p ≃ Fin r ⊕ Fin (p−r)` and `Fin q ≃ Fin r ⊕ Fin (q−r)`
(`finSplit`), distributes the product, then rearranges (`blockRearrange`). -/
def repCoordReindex (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    RepCoord (dStratum q p) ≃ B22block q p r ⊕ SchurVar q p r :=
  (Equiv.uniqueSigma _).trans <|
    (Equiv.prodCongr (finSplit hp) (finSplit hq)).trans <|
      (Equiv.sumProdDistrib _ _ _).trans <|
        (Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
          (blockRearrange q p r)

/-- A pivot coordinate `⟨0, (castLE i, castLE j)⟩` (pivot row `i`, pivot column `j`, both `< r`)
maps under the reindex into the `Δ`-block of `SchurVar`: `Sum.inr (Sum.inl (i, j))`. So the pivot
minor `detΔ` is a polynomial in the `SchurVar` coordinates only. -/
theorem repCoordReindex_pivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (i j : Fin r) :
    repCoordReindex q p r hp hq
        ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩
      = Sum.inr (Sum.inl (i, j)) := by
  change ((Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
      (blockRearrange q p r)) ((Equiv.sumProdDistrib _ _ _)
        ((finSplit hp (Fin.castLE hp i), finSplit hq (Fin.castLE hq j)))) = _
  rw [finSplit_castLE, finSplit_castLE]
  rfl

/-! ## The generic product entries are the coordinate variables (`N = 1`) -/

variable {k : Type u} [Field k]

/-- At `N = 1`, the product `mult (dStratum q p) A` is the lone factor `A 0` (the empty prefix
product is the identity). General over any commutative ring. -/
theorem mult_stratum_eq {R : Type*} [CommRing R] (q p : ℕ) (A : Tuple (k := R) (dStratum q p)) :
    mult (dStratum q p) A = A 0 := by
  have hdef : mult (dStratum q p) A
      = A 0 * multPrefix (dStratum q p) A (Fin.castSucc (0 : Fin 1)) := rfl
  have h1 : multPrefix (dStratum q p) A (Fin.castSucc (0 : Fin 1))
      = (1 : Matrix (Fin (dStratum q p (Fin.castSucc (0 : Fin 1))))
            (Fin (dStratum q p (Fin.castSucc (0 : Fin 1)))) R) := rfl
  rw [hdef, h1]; exact Matrix.mul_one _

/-- The generic single-matrix product entries are the coordinate variables:
`multPoly (dStratum q p) a b = X ⟨0, (a, b)⟩`. -/
theorem multPoly_stratum_apply (q p : ℕ) (a : Fin p) (b : Fin q) :
    (Matrix.of (multPoly (k := k) (dStratum q p))) a b
      = (X ⟨0, (a, b)⟩ : MvPolynomial (RepCoord (dStratum q p)) k) := by
  rw [Matrix.of_apply, multPoly, mult_stratum_eq q p (genericTuple (dStratum q p))]
  rfl

/-! ## The pivot minor `detΔ` lives in the `SchurVar` block

Under the block reindex `Φ = renameEquiv (repCoordReindex)`, the pivot minor `detΔ = detPivotPoly`
maps to `rename Sum.inr detSchurS` — a polynomial in the `SchurVar` (specifically `Δ`) coordinates
only. Pushing further through `sumAlgEquiv` (with `B22block` outermost), `detΔ` becomes the constant
`C detSchurS`, so localizing `A_eng` at `detΔ` is localizing the coefficient ring at `detSchurS`. -/

/-- The pivot determinant in the free Schur coordinate ring: `det` of the `Δ`-block coordinate
matrix `(i, j) ↦ X (Sum.inl (i, j))` in `MvPolynomial (SchurVar q p r) k`. This is `detΔ` after
eliminating the `B22` block — the localization element on the Schur side. -/
noncomputable def detSchurS (q p r : ℕ) : MvPolynomial (SchurVar q p r) k :=
  (Matrix.of (fun i j : Fin r ↦ (X (Sum.inl (i, j)) : MvPolynomial (SchurVar q p r) k))).det

/-- Under the reindex `renameEquiv (repCoordReindex)`, the pivot minor `detΔ` maps to
`rename Sum.inr (detSchurS)`: it is a polynomial in the `SchurVar` coordinates only. (`det` commutes
with the algebra maps; each pivot entry `X ⟨0, (castLE i, castLE j)⟩` maps to the `Δ`-coordinate
`X (Sum.inr (Sum.inl (i, j)))`, by `repCoordReindex_pivot`.) -/
theorem renameEquiv_detPivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (renameEquiv k (repCoordReindex q p r hp hq)) (detPivotPoly (k := k) q p r hp hq)
      = rename Sum.inr (detSchurS (k := k) q p r) := by
  rw [detPivotPoly, detSchurS, AlgEquiv.map_det, AlgHom.map_det (rename Sum.inr)]
  congr 1
  funext i j
  rw [AlgEquiv.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    Matrix.submatrix_apply, multPoly_stratum_apply, renameEquiv_apply, rename_X, Matrix.of_apply,
    rename_X]
  congr 1
  exact repCoordReindex_pivot q p r hp hq i j

/-- The full block algebra equivalence
`A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k)`: relabel the coordinates
(`renameEquiv (repCoordReindex)`) then split off the `B22` block (`sumAlgEquiv`, `B22block`
outermost). -/
noncomputable def blockAlgEquiv (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    MvPolynomial (RepCoord (dStratum q p)) k
      ≃ₐ[k] MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k) :=
  (renameEquiv k (repCoordReindex q p r hp hq)).trans (sumAlgEquiv k _ _)

/-- Under `blockAlgEquiv`, the pivot minor `detΔ` becomes the constant `C detSchurS`: it lives
purely in the `SchurVar` coefficient ring (`sumAlgEquiv` sends `rename Sum.inr` into the constants).
So localizing `A_eng` at `detΔ` corresponds to localizing the `SchurVar` coefficient ring at
`detSchurS`. -/
theorem blockAlgEquiv_detPivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    blockAlgEquiv (k := k) q p r hp hq (detPivotPoly (k := k) q p r hp hq)
      = C (detSchurS (k := k) q p r) := by
  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_detPivot]
  have h := sumAlgEquiv_comp_rename_inr (R := k) (S₁ := B22block q p r) (S₂ := SchurVar q p r)
  have hs := congrArg (fun f ↦ f (detSchurS (k := k) q p r)) h
  simpa using hs

/-- `detSchurS ≠ 0`: it is the determinant of the generic `Δ`-coordinate matrix (a renamed
`mvPolynomialX`), nonzero by `det_mvPolynomialX_ne_zero`. So `Sd = Localization.Away detSchurS` is a
nontrivial localization (a domain), and `detSchurS` is a valid localization element. -/
theorem detSchurS_ne_zero (q p r : ℕ) : detSchurS (k := k) q p r ≠ 0 := by
  rw [detSchurS]
  have hren : (Matrix.of (fun i j : Fin r ↦ (X (Sum.inl (i, j)) : MvPolynomial (SchurVar q p r) k)))
      = (mvPolynomialX (Fin r) (Fin r) k).map
          (rename (fun ab : Fin r × Fin r ↦ (Sum.inl ab : SchurVar q p r))) := by
    ext i j; simp [mvPolynomialX_apply, rename_X]
  rw [hren,
    show ((mvPolynomialX (Fin r) (Fin r) k).map
        (rename (fun ab : Fin r × Fin r ↦ (Sum.inl ab : SchurVar q p r)))).det
      = rename (fun ab : Fin r × Fin r ↦ (Sum.inl ab : SchurVar q p r))
          (mvPolynomialX (Fin r) (Fin r) k).det from
      (AlgHom.map_det (rename (fun ab : Fin r × Fin r ↦ (Sum.inl ab : SchurVar q p r))) _).symm,
    Ne, rename_eq_zero_iff_of_injective]
  · exact det_mvPolynomialX_ne_zero (Fin r) k
  · intro a b hab; simpa using hab

end DLNFibre.Core
