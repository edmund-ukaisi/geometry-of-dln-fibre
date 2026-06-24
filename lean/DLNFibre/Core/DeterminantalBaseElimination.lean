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

/-- The full block reindex `RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar`. Drops the `Σ _ : Fin 1`
(`Equiv.uniqueSigma`), splits `Fin p ≃ Fin r ⊕ Fin (p−r)` and `Fin q ≃ Fin r ⊕ Fin (q−r)`,
distributes the product, then rearranges (`blockRearrange`). -/
def repCoordReindex (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    RepCoord (dStratum q p) ≃ B22block q p r ⊕ SchurVar q p r :=
  let ep : Fin p ≃ Fin r ⊕ Fin (p - r) :=
    (finCongr (by omega : p = r + (p - r))).trans finSumFinEquiv.symm
  let eq : Fin q ≃ Fin r ⊕ Fin (q - r) :=
    (finCongr (by omega : q = r + (q - r))).trans finSumFinEquiv.symm
  (Equiv.uniqueSigma _).trans <|
    (Equiv.prodCongr ep eq).trans <|
      (Equiv.sumProdDistrib _ _ _).trans <|
        (Equiv.sumCongr (Equiv.prodSumDistrib _ _ _) (Equiv.prodSumDistrib _ _ _)).trans
          (blockRearrange q p r)

end DLNFibre.Core
