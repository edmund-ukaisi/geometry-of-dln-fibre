import DLNFibre.DLN.RLCT.Validate.RouteMGenFlatStruct

/-!
# `RouteMFlatStructV` — the VECTOR-parametrized structured achiever chart + its rate (∀M)

`RouteMGenFlatStruct` banks the structured decoder `genBlkFlatStruct M t ha x` (reading free
Schur/lift coords from a flat vector `x` via disjoint `chartIdxEquiv` role slots) but exposes the rate
only for the CONSTANT-radius diagonal `phiFlatStruct M t ha u = phiGen u M t (genBlkFlatStruct M t ha
(fun _ => u)) …` — a one-parameter family, not a full chart map.

This module lifts the rate to a genuine **full chart map** `phiFlatStructV M t ha : (Fin N → ℝ) →
(Fin N → ℝ)`, reading the radial pivot as the scalar coordinate `x p` (`p = ⟨0,_⟩`) and the block data
from the SAME vector `x`. The decoder-agnostic engine `routeMCore_phiGen` consumes only the block data
+ `hC0`, and the identity-boundary `C 0 = 1` reads only the x-INDEPENDENT constants `Bmat 0 = reindex 1`,
`Rmat 0 = 0`, so it holds for arbitrary `x` (and arbitrary scalar `v`, since `v • Rmat 0 = 0`). Hence
the rate transfers ∀M to the vector chart with NO bridge:

  `routeMCore M (phiFlatStructV M t ha x) = (x p)² · VvalGen (x p) M t (genBlkFlatStruct M t ha x) hle`.

This is the `NodeAchieverChart.leaf_integrand` rate factor `routeMCore (phi u) = (u p)² · Ufun(u)` for
arbitrary `M` (`Ufun := VvalGen (x p) …`). The determinant `cov` field is the genuinely hard piece (the
factored telescope) and is handled separately.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra / finite equivalences).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

variable {L : ℕ}

/-! ## The identity-boundary `C 0 = 1` for a GENERAL decoder argument + scalar

`C0_eq_one` (`RouteMGenFlatStruct`) proves `C 0 = 1` for `genBlkFlatStruct M t ha (fun _ => u)`; its
proof reads only `.Bmat 0 = reindex 1` and `.Rmat 0 = 0` (both x-independent), plus `v • Rmat 0 = 0`.
The same proof works verbatim for an arbitrary decoder argument `x` and an arbitrary scalar `v`. -/

/-- **The identity boundary `C 0 = 1`** (general decoder argument `x`, general scalar `v`): the proof of
`C0_eq_one` reads only the x-independent boundary constants `Bmat 0 = reindex 1`, `Rmat 0 = 0`, so it
holds for any `x` and any `v` (since `v • Rmat 0 = 0`). -/
theorem C0_eq_one_gen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)).toChain.C 0
      = (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := by
  rw [chainOfMt_C_zero v M t _ (hleStruct M t ha) ha.hL,
    show (genBlkFlatStruct M t ha x).Rmat 0 = 0 from rfl, smul_zero, add_zero]
  have h1W : Text M t 1 = Wext M 0 := Wext0_eq_Text1 M t ha
  have hBmat : (genBlkFlatStruct M t ha x).Bmat 0
      = Matrix.reindex (Equiv.refl _) (finCongr (Text0_eq_Text1_struct M t ha.h0))
          (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) := rfl
  rw [hBmat]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.cast (Text0_eq_Text1_struct M t ha.h0) i)]
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, Matrix.one_apply_eq, one_mul]
    have hjcol : (j : Fin (Wext M 0)) = Fin.cast (genWidthEq M t (hleStruct M t ha) 0 ha.hL)
        (Fin.castAdd (Wext M 0 - Text M t (0 + 1)) (Fin.cast h1W.symm j)) := by
      apply Fin.ext; simp
    rw [hjcol, chainQ_apply_castAdd, Matrix.one_apply, Matrix.one_apply]
    by_cases h : (i : ℕ) = (j : ℕ)
    · rw [if_pos (by apply Fin.ext; simpa using h), if_pos (by apply Fin.ext; simpa using h)]
    · rw [if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc)),
        if_neg (by intro hc; exact h (by simpa using congrArg Fin.val hc))]
  · intro b _ hb
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply,
      finCongr_symm, finCongr_apply]
    rw [show (1 : Matrix (Fin (Text M t 0)) (Fin (Text M t 0)) ℝ) i
          (Fin.cast (Text0_eq_Text1_struct M t ha.h0).symm b) = 0 from by
      rw [Matrix.one_apply, if_neg]; intro hc; apply hb; rw [hc]; apply Fin.ext; simp]
    rw [zero_mul]
  · intro hi; exact absurd (Finset.mem_univ _) hi

/-- **`hC0` for the structured decoder at a general `x` + scalar `v`**: `C 0 · suffix 0 = suffix 0`
(`C 0 = 1`). -/
theorem hC0_struct_gen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (v : ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (chainOfMt v M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)).toChain.C 0
        * (chainOfMt v M t (genBlkFlatStruct M t ha x)
            (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L)
      = (chainOfMt v M t (genBlkFlatStruct M t ha x)
          (hleStruct M t ha)).toChain.suffix 0 (Nat.zero_le L) := by
  rw [C0_eq_one_gen M t ha v x]
  exact Matrix.one_mul _

/-! ## The vector-parametrized structured chart + its rate -/

/-- The binding radial pivot axis `p = ⟨0,_⟩` of the structured chart (the radial scalar coordinate). -/
def structPivot (M : Fin (L + 1) → ℕ) (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) := ⟨0, hN⟩

/-- **The vector-parametrized structured achiever chart** `phiFlatStructV M t ha hN x := paramsEquivFlat
∘ chartParamsGen (x p) ∘ genBlkFlatStruct x` — a genuine full chart map `(Fin N → ℝ) → (Fin N → ℝ)`,
with the radial scalar read as the pivot coordinate `x p` and the block data from the same `x`. -/
noncomputable def phiFlatStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)

/-- The unit factor `Ufun x := VvalGen (x p) M t (genBlkFlatStruct M t ha x) hle` (the `(x p)`-free
factor of the rate `routeMCore = (x p)² · U`). -/
noncomputable def UvalStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)

/-- **The rate transfers to the vector chart ∀M (NO bridge)**: `routeMCore M (phiFlatStructV x) =
(x p)² · UvalStructV x`, directly from the decoder-agnostic `routeMCore_phiGen` + the general-`x`
identity-boundary `hC0_struct_gen`. This is the `NodeAchieverChart.leaf_integrand` rate factor for
arbitrary `M`. -/
theorem routeMCore_phiFlatStructV (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatStructV M t ha hN x)
      = (x (structPivot M hN)) ^ 2 * UvalStructV M t ha hN x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha x) (hleStruct M t ha)
    (hC0_struct_gen M t ha (x (structPivot M hN)) x)

end DLNFibre.DLN.RLCT
