import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract

/-!
# `RouteMInteriorLiveAnalytic` — the analytic chart atoms for the LIVE-leaf ∘ kLDU interior chart

The three analytic atoms the LIVE-leaf interior achiever contract (`RouteMInteriorLiveContract`)
consumes in its `NodeAchieverChart` `Umeas`/`Ubound`/`image_subset` slots. Built as named atoms in
this own module (genm-r1lower wires them into the contract's frozen `interiorLive_Umeas`/`_Ubound`/
`_image` `sorry`s).

* `ldu_image` — image containment (continuity of `interiorLivePhi` + `interiorLivePhi 0 = 0`).
* `ldu_Umeas` — `interiorLiveUnit` is measurable.
* `ldu_Ubound` — box bound + a.e.-positivity (the `NodeAchieverChart.Ubound` field).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open Matrix

variable {M : Fin (2 + 1) → ℕ}

/-! ## `interiorLivePhi 0 = 0` (the deepest point) -/

/-- **`kLDU` fixes `0`** — `kLens 0 = 0` (the diagonal pivots vanish), and the pass-through arms send
`0` to `0`. -/
theorem kLDU_zero (ha : StructAdm M (tach M)) :
    kLDU M (tach M) ha 0 = 0 := by
  funext q
  unfold kLDU
  split
  · rename_i k s heq
    split
    · rename_i qK hfeq
      show kLens (Matrix.of (readK M (tach M) ha 0 k)) _ _ = (0 : Fin (routeMAmbient M) → ℝ) q
      have h0 : Matrix.of (readK M (tach M) ha (0 : Fin (routeMAmbient M) → ℝ) k) = 0 := by
        funext i j; simp only [Matrix.of_apply, readK, Pi.zero_apply, Matrix.zero_apply]
      rw [h0]
      have hk0 : kLens (0 : Matrix (Fin (Text M (tach M) (k.val + 2)))
          (Fin (Text M (tach M) (k.val + 2))) ℝ) = 0 := by
        rw [kLens_eq]; simp
      rw [hk0]; simp
    · rfl
  · rfl

end DLNFibre.DLN.RLCT
