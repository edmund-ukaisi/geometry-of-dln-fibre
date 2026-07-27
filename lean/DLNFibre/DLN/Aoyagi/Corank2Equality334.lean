import DLNFibre.DLN.Aoyagi.Corank2CiteFree334
import DLNFibre.DLN.Aoyagi.Corank2DLNRlct334

/-!
# `DLN.Aoyagi.Corank2Equality334` — the (3,3,4) `rlct = ½·codim` EQUALITY, CITE-FREE

The paper's headline "`rlct = ½·codim` (DLNs are mildly singular)" at the coupled `(3,3,4)`,
`B = 0` instance, FULLY CITE-FREE and monument-free. Both halves are built geometrically:

* **≤ (upper)** — `Corank2CiteFree334.rlctGlobal_lossDLN_334_zero_le_half_codimRealFibre`, the
  single-chart change-of-variables upper (from `chart334`, cite-free), which carried the sole
  un-banked input `MeasurePreserving eWrap` as a hypothesis. Here that hypothesis is DISCHARGED by
  the now-proven `measurePreserving_eWrap` (`Corank2EwrapMeasure`, the transpose-flatten coordinate
  permutation), yielding the UNCONDITIONAL upper `dln_rlct334_le_half_codim`.
* **≥ (lower)** — `Corank2DLNRlct334.dln_rlct334_ge_four`, the unconditional geometric V-lower.

`le_antisymm` of the two gives `dln_rlct334_eq_half_codim`:
`rlctGlobal (lossDLN ![3,3,4] 0) = ½·codimRealFibre ![3,3,4] 0 = 4`. This is the paper's equality at
one coupled instance WITHOUT the cited Watanabe bound — the geometric codimension is `8`
(`codimRealFibre_334_zero_toNat`), and both `rlct ≤ 4` and `rlct ≥ 4` are proved from the built
geometry (a single certified chart on one side, the over-vanishing V-lower on the other).

**Significance.** `dln_rlct334_eq_half_codim` is the cite-free `(3,3,4)` instance of the
`aoyagi_learning_coefficient` payoff (`rlct = ½·codim`), obtained WITHOUT the general
`exists_coreResolution` monument: the upper half rides one certified chart (not the full resolution
atlas) and the lower half the over-vanishing headline, so at this coupled instance the headline is
established on built geometry alone — neither the Watanabe cite nor the resolution-existence monument.
-/

open MeasureTheory
open DLNFibre.Core DLNFibre.Core.Aoyagi RLCT
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN (codimRealFibre lossDLN)

/-- **The (3,3,4) core-loss RLCT EQUALITY, cite-free**: `rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0 = 4`.
`le_antisymm` of the single-chart upper `rlctAt_coreGen334_le_four` (`≤ 4`) and the over-vanishing
V-lower `rlctAt_coreGen334_ge_four` (`4 ≤`). -/
theorem rlctAt_coreGen334_eq_four :
    rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) = 4 :=
  le_antisymm rlctAt_coreGen334_le_four OverVanishHeadline334.rlctAt_coreGen334_ge_four

/-- **The (3,3,4) DLN square-Frobenius UNCONDITIONAL cite-free upper**:
`rlctGlobal (lossDLN ![3,3,4] 0) ≤ ½·codimRealFibre ![3,3,4] 0`. The conditional single-chart upper
`rlctGlobal_lossDLN_334_zero_le_half_codimRealFibre` with its sole hypothesis `MeasurePreserving
eWrap` discharged by the proven `measurePreserving_eWrap` (the transpose flatten is a coordinate
permutation). No cite, no `MeasurePreserving eWrap` hypothesis. -/
theorem dln_rlct334_le_half_codim :
    RLCT.Global.rlctGlobal
        (lossDLN dvec (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ))
      ≤ ((codimRealFibre dvec
          (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)).toNat : ℝ) / 2 :=
  rlctGlobal_lossDLN_334_zero_le_half_codimRealFibre measurePreserving_eWrap

/-- **The (3,3,4) `rlct = ½·codim` EQUALITY, cite-free (the paper's headline at one instance)**:
`rlctGlobal (lossDLN ![3,3,4] 0) = ½·codimRealFibre ![3,3,4] 0`. `le_antisymm` of the unconditional
cite-free upper `dln_rlct334_le_half_codim` and the geometric V-lower `dln_rlct334_ge_four` (via
`codimRealFibre.toNat = 8`, so `½·codim = 4`). Both halves are BUILT geometry — Aoyagi's
`rlct = ½·codim` at `(3,3,4)`, `B = 0`, WITHOUT the cited Watanabe bound. -/
theorem dln_rlct334_eq_half_codim :
    RLCT.Global.rlctGlobal
        (lossDLN dvec (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ))
      = ((codimRealFibre dvec
          (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)).toNat : ℝ) / 2 := by
  have hcodim : ((codimRealFibre dvec
      (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)).toNat : ℝ) / 2 = 4 := by
    rw [codimRealFibre_334_zero_toNat]; norm_num
  refine le_antisymm dln_rlct334_le_half_codim ?_
  rw [hcodim]
  exact dln_rlct334_ge_four

/-- **The (3,3,4) DLN square-Frobenius RLCT value, cite-free**:
`rlctGlobal (lossDLN ![3,3,4] 0) = 4`. The equality `dln_rlct334_eq_half_codim` evaluated at the
geometric codimension `codimRealFibre.toNat = 8`. -/
theorem dln_rlct334_eq_four :
    RLCT.Global.rlctGlobal
        (lossDLN dvec (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)) = 4 := by
  rw [dln_rlct334_eq_half_codim, codimRealFibre_334_zero_toNat]; norm_num

end DLNFibre.DLN.Aoyagi
