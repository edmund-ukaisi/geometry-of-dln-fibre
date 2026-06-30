import DLNFibre.DLN.RLCT.Validate.RouteMLeafBData
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

/-!
# `RouteMLeafEngine` — the HONEST per-boundary engine for `BchartLeaf`

The ∀M-L2 interior-det headline `interiorDet_leaf_headline_Bchart` (`RouteMLeafBData`) carries one
hypothesis, `hdet : |det (fderiv ℝ (BchartLeaf ha) (pbo u))| = ∏_{s:Fin 2} engine_s`. This module
records the HONEST engine for the actual `BchartLeaf`.

## Fidelity finding (validate-small `(3,3,4)`, numeric + decorrelated Codex)
`BparamsLeaf ha y = chartParamsGen 1 … (genBlkFlatLive … (rfinDirect ha y) y)` reads the Schur core
`K = readK …` DIRECTLY (free coordinates), so its Jacobian determinant is the **free-K Schur** value
`|det K|^(r+c)` — NOT the Schur·LDU value `|det K|^(r+c) · ∏ᵢ |qᵢ|^{2(t−1−i)}`. The LDU
multiplier appears only for a *lensed* decoder (`kLDU`, `RouteMKLens`) that first reparametrizes the
K slots; the current chart does not. At `(3,3,4)` the numeric Jacobian det is exactly
`(det K)^{r+c} = (det K)^4` (interior boundary `t = Text 2 = 1`, so the LDU exponents `2(t−1−i)`
vanish and the LDU product is the empty `1`, making `|det K|^4` simultaneously the free-K AND the
vacuously-LDU value there). For interior boundaries with `t ≥ 2` the two genuinely differ; the
honest value for `BchartLeaf` is the free-K one.

So the honest engine is `engineFreeK 0 = |det (readK-core at the pivot point)|^(r+c)`,
`engineFreeK 1 = 1`.

## What this module delivers
* `engineFreeK` — the honest per-boundary engine (free-K Schur at boundary 0, `1` at the leaf).
* `engineFreeK_prod` — the product collapses to the single interior-boundary value.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the engine is matrix algebra; no analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

section L2

variable {M : Fin (2 + 1) → ℕ}

/-! ## The honest free-K Schur engine -/

/-- The interior Schur core `K = readK … ⟨0⟩` read at the blown-up point `pbo u`, as a
`Text 2 × Text 2` matrix. -/
noncomputable def leafKcore (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (Text M (tach M) (0 + 2))) (Fin (Text M (tach M) (0 + 2))) ℝ :=
  Matrix.of (readK M (tach M) ha
    (pivotBlowupOn (activeM M ha) (leafPivot M ha (by norm_num) h0r h0c) u) ⟨0, by decide⟩)

/-- **The honest per-boundary engine** for `BchartLeaf` at L=2: at the interior boundary `0` the
free-K Schur value `|det K|^(r+c)` with `r = Text 1 − Text 2`, `c = Wext 1 − Text 2`, the Schur core
`K = leafKcore` read at the blown-up point `pbo u`; at the leaf `1`. -/
noncomputable def engineFreeK (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) : Fin 2 → ℝ :=
  fun s => if s = 0 then
    |(leafKcore ha h0r h0c u).det|
      ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2))
    else 1

/-- The product of the honest engine collapses to the single interior-boundary value. -/
theorem engineFreeK_prod (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2)
    (u : Fin (routeMAmbient M) → ℝ) :
    ∏ s : Fin 2, engineFreeK ha h0r h0c u s
      = |(leafKcore ha h0r h0c u).det|
        ^ ((Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)) := by
  rw [Fin.prod_univ_two]
  simp [engineFreeK]

end L2

end DLNFibre.DLN.RLCT
