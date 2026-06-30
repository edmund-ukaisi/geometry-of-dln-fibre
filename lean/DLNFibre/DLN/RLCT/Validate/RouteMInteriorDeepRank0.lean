import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveContract
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareReduce

/-!
# `RouteMInteriorDeepRank0` — the `deepRank = 0` interior achiever handler (L = 2)

The LIVE-leaf ∘ kLDU interior atom (`routeMCore_box_diverges_interiorLive`, `RouteMInteriorLiveAtom`)
covers `InteriorDrop ∧ 0 < deepRank` — its chart binds `leafPivot`, which needs `h0r : 0 < Text 2`
(= `0 < deepRank`). At `deepRank = 0` (a genuine interior stratum, e.g. `M = (1,1,2)`: unique
`tStar = ![0,0]`, `interiorDrop_L2_iff` ⟹ InteriorDrop, `minAdm = M0·M1 = 1`) the leaf K-block is
VACUOUS (`activeLeafImg.card = Text 2 · Wext 2 = 0`) and the codimension lives ENTIRELY in the front
E-block (`activeEImg.card = (Text1 − 0)(Wext1 − 0) = M0·M1 = minAdm`).

**The handler is the SAME `phiFlatLiveAt` chart with the pivot moved from the (empty) leaf to the
E-block.** `phiFlatLiveAt`/`phiFlatLiveAt_rate` are PIVOT-GENERIC (`routeMCore (phiFlatLiveAt … p₀ x)
= (x p₀)²·V` for any `p₀`); `activeSlotE_mem_activeM` puts the E-block (0,0) slot in `activeM`; and at
`deepRank = 0`, `activeM = activeEImg` with `card = minAdm`. So the radial `pivotBlowupOn (activeM) p₀`
on the E-pivot has det `|u_{p₀}|^{minAdm−1}` (a PURE MONOMIAL Jacobian — no poly-det fold, bedrock-safe)
and the rate `(u_{p₀})²·U`, giving the box-divergence threshold `½·minAdm = ½·M0·M1` — EXACTLY the
headline rate (kill-condition verified: Codex xhigh + the `rBlock·cBlock` budget).

**STATUS: SPECIFY skeleton.** Signatures fixed + validated; the analytic fills mirror the `0<deepRank`
interior leg with the E-pivot. The heavy fill is `eDeepRank0_BdetMonomial` (the E-pivot determinant
monomial — the deepRank=0 analog of `interiorLive_BdetMonomial_of_hreg`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {M : Fin (2 + 1) → ℕ}

/-- **The E-block (0,0) pivot** at the interior boundary `⟨0⟩`, the radial binding axis at
`deepRank = 0`. Needs `0 < Text 1 − Text 2` and `0 < Wext 1 − Text 2` (at `deepRank = 0`: `0 < M0`,
`0 < M1`, from `widths_pos_of_minAdm`). -/
noncomputable def eBlockPivot (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    Fin (routeMAmbient M) :=
  activeSlotE M (tach M) ha ⟨0, by decide⟩ ⟨0, hr⟩ ⟨0, hc⟩

/-- **`eBlockPivot ∈ activeM`** (in the E-image, hence the active set). -/
theorem eBlockPivot_mem_activeM (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    eBlockPivot ha hr hc ∈ activeM M ha :=
  activeSlotE_mem_activeM ha ⟨0, hr⟩ ⟨0, hc⟩

/-! ## The deepRank=0 E-block radial chart + its rate -/

/-- **The deepRank=0 chart** `φ₀ := phiFlatLiveAt … eBlockPivot` — the SAME live chart as the interior
leg with the radial pivot moved from the (empty) leaf to the E-block. Pivot-generic `phiFlatLiveAt`
carries the radial scalar at `eBlockPivot`. (At `deepRank = 0` every K-block vanishes — boundary 0's K
is `Text 2 = 0`-dim, the leaf's is `Text 3 = 0`-dim — so no `∘ kLDU` lens is needed.) -/
noncomputable def eDeepRank0Phi (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) :=
  phiFlatLiveAt M ha (by norm_num) (eBlockPivot ha hr hc)

/-- **The deepRank=0 rate** `routeMCore M (φ₀ x) = (x eBlockPivot)²·V` — the pivot-generic
`phiFlatLiveAt_rate` at `p₀ = eBlockPivot` (verbatim; the rate holds for ANY pivot). -/
theorem eDeepRank0Phi_rate (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (eDeepRank0Phi ha hr hc x)
      = (x (eBlockPivot ha hr hc)) ^ 2
        * VvalGen (x (eBlockPivot ha hr hc)) M (tach M)
            (genBlkFlatLive M (tach M) ha (rfinFixedPivot M ha (by norm_num) x) x)
            (hleStruct M (tach M) ha) :=
  phiFlatLiveAt_rate M ha (by norm_num) (eBlockPivot ha hr hc) x

/-! ## The single-axis Jacobian exponent vector (pure radial: `minAdm−1` at the pivot, `0` else) -/

/-- **The deepRank=0 Jacobian exponent vector** — SINGLE-AXIS: `minAdm − 1` on the binding E-pivot,
`0` on every other coordinate. At `deepRank = 0` the chart is a pure radial blow-up of the E-block
(all K-blocks vanish, so there is no LDU-core / Schur-frame exponent contribution); the only Jacobian
weight is the radial `|u_{eBlockPivot}|^{minAdm−1}`. -/
noncomputable def eDeepRank0_leafH (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    Fin (routeMAmbient M) → ℕ := fun j =>
  if j = eBlockPivot ha hr hc then minAdm M - 1 else 0

/-- **The binding axis carries `minAdm − 1`** (`if_pos rfl`). -/
theorem eDeepRank0_leafH_pivot (ha : StructAdm M (tach M))
    (hr : 0 < Text M (tach M) 1 - Text M (tach M) 2) (hc : 0 < Wext M 1 - Text M (tach M) 2) :
    eDeepRank0_leafH ha hr hc (eBlockPivot ha hr hc) = minAdm M - 1 := by
  rw [eDeepRank0_leafH, if_pos rfl]

end DLNFibre.DLN.RLCT
