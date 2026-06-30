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

end DLNFibre.DLN.RLCT
