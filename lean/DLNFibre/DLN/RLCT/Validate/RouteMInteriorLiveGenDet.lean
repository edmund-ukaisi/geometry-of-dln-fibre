import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenBase
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenChart
import DLNFibre.DLN.RLCT.Validate.RouteMSchurStairDet
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMChainFDerivValue
import DLNFibre.DLN.RLCT.Validate.RouteMReaderFDeriv
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.DLN.RLCT.Validate.RouteMHregPerm

/-!
# `RouteMInteriorLiveGenDet` — Factor 1: the general-`L` boundary-factor determinant

The general-`L` analogue of `RouteMEihdFreePoint.Dtot_abs_det_free` (the `L = 2` boundary-factor
determinant). This is **Factor 1** of the general-`L` `BdetMonomial` chain-rule; Factor 2 (the ambient
LDU lens) is the controller's `RouteMInteriorLiveGenAmbient.kLDU_ambient_det_pbo_gen`.

## The mathematics

The `u`-free boundary chart `BparamsLeafGen ha y : Params M` reads the residual/frame coordinates
directly from `y` (radial hardwired to `1`) and assembles the chain. Its flat-Jacobian
`DtotGen ha y₀ := fderiv ℝ (BchartLeafGen ha) y₀` is block-lower-triangular in the `L` chain layers
`A_s` (`s : Fin L`); each diagonal block is the per-boundary Schur frame
`schurFrameDeriv (readX s) (readK s) (readN s)` with abs-det `|det (readK s)|^{r_s + c_s}`; the
head-into-tail chain couplings are det-irrelevant. Collecting the `L` flat layers by a
layer-collecting equiv, `DtotGen` conjugates to the per-boundary Schur staircase
`schurStairMap` (`RouteMSchurStairDet`), and `schurStairMap_abs_det_twoConj` reads off

  `|det (DtotGen ha y₀)| = ∏_{s : Fin L} |det (readK y₀ s)|^{r_s + c_s}`,

with `t_s = Text(s+2)`, `r_s = Text(s+1) − Text(s+2)`, `c_s = Wext(s+1) − Text(s+2)`.

## The per-boundary width functions

`schurTGen/schurRGen/schurCGen : ℕ → ℕ` are the per-boundary `t/r/c` families: `t s = Text(s+2)`,
`r s = Text(s+1) − Text(s+2)`, `c s = Wext(s+1) − Text(s+2)` (the frame `SchurInc_s` shape).

## The dimensionally-correct staircase (design corrected 2026-07-01)

The flat ambient is `⊕_{k : Fin L} (frame slot k ⊕ lift slot k)` (`chartIdxEquiv`); the correct
staircase boundary space is `genV k = (Fin (schurDim k) → ℝ) × (Fin (liftDim k) → ℝ)` — frame ⊕ lift.
The diagonal block `genF k` is `schurFrameDeriv` on the frame (det `|det K_k|^{r_k+c_k}`) ⊕ id on the
lift (det `1`). Consumes the general `stairMap` spine (`RouteMStairFold`/`RouteMStairTwoSided`), NOT
the pure-`SchurInc` `schurStairMap` (which OMITS the lift coordinates — a dimension mismatch).

## Deliverables

* `rfinDirectGen` / `BparamsLeafGen` / `BchartLeafGen` — the general-`L` boundary chart.
* `reindexLs_BparamsLeafGen` — the per-layer chart-component ↔ `Agen` bridge (sorry-free).
* `DtotGen` — the flat-Jacobian linear map.
* `genV` / `genF` / `genF_abs_det` — the staircase boundary spaces + diagonal blocks + per-block det.
* `eInGen` / `eihdOutGen` / `eihdcGen` — the layer-collecting equivs + coupling.
* `eihd_hD_gen` — the block identity `eihdOutGen ∘ DtotGen ∘ eInGen.symm = stairMap genV L genF`.
* `eihd_hreg_gen` — the regauge abs-det-`1`.
* `DtotGen_abs_det` — the headline, via `stairMap_abs_det_twoConj` + `genF_abs_det`.

## Status (ROUND-3, 2026-07-01: staggered pack LANDED; 2 residuals)

`DtotGen_abs_det` is PROVEN sorry-free MODULO the 2 residuals below: the general spine
`stairMap_abs_det_twoConj` is threaded and `genF_abs_det` folds the per-block dets to the readers
(`∏_{s : Fin L} |det (readK y₀ s)|^{r_s+c_s}`).

CLOSED THIS ROUND (were residuals, now sorry-free): `packStairGen` (the staggered Params-layer →
staircase pack, ROUTE-B cast-tower assembly — `piReindexOfSigma` [step5] + `liftGatherFinL` [the
`finCongr`+`Equiv.sigmaCongrLeft'` transport of `sigmaGather`] + `packRowSplitGen`/`flatMatLEGen`/
`piProdSplit`/`piToStair`; the cast-tower typechecks — `schurDim = Text·Wext` defeq + the `genV k.val`
alignment both fire), and `eihdOutGen := (paramsEquivFlatLinear).symm ≪≫ₗ packStairGen` (thin,
`routeMAmbient = flatDim` DEFINITIONALLY). NB `packStairGen` carries an explicit `(hL : 0 < L)`
(supplied by `ha.hL`) — the `L = 0` subsingleton case is not needed by any consumer.

ROUND-2 CORRECTION (2026-07-01): the earlier `eihdOutGen := eInGen` (single-conjugate) was
GREEN-BUT-WRONG — `eInGen` reads the SLOT layout but `DtotGen`'s OUTPUT is Params-LAYER, so
`diag(T) s = genF s` was FALSE (numeric L=3: slot 17/9/0 vs Params-layer 8/12/6). FIX (genm-crux +
Codex, VERIFY-FIRST-confirmed): a STAGGERED output pack in the EXISTING `genV` — `genV` slot `s` ←
`kept(layer s) ⊕ lift(layer s+1)` (dims balance: `kept(layer s)=schurDim_s`, `lift(layer s+1)=liftDim_s`).
`genV` is KEPT (injOn unaffected — grep-verified: GenInj/InjRec reuse `eInGen`-as-injection + reader
side, not the det block route).

DONE (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):
* `genV` / `genF` / `genF_abs_det` — boundary spaces + diagonal block + det `|det K_k|^{r_k+c_k}`.
* `flatMatLEGen` / `roleReorderLEGen` / `frameToSchurIncGen` — the faithful frame reshape.
* `piToStair` / `headTailFinPi` — the reusable Pi-over-`Fin` ↔ `StairProd` bridge.
* `eInGen` — the input equiv (slot layout: `funCongrLeft chartIdxEquiv.symm ≫ piCurry ≫ sumArrow ≫
  piToStair`) — CORRECT for the INPUT (readers ARE slot-based) + reused by injRec.
* `stairCouplingOf` / `eihdcGen` — the coupling extractor + `eihdcGen := stairCouplingOf (eihdOutGen ∘
  DtotGen ∘ eInGen.symm)`.
* `stairMap_eq_of_lowerTriDiag` (+ `StairLowerTriDiag`) — reconstruction lemma: `StairLowerTriDiag V n
  f T → T = stairMap V n f (stairCouplingOf T)`. Reduces `eihd_hD_gen` to per-boundary block facts.
* `reindexLs_BparamsLeafGen`; `hasFDerivAt_readN/_readX/_readW`; `det_symm_conj_toLinearMap`.

BANKED sorry-free (Route-B bricks, 2026-07-01 — the hard cores):
* `packRowSplitGen` — per-layer row-split `Matrix (Wext s)(Wext s+1) ≃ₗ kept_s × liftblock_s`.
* `sigmaGather` — the OFF-BY-ONE lift Sigma-bijection `(Σ k, Fin(blk k)) ≃ (Σ k, Fin(lift k))` (the
  irreducible combinatorial core), via `Fin.cases`/`Fin.lastCases`.
* `gatherBlk_zero`/`gatherLift_last`/`gatherShift` — its 3 hyps at the actual DLN widths.

REMAINING (2 sorries — both large, isolated, honest; NEITHER forced green):
* `eihd_hD_gen` — **THE CRUX**: `eihdOutGen ∘ DtotGen ∘ eInGen.symm = stairMap genV L genF eihdcGen`.
  REDUCED (this round) via `stairMap_eq_of_lowerTriDiag` (`eihdcGen = stairCouplingOf genV L T` by `rfl`)
  to the single isolated goal `StairLowerTriDiag genV L genF T` (`T` the conjugated `DtotGen`): per
  boundary (i) upper-block = 0 + (ii) diag = genF s. (ii) is the per-boundary fderiv-Schur collapse of
  `Agen s = chainA(readN s)(readW s)(Cgen(s+1))` in the STAGGERED `genV` coords → `schurFrameDeriv` on
  the frame ⊕ id on the lift. Foundation banked: `hasFDerivAt_chainA` + `hasFDerivAt_readN/X/W` +
  `reindexLs_BparamsLeafGen` + `genF`; generalizes the `L = 2` `layer0SchurMap_fderiv_collapse` (which
  needs the general analogues of `slotReadV0`/`packLayer0`/`gate_schurCore_eq` — a multi-hundred-LoC
  fderiv development). SOUNDNESS — VERIFIED (2026-07-01, two decorrelated Codex `xhigh` passes):
  `diag(T) s = genF s` GENUINELY holds. DECISIVE FACT: the chain-reader index-shift `Nblk_s = readN⟨s−1⟩`
  (`genBlkFlatLive_Nblk_succ`): the layer-s KEPT block = `Cgen(s+1) − Nblk_s·Wblk_s` where `Cgen(s+1) =
  schurFrameProd(readK⟨s⟩,readX⟨s⟩,readN⟨s⟩,readE⟨s⟩)`; the `−N·W` coupling reads `readN⟨s−1⟩` (slot s−1
  frame) and `Wblk_s` (slot s−1 lift, by the STAGGER) → strictly OFF-DIAGONAL (s−1 → s, lower), captured
  by `eihdcGen` (det-invisible). `Cgen` uses `Bmat/Nblk/Rmat` NOT `Wblk` ⇒ no same-slot spoiler; the
  diagonal frame block is exactly the `Cgen(s+1)` Schur fderiv = `schurFrameDeriv_s`. Lift diag genuinely
  `id` (the off-by-one gather routes layer-(s+1)-lift input=output to slot s). So `genF s =
  schurFrameDeriv_s ⊕ id` IS the diagonal (unlike the removed single-conjugate `eihdOutGen := eInGen`,
  green-but-wrong). NOT forced green — remaining sorry is pure Lean construction (own tide), math settled.
* `eihd_hreg_gen` — `|det (eihdOutGen.symm ∘ eInGen)| = 1`: the slot↔staggered-layer reindex is a signed
  coord permutation (det ±1). Route (general-L lift of `RouteMHregPerm.eihd_hreg`): build a `stairChartGen`
  on `StairProd genV L` + certify `isCoordLE_eInGen` / `isCoordLE_packStairGen` via `isCoordLE_of_read`,
  compose by `IsCoordLE.trans`/`.symm`, feed `hreg_of_exists_funCongrLeft`. The top-level assembly is
  general (mirrors L=2 `eihd_hreg`); the two per-block `IsCoordLE` certificates need per-slot reads
  through the recursive `stairChartGen` (the ~600-LoC L=2 `bigToChartEin`/`bigToFlatIdx` analogue at
  general L). TRUE and det-irrelevant to soundness; left isolated.

The mathematics is confirmed (numerically at `L = 3`, `(2,4,3,2)`, via
`RouteMSchurStairDet.schurStairMap_abs_det_2432`); the residual is the LEAN CONSTRUCTION.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The per-boundary width functions (matching the Schur-staircase spine) -/

/-- **The per-boundary K-block width** `t_s = Text(s+2)` — the `readK s` square dimension. -/
def schurTGen (M : Fin (L + 1) → ℕ) : ℕ → ℕ := fun s => Text M (tach M) (s + 2)

/-- **The per-boundary X-row count** `r_s = Text(s+1) − Text(s+2)` — the `readX s` row count. -/
def schurRGen (M : Fin (L + 1) → ℕ) : ℕ → ℕ :=
  fun s => Text M (tach M) (s + 1) - Text M (tach M) (s + 2)

/-- **The per-boundary N-col count** `c_s = Wext(s+1) − Text(s+2)` — the `readN s` col count. -/
def schurCGen (M : Fin (L + 1) → ℕ) : ℕ → ℕ := fun s => Wext M (s + 1) - Text M (tach M) (s + 2)

/-! ## The general-`L` boundary chart `BparamsLeafGen` -/

/-- **The direct leaf reader** at general `L`: `rfinDirectGen ha y i j := y (leafSlot … i j)` — reads
ALL leaf entries (including the pivot slot `(0,0)`) DIRECTLY from `y`, no fixed-`1`, no radial scaling.
The general-`L` lift of `RouteMLeafBData.rfinDirect`. -/
def rfinDirectGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) :
    Matrix (Fin (Text M (tach M) L)) (Fin (Wext M L)) ℝ :=
  Matrix.of fun i j => y (leafSlot M (tach M) ha ha.hL i j)

/-- **The general-`L` boundary-factor chart parameters** `BparamsLeafGen ha y : Params M` — the
`u`-FREE chart, radial scalar hardwired to `1`, reading the residual coords directly (`rfinDirectGen`)
from `y`. The general-`L` lift of `RouteMLeafBData.BparamsLeaf`. -/
def BparamsLeafGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) : Params M :=
  chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
    (hleStruct M (tach M) ha)

/-- **The general-`L` boundary factor** `BchartLeafGen ha y := paramsEquivFlat M (BparamsLeafGen ha y)`.
The general-`L` lift of `RouteMLeafBData.BchartLeaf`. -/
def BchartLeafGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  paramsEquivFlat M (BparamsLeafGen M ha y)

/-! ## The per-layer chart-component ↔ `Agen` bridge (bankable, no fderiv/Schur collapse)

The foundation the per-boundary fderiv-Schur-collapse (`eihd_hD_gen`) stands on: every boundary
component of `BparamsLeafGen` is, after the ambient→`M` width reindex, the chain layer
`Agen 1 … s.val` of the live decoder. This is pure `chartParamsGen`/`reindex` algebra (the banked
`hAgen`), independent of the differentiation. The general-`L` lift of the `L = 2`
`reindexL0_BparamsLeaf0` / `reindexL1_BparamsLeaf1` (which additionally special-cased the leaf and the
row split). -/

/-- **Per-layer chart-component identity** — `reindex (BparamsLeafGen ha z s) = Agen 1 … s.val`. The
`BparamsLeafGen` layer `s` (a `Matrix (M s.castSucc) (M s.succ)`), reindexed by the width equalities
`Wext s.val = M s.castSucc` / `Wext (s.val+1) = M s.succ`, IS the live decoder's chain layer
`Agen 1 M (tach M) (genBlkFlatLive …) hle s.val`. Direct from the banked `hAgen` (the reindex is the
same `Fin.cast`-valued composite) at `u = 1` and the achiever block data. -/
theorem reindexLs_BparamsLeafGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (z : Fin (routeMAmbient M) → ℝ) (s : Fin L) :
    Matrix.reindex (finCongr (hWgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha z) z)
        (hleStruct M (tach M) ha) s.val (le_of_lt s.isLt)))
        (finCongr (hWgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha z) z)
          (hleStruct M (tach M) ha) (s.val + 1) s.isLt))
        (Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha z) z)
          (hleStruct M (tach M) ha) s.val)
      = (BparamsLeafGen M ha z s :
          Matrix (Fin (M (s.castSucc))) (Fin (M (s.succ))) ℝ) := by
  -- `chainOfMt.A = Agen` (`rfl`), and `BparamsLeafGen … s = chartParamsGen 1 … s` (`rfl`), so this is
  -- exactly the banked `hAgen` at `u = 1`, block data the achiever's live decoder.
  exact hAgen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha z) z)
    (hleStruct M (tach M) ha) s.val s.isLt

/-! ### The per-layer reader fderiv atoms (`readN`/`readW`/`readX` are coordinate reads)

Each Schur/lift reader is a matrix of single-coordinate reads (`read· x k i j = x (·slot k i j)`,
banked in `RouteMInteriorLiveGenChart`), so its fderiv is the constant `matrixReaderCLM (·slot k)`
(`hasFDerivAt_matrixRead`). These are the leaf atoms `hasFDerivAt_chainA` consumes in the per-layer
`Agen`-fderiv (the grouping-2 infra for `eihd_hD_gen`). -/

/-- `fun z => readN z k` (as a matrix function) has fderiv `matrixReaderCLM (readNslot k)`. -/
theorem hasFDerivAt_readN (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (fun z : Fin (routeMAmbient M) → ℝ =>
        (Matrix.of (fun i j => readN M (tach M) ha z k i j) :
          Matrix (Fin (Text M (tach M) (k.val + 2)))
            (Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) ℝ))
      (matrixReaderCLM (fun i j => readNslot M ha k i j)) y₀ := by
  have : (fun z : Fin (routeMAmbient M) → ℝ =>
        (Matrix.of (fun i j => readN M (tach M) ha z k i j) : Matrix _ _ ℝ))
      = fun z => Matrix.of (fun i j => z (readNslot M ha k i j)) := by
    funext z; rfl
  rw [this]; exact hasFDerivAt_matrixRead _ y₀

/-- `fun z => readX z k` has fderiv `matrixReaderCLM (readXslot k)`. -/
theorem hasFDerivAt_readX (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (fun z : Fin (routeMAmbient M) → ℝ =>
        (Matrix.of (fun i j => readX M (tach M) ha z k i j) :
          Matrix (Fin (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2)))
            (Fin (Text M (tach M) (k.val + 2))) ℝ))
      (matrixReaderCLM (fun i j => readXslot M ha k i j)) y₀ := by
  have : (fun z : Fin (routeMAmbient M) → ℝ =>
        (Matrix.of (fun i j => readX M (tach M) ha z k i j) : Matrix _ _ ℝ))
      = fun z => Matrix.of (fun i j => z (readXslot M ha k i j)) := by
    funext z; rfl
  rw [this]; exact hasFDerivAt_matrixRead _ y₀

/-- `fun z => readW z k hk` has fderiv `matrixReaderCLM (readWslot k hk)` (deep interior `k+1 < L`). -/
theorem hasFDerivAt_readW (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (hk : k.val + 1 < L) (y₀ : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (fun z : Fin (routeMAmbient M) → ℝ =>
        (Matrix.of (fun i j => readW M (tach M) ha z k hk i j) :
          Matrix (Fin (Wext M (k.val + 1) - Text M (tach M) (k.val + 2)))
            (Fin (Wext M (k.val + 2))) ℝ))
      (matrixReaderCLM (fun i j => readWslot M ha k hk i j)) y₀ := by
  have : (fun z : Fin (routeMAmbient M) → ℝ =>
        (Matrix.of (fun i j => readW M (tach M) ha z k hk i j) : Matrix _ _ ℝ))
      = fun z => Matrix.of (fun i j => z (readWslot M ha k hk i j)) := by
    funext z; rfl
  rw [this]; exact hasFDerivAt_matrixRead _ y₀

/-- **The live decoder's deep-interior `Wblk (k+1) = readW ⟨k⟩`** (`k + 1 < L`) — the `Wblk_succ`
analogue of `RouteMHmapGen.genBlkFlatLive_Nblk_succ`. The chain lift block at boundary `k+1` is the
reader `readW ⟨k⟩` (a slot-`k` LIFT coord). The DECISIVE fact for placing the `−Nblk·Wblk` coupling
off-diagonal in `eihd_hD_gen`: with `Nblk (k+1) = readN⟨k⟩` (slot-`k` frame) and `Wblk (k+1) =
readW⟨k⟩` (slot-`k` lift), the layer-`(k+1)` `−N·W` term reads only slot-`k` coords. -/
theorem genBlkFlatLive_Wblk_succ (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ)
    (k : ℕ) (hk : k < L) (hk2 : k + 1 < L) :
    (genBlkFlatLive M t ha rfin x).Wblk (k + 1) = readW M t ha x ⟨k, hk⟩ hk2 := by
  show (genBlkFlatStruct M t ha x).Wblk (k + 1) = _
  simp only [genBlkFlatStruct, dif_pos hk, dif_pos hk2]

/-- **The flat-Jacobian** `DtotGen ha y₀ := fderiv ℝ (BchartLeafGen ha) y₀` (as a linear map) — the
boundary-factor differential whose staircase det Factor 1 reads. -/
def DtotGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ) :=
  (fderiv ℝ (fun y => BchartLeafGen M ha y) y₀).toLinearMap

/-! ## The dimensionally-correct staircase (frame slot ⊕ lift slot per boundary)

DESIGN NOTE (corrected 2026-07-01). The pure-`SchurInc` staircase `schurStairMap` is NOT the flat
conjugate: the flat ambient decomposes (`chartIdxEquiv`, `card_chartIdx` PROVEN) as
`⊕_{k : Fin L} (Fin (schurDim k) ⊕ Fin (liftDim k))` — a **frame slot** (`schurDim k = Text(k+1)·
Wext(k+1)`, the `K/X/N/E` roles = `SchurInc_k`) PLUS a **lift slot** (`liftDim k`, the chain lift
`W_k`; `0` at the leaf). The pure-`SchurInc` product omits the `∑_k liftDim_k` lift coordinates, so no
equiv exists. The correct staircase boundary space is `genV k = (frame slot k) × (lift slot k)`,
dimensionally EXACT against the flat ambient. The diagonal block carries `schurFrameDeriv` on the
frame (det `|det K_k|^{r_k+c_k}`) and identity on the lift (det `1`); couplings are the chain feed.
This mirrors the `L = 2` `eihdV` (`V0 = SchurInc_0`, `V1 = (W_0, leaf)`) faithfully. Consumes the
general `stairMap` spine (`RouteMStairFold`), NOT `schurStairMap`. -/

/-- **The per-boundary staircase space** `genV k = (frame slot k) × (lift slot k)` — the flat
coordinates of boundary `k`: the Schur-frame slot (`Fin (schurDim k) → ℝ`, the `SchurInc_k` roles) and
the chain-lift slot (`Fin (liftDim k) → ℝ`, the lift `W_k`; trivial at the leaf). Dimensionally exact:
`⊕_{k : Fin L} genV k` matches the flat ambient (`chartIdxEquiv`). -/
abbrev genV (M : Fin (L + 1) → ℕ) : ℕ → Type := fun k =>
  (Fin (schurDim M (tDesc M (tach M)) k) → ℝ) × (Fin (liftDim M (tDesc M (tach M)) k) → ℝ)

/-! ### The Pi-over-`Fin n` ↔ `StairProd` bridge (general utility)

The nested-product `StairProd V n` is linearly equivalent to the flat Pi `∀ k : Fin n, V k.val` — the
head-tail recursion (`Fin.consLinearEquiv` at each step, with the `V (Fin.succ i) = V (i.val + 1)`
index bridge). This is the collector that turns the per-boundary Pi (from `chartIdxEquiv` + `piCurry`)
into the staircase product the `stairMap` spine consumes. -/

/-- The head-tail split `(∀ k : Fin (n+1), V k.val) ≃ₗ V 0 × (∀ i : Fin n, V (i.val + 1))` — the
`Fin.cons` split, the tail reindexing `V i.succ.val = V (i.val + 1)` (`rfl`). -/
def headTailFinPi (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] (n : ℕ) :
    ((k : Fin (n + 1)) → V k.val) ≃ₗ[ℝ] V 0 × ((i : Fin n) → V (i.val + 1)) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 (fun i => p.2 i)
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    simp [Fin.cons_succ]
  right_inv p := by
    refine Prod.ext rfl ?_
    funext i
    simp [Fin.cons_succ]

/-- **The Pi ↔ StairProd bridge** `(∀ k : Fin n, V k.val) ≃ₗ StairProd V n`, by recursion on `n`. At
`n = 0` both are `Subsingleton` (`Fin 0` Pi / `PUnit`); at `n+1`, split the head `k = 0` off with
`headTailFinPi` and recurse on the tail `V (·+1)`. -/
def piToStair (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    (n : ℕ) → ((k : Fin n) → V k.val) ≃ₗ[ℝ] StairProd V n
  | 0 =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => fun k => k.elim0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => funext fun k => k.elim0
      right_inv := fun _ => rfl }
  | (n + 1) =>
    -- `(∀ k : Fin (n+1), V k) ≃ V 0 × (∀ i : Fin n, V (i+1)) ≃ V 0 × StairProd (V∘succ) n`.
    (headTailFinPi V n).trans
      ((LinearEquiv.refl ℝ (V 0)).prodCongr (piToStair (fun k => V (k + 1)) n))

/-! ### The faithful general-`L` frame reshape `(frame slot k) ≃ₗ SchurInc_k`

The frame slot at boundary `k` (`schurDim k = Text(k+1)·Wext(k+1)`) reshapes to the `SchurInc
(t_k)(r_k)(c_k)` tuple via the SAME `frameSplitEquiv M (tach M) (k+1)` the readers use: reindex
`Fin (schurDim k) → ℝ` by `frameSplitEquiv.symm` to the role-Sum-indexed Pi `(((K⊕X)⊕N)⊕E) → ℝ`,
split off each role by `sumArrowLequivProdArrow`, reshape each to its matrix, and REORDER
`(K, X, N, E) → (K, N, X, E)` to match `SchurInc`'s tuple. General-`L` lift of `RouteMHDtotEihd`'s
`frameToSchurInc` / `roleReorderLE` / `flatMatLE`. -/

/-- `(Fin (a*b) → ℝ) ≃ₗ Matrix (Fin a) (Fin b) ℝ` — the flat-slot ↔ matrix reshape (local copy,
avoids importing the L=2 module). -/
noncomputable def flatMatLEGen (a b : ℕ) :
    (Fin (a * b) → ℝ) ≃ₗ[ℝ] Matrix (Fin a) (Fin b) ℝ :=
  (LinearEquiv.funCongrLeft ℝ ℝ finProdFinEquiv).trans
    ((LinearEquiv.curry ℝ ℝ (Fin a) (Fin b)).trans (Matrix.ofLinearEquiv ℝ))

/-- Reorder/reshape `(((K × X) × N) × E) → SchurInc (K, N, X, E)` at general per-boundary widths —
`frameSplitEquiv`'s role order is `(((K⊕X)⊕N)⊕E)` but `SchurInc`/`readK…` is `(K, N, X, E)`. -/
noncomputable def roleReorderLEGen (t r c : ℕ) :
    ((((Fin (t * t) → ℝ) × (Fin (r * t) → ℝ)) × (Fin (t * c) → ℝ)) × (Fin (r * c) → ℝ))
      ≃ₗ[ℝ] SchurInc t r c where
  toFun p :=
    (flatMatLEGen t t p.1.1.1, flatMatLEGen t c p.1.2, flatMatLEGen r t p.1.1.2, flatMatLEGen r c p.2)
  invFun z :=
    ((((flatMatLEGen t t).symm z.1, (flatMatLEGen r t).symm z.2.2.1),
      (flatMatLEGen t c).symm z.2.1), (flatMatLEGen r c).symm z.2.2.2)
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add, map_add]; rfl
  map_smul' r a := by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]; rfl
  left_inv p := by simp only [LinearEquiv.symm_apply_apply]
  right_inv z := by simp only [LinearEquiv.apply_symm_apply]

/-- **The faithful frame reshape** `(Fin (schurDim k) → ℝ) ≃ₗ SchurInc (t_k)(r_k)(c_k)` at boundary
`k : Fin L` — the general-`L` `frameToSchurInc`. Reindex by `frameSplitEquiv (k+1)`, peel the nested
`⊕` (E, N, X, K), reshape + reorder to `(K, N, X, E)`. -/
noncomputable def frameToSchurIncGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L) :
    (Fin (schurDim M (tDesc M (tach M)) k.val) → ℝ)
      ≃ₗ[ℝ] SchurInc (schurTGen M k.val) (schurRGen M k.val) (schurCGen M k.val) :=
  (LinearEquiv.funCongrLeft ℝ ℝ
      (frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm).trans
    (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans
        ((((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).trans
            (((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ ℝ).prodCongr
              (LinearEquiv.refl ℝ _)))).prodCongr (LinearEquiv.refl ℝ _)))).trans
      (roleReorderLEGen (schurTGen M k.val) (schurRGen M k.val) (schurCGen M k.val)))

/-- The `.toLinearMap`-form conjugation det: `det (e.symm ∘ f ∘ e) = det f` (via `LinearMap.det_conj`
on `e.symm`, restated so it matches `.toLinearMap` composites). -/
theorem det_symm_conj_toLinearMap {E₁ E₂ : Type} [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂]
    [Module ℝ E₂] [FiniteDimensional ℝ E₁] (f : E₂ →ₗ[ℝ] E₂) (e : E₁ ≃ₗ[ℝ] E₂) :
    LinearMap.det (e.symm.toLinearMap ∘ₗ f ∘ₗ e.toLinearMap) = LinearMap.det f := by
  have h := LinearMap.det_conj f e.symm
  rw [LinearEquiv.symm_symm] at h
  exact h

/-- **The per-boundary diagonal block** `genF k : genV k →ₗ genV k` — `schurFrameDeriv (readX k)
(readK k) (readN k)` conjugated onto the frame slot by `frameToSchurIncGen` (det `|det K_k|^{r_k+c_k}`),
identity on the lift slot (det `1`). For `k ≥ L` the block is `id` (the staircase reads only `k < L`).
The `readK/X/N k` are read at the free point `y₀`.

## WHY this IS the diagonal block of the conjugated Jacobian (auditable soundness argument)

`genF k = schurFrameDeriv_k ⊕ id` is claimed (in `eihd_hD_gen`) to equal the slot-`k`→slot-`k`
DIAGONAL block of `T = eihdOutGen ∘ DtotGen ∘ eInGen.symm`. This holds — audit against the defs:

The chart's layer-`s` matrix is `Agen … s = chainA (Nblk s) (Wblk s) (Cgen (s+1))`
(`RouteMGenChain.Agen`/`RouteMChainBlock.chainA`); its rows split (`packRowSplitGen`) into the top
`Text(s+1)` KEPT rows `Cgen(s+1) − Nblk_s · Wblk_s` and the bottom LIFT rows `Wblk_s`. The staggered
pack (`packStairGen` via `liftGatherFinL`) routes: `genV`-slot-`s` **frame** ← KEPT rows of layer `s`;
`genV`-slot-`s` **lift** ← LIFT rows of layer `s+1` (`Wblk_{s+1}`).

* **Frame half `= schurFrameDeriv_k`.** The diagonal frame output is the fderiv of layer-`s`'s KEPT
  block `Cgen(s+1) − Nblk_s·Wblk_s`, restricted to slot-`s` INPUT coordinates.
  - `Cgen (s+1) = schurFrameProd (readK⟨s⟩, readX⟨s⟩, readN⟨s⟩, readE⟨s⟩)`
    (`RouteMHmapGen.Cgen_live_interior_eq_schurFrameProd`) — its readers are all boundary-`s`
    (slot-`s`) coords; `Cgen` is built from `Bmat/Nblk/Rmat`, NOT `Wblk` (`RouteMGenChain.Cgen`), so it
    contributes NO same-slot lift term. Its fderiv is `schurFrameDeriv_s` (the width-generic
    `schurFrameMap`/`schurFrameD`; the `L = 2` witness `RouteMProjV0Gate.gate_schurCore_eq`).
  - the `−Nblk_s·Wblk_s` correction reads `Nblk_s = readN⟨s−1⟩` (`RouteMHmapGen.genBlkFlatLive_Nblk_succ`:
    `.Nblk (k+1) = readN⟨k⟩`) — a slot-`(s−1)` FRAME coord — and `Wblk_s` — a slot-`(s−1)` LIFT coord
    (by the stagger, `Wblk_s` = layer-`s` lift ↦ slot `s−1`). So BOTH its fderiv terms
    `−(δNblk_s)·Wblk_s(y₀)` and `−Nblk_s(y₀)·(δWblk_s)` are variations of slot-`(s−1)` inputs feeding
    the slot-`s` frame output ⇒ strictly LOWER (slot `s−1 → s`), NOT on the diagonal. They are the
    head-into-tail chain feed captured by `eihdcGen` (det-invisible). Hence the diagonal frame block is
    `schurFrameDeriv_s` alone.
* **Lift half `= id`.** The slot-`s` lift INPUT is `Wblk_{s+1}` (layer `s+1`'s lift). In the chart, the
  bottom rows of `Agen … (s+1)` are `Wblk_{s+1}` verbatim (`chainA` lift rows = `W`), and the off-by-one
  gather (`liftGatherFinL`, `gatherShift`) routes that OUTPUT back to slot `s`'s lift — same slot as the
  input. So the lift diagonal is `id`. The induced `−Nblk_{s+1}(y₀)·(δWblk_{s+1})` lands in the layer-
  `(s+1)` frame ⇒ slot `s+1` ⇒ off-diagonal.

Soundness verdict VERIFIED by two decorrelated Codex `xhigh` passes (2026-07-01); the decisive fact is
the `Nblk_s = readN⟨s−1⟩` index shift moving the `−N·W` coupling strictly off-diagonal. This is NOT the
removed green-but-wrong `eihdOutGen := eInGen` single-conjugate (there the Params-LAYER output was
mis-paired with the SLOT input, so `diag ≠ genF`); the STAGGERED pack makes `diag = genF k` genuine. -/
noncomputable def genF (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    (k : ℕ) → genV M k →ₗ[ℝ] genV M k := fun k =>
  if hk : k < L then
    ((frameToSchurIncGen M ha ⟨k, hk⟩).symm.toLinearMap
        ∘ₗ schurFrameDeriv (readX M (tach M) ha y₀ ⟨k, hk⟩) (readK M (tach M) ha y₀ ⟨k, hk⟩)
            (readN M (tach M) ha y₀ ⟨k, hk⟩)
        ∘ₗ (frameToSchurIncGen M ha ⟨k, hk⟩).toLinearMap).prodMap LinearMap.id
  else LinearMap.id

/-- **The per-boundary det** `|det (genF k)| = |det K_k|^{r_k+c_k}` at an interior `k` (`0` at the
leaf's `0×0` K). The frame block is `schurFrameDeriv` conjugated by `frameToSchurIncGen` (det-invariant,
`schurFrame_abs_det`), the lift block is `id` (det `1`). -/
theorem genF_abs_det (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) (k : Fin L) :
    |LinearMap.det (genF M ha y₀ k.val)|
      = |(Matrix.of (readK M (tach M) ha y₀ k)).det|
        ^ ((Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
          + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))) := by
  have hk : (k : ℕ) < L := k.isLt
  rw [genF, dif_pos hk, LinearMap.det_prodMap, LinearMap.det_id, mul_one,
    det_symm_conj_toLinearMap, schurFrame_abs_det]
  -- `⟨↑k, hk⟩ = k` (Fin.eta, defeq) + `schurRGen/schurCGen` unfold (defeq) to the `Text`/`Wext`
  -- exponent — the remaining goal is definitional.
  rfl

/-- **The input layer-collecting equiv** `eInGen : (Fin (routeMAmbient M) → ℝ) ≃ₗ StairProd genV L` —
the `chartIdxEquiv`-based reshape collecting the per-boundary (frame slot ⊕ lift slot). Concrete and
reachable (funCongrLeft chartIdxEquiv.symm ≫ piCurry ≫ the per-boundary sum-split), unlike the
abstract recursion. LOAD-BEARING RESIDUAL. -/
def eInGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (Fin (routeMAmbient M) → ℝ) ≃ₗ[ℝ] StairProd (genV M) L :=
  -- flat → ChartIdx-Pi → nested Π (piCurry) → per-boundary sum-split (genV k) → StairProd (piToStair).
  (LinearEquiv.funCongrLeft ℝ ℝ
      (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm) ≪≫ₗ
  (LinearEquiv.piCurry ℝ (κ := fun k : Fin L =>
      Fin (schurDim M (tDesc M (tach M)) k.val) ⊕ Fin (liftDim M (tDesc M (tach M)) k.val))
      (fun _ _ => ℝ)) ≪≫ₗ
  (LinearEquiv.piCongrRight (fun k : Fin L =>
      LinearEquiv.sumArrowLequivProdArrow (Fin (schurDim M (tDesc M (tach M)) k.val))
        (Fin (liftDim M (tDesc M (tach M)) k.val)) ℝ ℝ)) ≪≫ₗ
  piToStair (genV M) L

/-! ### The STAGGERED output pack `eihdOutGen` (design corrected 2026-07-01, round 2)

DESIGN NOTE (round-2 correction). The earlier `eihdOutGen := eInGen` (single-conjugate) was
GREEN-BUT-WRONG for the block identity: `eInGen` reads coords in the `chartIdxEquiv` SLOT layout, but
`DtotGen`'s OUTPUT lives in the `paramsEquivFlat` Params-LAYER layout — unrelated `Fintype.equivFin`
bijections, so `diag(T) s = genF s` is FALSE (numeric L=3 `(2,4,3,2)`: slot 17/9/0 vs Params-layer
8/12/6, per-position mismatch). The FIX (genm-crux + Codex + numeric): a STAGGERED output pack in the
EXISTING `genV` — `genV` slot `s` ← `kept(layer s) ⊕ lift(layer s+1)` (dims balance exactly:
`kept(layer s) = Text(s+1)·Wext(s+1) = schurDim_s`, `lift(layer s+1) = liftDim_s`). The stagger (lift
of Params layer `s+1` → `genV` slot `s`'s lift) is why the per-position mismatch is no obstruction; it
mirrors the `L = 2` `bigToFlatIdx` (W/leaf → Params layer `1`). ROUTE B (Codex `high`, 2026-07-01):
build `packStairGen : Params M ≃ₗ StairProd genV L` DIRECTLY (per-layer row-split via `piCongrRight` +
the off-by-one lift gather via `piCongrLeft'` + `piToStair`), then `eihdOutGen := packStairGen ∘
paramsEquivFlatLinear.symm` — cleaner than the Route-A `ChartIdx ≃ FlatIdx` index bijection (200+ LoC
Sigma bookkeeping). The off-by-one gather (lift `s ↦ s+1`, layers `1..L−1 ≃ pred → slots 0..L−2`, with
`lift 0 = 0` and `genLift (L−1) = 0` the padded ends) is the irreducible combinatorial core. -/

/-! ### Route-B brick 1: the per-layer row-split -/

/-- **The per-layer row-split** `packRowSplitGen s : Matrix (Wext s) (Wext s+1) ≃ₗ (kept_s) × (lift_s)`
— the layer-`s` matrix (`= Params M s` after the `M s.castSucc = Wext s` recast) splits its rows into
the top `Text(s+1)` (KEPT → the frame block `Matrix (Text(s+1)) (Wext(s+1))`) and the bottom
`Wext(s)−Text(s+1)` (LIFT → the lift block `Matrix (Wext(s)−Text(s+1)) (Wext(s+1))`). Via `genWidthEq`
(`Text(s+1)+(Wext s−Text(s+1))=Wext s`) row recast + `finSumFinEquiv.symm` split + `sumArrowLequivProdArrow`.
Route-B brick 1 (sorry-free). -/
noncomputable def packRowSplitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (s : Fin L) :
    Matrix (Fin (Wext M s.val)) (Fin (Wext M (s.val + 1))) ℝ ≃ₗ[ℝ]
      (Matrix (Fin (Text M (tach M) (s.val + 1))) (Fin (Wext M (s.val + 1))) ℝ) ×
      (Matrix (Fin (Wext M s.val - Text M (tach M) (s.val + 1))) (Fin (Wext M (s.val + 1))) ℝ) :=
  (Matrix.reindexLinearEquiv ℝ ℝ
      (finCongr (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt).symm)
      (Equiv.refl _)) ≪≫ₗ
    (Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv.symm (Equiv.refl _)) ≪≫ₗ
    (Matrix.ofLinearEquiv ℝ).symm ≪≫ₗ
    (LinearEquiv.sumArrowLequivProdArrow (Fin (Text M (tach M) (s.val + 1)))
      (Fin (Wext M s.val - Text M (tach M) (s.val + 1))) ℝ (Fin (Wext M (s.val + 1)) → ℝ)) ≪≫ₗ
    ((Matrix.ofLinearEquiv ℝ).prodCongr (Matrix.ofLinearEquiv ℝ))

/-- **Pi-of-product split** `(∀ i, A i × B i) ≃ₗ (∀ i, A i) × (∀ i, B i)` — the `LinearEquiv` mirror
of `Equiv.arrowProdEquivProdArrow` (Mathlib has only the `Equiv`/`MeasurableEquiv` forms). Separates
the frame-Pi from the lift-Pi after the per-layer `packRowSplitGen` split, so the lift-Pi alone feeds
the `sigmaGather` reindex. Reusable Route-B assembly brick. -/
def piProdSplit {ι : Type} (A B : ι → Type)
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℝ (B i)] :
    ((i : ι) → A i × B i) ≃ₗ[ℝ] ((i : ι) → A i) × ((i : ι) → B i) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by funext i; rfl
  right_inv p := rfl

/-! ### Route-B brick 2: the off-by-one lift Sigma-gather (the combinatorial core) -/

/-- **The off-by-one Sigma-gather** — for two width families `blk lift : Fin (n+1) → ℕ` with
`blk 0 = 0`, `lift (last) = 0`, and `blk i.succ = lift i.castSucc` (the shift identity), the flat
lift index of `Params` (`Σ k, Fin (blk k)`) reindexes bijectively to the `genV` lift index
(`Σ k, Fin (lift k)`) via `k ↦ k−1` (the nonzero part; the two `0`-dim ends `blk 0`, `lift last`
cancel). The irreducible combinatorial core of the staggered pack (`Fin.cases`/`Fin.lastCases` on the
boundary, closed by `Fin.cases_succ`/`Fin.lastCases_castSucc`). Sorry-free. -/
def sigmaGather (n : ℕ) (blk lift : Fin (n + 1) → ℕ)
    (h0 : blk 0 = 0) (hlast : lift (Fin.last n) = 0)
    (hshift : ∀ i : Fin n, blk i.succ = lift i.castSucc) :
    (Σ k : Fin (n + 1), Fin (blk k)) ≃ (Σ k : Fin (n + 1), Fin (lift k)) where
  toFun := fun ⟨k, i⟩ => by
    refine Fin.cases ?_ ?_ k i
    · intro i0; rw [h0] at i0; exact i0.elim0
    · intro j i; exact ⟨j.castSucc, Fin.cast (hshift j) i⟩
  invFun := fun ⟨k, i⟩ => by
    refine Fin.lastCases ?_ ?_ k i
    · intro ilast; rw [hlast] at ilast; exact ilast.elim0
    · intro j i; exact ⟨j.succ, Fin.cast (hshift j).symm i⟩
  left_inv := by
    rintro ⟨k, i⟩
    refine Fin.cases ?_ ?_ k i
    · intro i0; rw [h0] at i0; exact i0.elim0
    · intro j i
      simp only [Fin.cases_succ, Fin.lastCases_castSucc, Fin.cast_cast, Fin.cast_eq_self]
  right_inv := by
    rintro ⟨k, i⟩
    refine Fin.lastCases ?_ ?_ k i
    · intro ilast; rw [hlast] at ilast; exact ilast.elim0
    · intro j i
      dsimp only
      rw [Fin.lastCases_castSucc]
      simp only [Fin.cases_succ, Fin.cast_cast, Fin.cast_eq_self]

/-- `sigmaGather` hyp `blk 0 = 0`: at boundary `0` the lift rows `Wext 0 − Text 1 = 0` (`Text 1 =
tDesc 0 = M 0 = Wext 0`, `ha.h0`). -/
theorem gatherBlk_zero (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (Wext M 0 - Text M (tach M) (0 + 1)) * Wext M (0 + 1) = 0 := by
  have h : Text M (tach M) (0 + 1) = Wext M 0 := by
    rw [show Wext M 0 = M 0 from by rw [Wext]; simp]
    have := ha.h0; rw [tDesc_apply] at this; exact this
  rw [h, Nat.sub_self, Nat.zero_mul]

/-- `sigmaGather` hyp `lift (last) = 0`: the leaf boundary `L−1` has `liftDim = 0`. -/
theorem gatherLift_last (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    liftDim M (tDesc M (tach M)) (L - 1) = 0 := by
  have hL := ha.hL; unfold liftDim; rw [if_neg (by omega)]

/-- `sigmaGather` hyp `blk (i+1) = lift i` (the shift identity): layer `i+1`'s lift rows =
`genV` slot `i`'s lift. -/
theorem gatherShift (M : Fin (L + 1) → ℕ) (i : ℕ) (hi : i < L - 1) :
    (Wext M (i + 1) - Text M (tach M) (i + 1 + 1)) * Wext M (i + 1 + 1)
      = liftDim M (tDesc M (tach M)) i := by
  unfold liftDim; rw [if_pos (by omega : i + 1 < L)]; rfl

/-- **Step-5 tool: a Pi-of-`→ℝ` reindex from a Σ-equiv.** Given a bijection `σ` between the flat
Σ-indices `Σ i, Fin (d i)` and `Σ i, Fin (e i)`, reindex the Pi of `→ℝ` charts:
`(∀ i, Fin (d i) → ℝ) ≃ₗ (∀ i, Fin (e i) → ℝ)` via `piCurry.symm ≫ funCongrLeft σ.symm ≫ piCurry`
(uncurry both Pis to a single `Σ → ℝ`, precompose with `σ.symm`, re-curry). Factor1's de-risked
composition tool. -/
noncomputable def piReindexOfSigma {ι : Type} (d e : ι → ℕ)
    (σ : (Σ i : ι, Fin (d i)) ≃ (Σ i : ι, Fin (e i))) :
    ((i : ι) → Fin (d i) → ℝ) ≃ₗ[ℝ] ((i : ι) → Fin (e i) → ℝ) :=
  (LinearEquiv.piCurry ℝ (fun (i : ι) (_ : Fin (d i)) => ℝ)).symm ≪≫ₗ
    (LinearEquiv.funCongrLeft ℝ ℝ σ.symm) ≪≫ₗ
    (LinearEquiv.piCurry ℝ (fun (i : ι) (_ : Fin (e i)) => ℝ))

/-- **The `Fin L`-indexed lift gather (transported).** The off-by-one lift Σ-bijection `sigmaGather`,
transported from its native `Fin ((L−1)+1)` indexing to the `Fin L` indexing via the base equiv
`finCongr (L = (L−1)+1)` and `Equiv.sigmaCongrLeft'`. Relates the per-layer lift block dim
`liftBlk k = (Wext k − Text(k+1))·Wext(k+1)` to the staggered `genV` lift dim `liftDim k` (`k ↦ k−1`).
The three `sigmaGather` hyps come from `gatherBlk_zero`/`gatherLift_last`/`gatherShift`. -/
noncomputable def liftGatherFinL (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L) :
    (Σ k : Fin L, Fin ((Wext M k.val - Text M (tach M) (k.val + 1)) * Wext M (k.val + 1)))
      ≃ (Σ k : Fin L, Fin (liftDim M (tDesc M (tach M)) k.val)) :=
  -- transport `finCongr hLe : Fin L ≃ Fin ((L−1)+1)` onto both sides of `sigmaGather (L−1)`.
  let hLe : L = (L - 1) + 1 := (Nat.succ_pred_eq_of_pos hL).symm
  let ecast : Fin L ≃ Fin ((L - 1) + 1) := finCongr hLe
  let blk : Fin ((L - 1) + 1) → ℕ := fun k =>
    (Wext M (ecast.symm k).val - Text M (tach M) ((ecast.symm k).val + 1)) * Wext M ((ecast.symm k).val + 1)
  let lift : Fin ((L - 1) + 1) → ℕ := fun k => liftDim M (tDesc M (tach M)) (ecast.symm k).val
  -- `Σ k : Fin L, Fin (blkL k) ≃ Σ k : Fin ((L−1)+1), Fin (blk k)` by `sigmaCongrLeft'` (β at `ecast.symm`).
  (Equiv.sigmaCongrLeft' (β := fun k : Fin L =>
      Fin ((Wext M k.val - Text M (tach M) (k.val + 1)) * Wext M (k.val + 1))) ecast).trans
    (-- the native off-by-one gather at `n = L−1`
    (sigmaGather (L - 1) blk lift
      (by
        -- `blk 0 = liftBlk (ecast.symm 0)`; `ecast.symm 0 = ⟨0,_⟩`, so this is `gatherBlk_zero`.
        show (Wext M (ecast.symm 0).val - Text M (tach M) ((ecast.symm 0).val + 1))
            * Wext M ((ecast.symm 0).val + 1) = 0
        have h0 : (ecast.symm 0).val = 0 := by
          simp only [ecast, finCongr_symm, finCongr_apply]; rfl
        rw [h0]; exact gatherBlk_zero M ha)
      (by
        -- `lift (last) = liftDim (ecast.symm last).val`; `(ecast.symm last).val = L−1`, so `gatherLift_last`.
        show liftDim M (tDesc M (tach M)) (ecast.symm (Fin.last (L - 1))).val = 0
        have hlast : (ecast.symm (Fin.last (L - 1))).val = L - 1 := by
          simp only [ecast, finCongr_symm, finCongr_apply, Fin.val_last, Fin.coe_cast]
        rw [hlast]; exact gatherLift_last M ha)
      (by
        -- `blk i.succ = lift i.castSucc`, i.e. `liftBlk (i.val+1) = liftDim (i.val)`, via `gatherShift`.
        intro i
        show (Wext M (ecast.symm i.succ).val - Text M (tach M) ((ecast.symm i.succ).val + 1))
              * Wext M ((ecast.symm i.succ).val + 1)
            = liftDim M (tDesc M (tach M)) (ecast.symm i.castSucc).val
        have hsucc : (ecast.symm i.succ).val = i.val + 1 := by
          simp only [ecast, finCongr_symm, finCongr_apply, Fin.coe_cast, Fin.val_succ]
        have hcast : (ecast.symm i.castSucc).val = i.val := by
          simp only [ecast, finCongr_symm, finCongr_apply, Fin.coe_cast, Fin.coe_castSucc]
        rw [hsucc, hcast]; exact gatherShift M i.val (by omega))).trans
    -- transport back to `Fin L` indexing
    (Equiv.sigmaCongrLeft' (β := fun k : Fin ((L - 1) + 1) =>
      Fin (liftDim M (tDesc M (tach M)) (ecast.symm k).val)) ecast.symm))

/-- **The staggered pack** `packStairGen : Params M ≃ₗ StairProd genV L` — the CORRECT Params-layer →
staircase reshape (ROUTE B). Assembly of banked bricks: (0) width-recast `Params M` layer `s`
(`M s.castSucc × M s.succ`) to `Wext s × Wext (s+1)`; (1) `piCongrRight packRowSplitGen` splits each
layer into `kept_s × liftblock_s`; (2) `piCongrRight (flatMatLEGen.symm × flatMatLEGen.symm)` flattens
both blocks to `Fin (schurDim s) → ℝ` and the lift flat `Fin (liftBlk s) → ℝ`; (3) `piProdSplit`
separates the frame-Pi from the lift-Pi; (4) `piReindexOfSigma (liftGatherFinL)` reindexes the lift-Pi
`liftBlk ↦ liftDim` (the off-by-one gather); (5) `piProdSplit.symm` recombines per slot to
`∀ k, genV k.val`; (6) `piToStair (genV M) L`. -/
noncomputable def packStairGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L) :
    Params M ≃ₗ[ℝ] StairProd (genV M) L :=
      -- (0) width recast: `Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ≃ Matrix (Fin (Wext s)) (Fin (Wext (s+1)))`
      (LinearEquiv.piCongrRight (fun s : Fin L =>
        Matrix.reindexLinearEquiv ℝ ℝ
          (finCongr (show M s.castSucc = Wext M s.val by rw [Wext_apply M s.val (by omega)]; rfl))
          (finCongr (show M s.succ = Wext M (s.val + 1) by rw [Wext_apply M (s.val + 1) (by omega)]; rfl)))) ≪≫ₗ
      -- (1) per-layer row-split
      (LinearEquiv.piCongrRight (fun s : Fin L => packRowSplitGen M ha s)) ≪≫ₗ
      -- (2) flatten frame + lift blocks
      (LinearEquiv.piCongrRight (fun s : Fin L =>
        (flatMatLEGen (Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))).symm.prodCongr
          (flatMatLEGen (Wext M s.val - Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))).symm)) ≪≫ₗ
      -- (3) split frame-Pi from lift-Pi
      (piProdSplit (fun s : Fin L => Fin (Text M (tach M) (s.val + 1) * Wext M (s.val + 1)) → ℝ)
        (fun s : Fin L => Fin ((Wext M s.val - Text M (tach M) (s.val + 1)) * Wext M (s.val + 1)) → ℝ)) ≪≫ₗ
      -- (4) reindex the lift-Pi by the off-by-one gather
      ((LinearEquiv.refl ℝ ((s : Fin L) → Fin (Text M (tach M) (s.val + 1) * Wext M (s.val + 1)) → ℝ)).prodCongr
        (piReindexOfSigma
          (fun k : Fin L => (Wext M k.val - Text M (tach M) (k.val + 1)) * Wext M (k.val + 1))
          (fun k : Fin L => liftDim M (tDesc M (tach M)) k.val)
          (liftGatherFinL M ha hL))) ≪≫ₗ
      -- (5) recombine frame ⊕ gathered-lift per slot into `∀ k, genV k.val`
      (piProdSplit (fun s : Fin L => Fin (schurDim M (tDesc M (tach M)) s.val) → ℝ)
        (fun s : Fin L => Fin (liftDim M (tDesc M (tach M)) s.val) → ℝ)).symm ≪≫ₗ
      -- (6) collect to the staircase
      (piToStair (genV M) L)

/-- **The staggered output pack** `eihdOutGen : (Fin (routeMAmbient M) → ℝ) ≃ₗ StairProd genV L` — the
CORRECT output reshape. `eihdOutGen := packStairGen ∘ paramsEquivFlatLinear.symm` (the controller's
directive; reuses the banked `paramsEquivFlatLinear : Params M ≃ₗ (Fin flatDim → ℝ)` for the
flat↔Params grouping, `routeMAmbient M = flatDim M` by `finCongr`). LOAD-BEARING RESIDUAL (thin — the
content is in `packStairGen`). -/
def eihdOutGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (Fin (routeMAmbient M) → ℝ) ≃ₗ[ℝ] StairProd (genV M) L :=
  -- `routeMAmbient M = flatDim M` DEFINITIONALLY (`RouteMExtraction.routeMAmbient`), so
  -- `(paramsEquivFlatLinear M).symm : (Fin (routeMAmbient M) → ℝ) ≃ₗ Params M` typechecks directly;
  -- compose with the staggered pack `packStairGen` (`0 < L` from `ha.hL`).
  (paramsEquivFlatLinear M).symm ≪≫ₗ packStairGen M ha ha.hL

/-- **Extract the staircase coupling from any endomorphism.** For `T : StairProd V n →ₗ StairProd V n`,
`stairCouplingOf` reads off, at each depth, the head-into-tail block `projTail ∘ T ∘ inclHead`
(recursing on the tail endomorphism `projTail ∘ T ∘ inclTail`). This is the coupling datum such that
`stairMap V n (diag of T) (stairCouplingOf T)` reproduces `T`'s lower-triangular part — the general-`L`
lift of the `L = 2` `eihdc_free` construction (`⟨projTail ∘ T ∘ inclV0, …⟩`). -/
def stairCouplingOf (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    (n : ℕ) → (StairProd V n →ₗ[ℝ] StairProd V n) → StairCoupling V n
  | 0, _ => PUnit.unit
  | (n + 1), T =>
    -- `StairProd V (n+1) = V 0 × StairProd (V∘succ) n`; head `V 0`, tail `StairProd (V∘succ) n`.
    ⟨(LinearMap.snd ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
        (T.comp (LinearMap.inl ℝ (V 0) (StairProd (fun k => V (k + 1)) n))),
     stairCouplingOf (fun k => V (k + 1)) n
       ((LinearMap.snd ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
         (T.comp (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n))))⟩

/-- **Lower-triangular-with-diagonal-`f` predicate** for a `StairProd` endomorphism, recursive on depth.
At `n = 0` (`PUnit`), trivially true. At `n+1`: the head-diagonal block `fst ∘ T ∘ inl = f 0`, the
upper block `fst ∘ T ∘ inr = 0`, and the tail endomorphism `snd ∘ T ∘ inr` is again
lower-triangular-with-diagonal-`f∘succ`. (The head-into-tail coupling `snd ∘ T ∘ inl` is unconstrained
— it is captured by `stairCouplingOf`.) -/
def StairLowerTriDiag (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    (n : ℕ) → ((s : ℕ) → V s →ₗ[ℝ] V s) → (StairProd V n →ₗ[ℝ] StairProd V n) → Prop
  | 0, _, _ => True
  | (n + 1), f, T =>
    (LinearMap.fst ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
        (T.comp (LinearMap.inl ℝ (V 0) (StairProd (fun k => V (k + 1)) n))) = f 0 ∧
    (LinearMap.fst ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
        (T.comp (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n))) = 0 ∧
    StairLowerTriDiag (fun k => V (k + 1)) n (fun s => f (s + 1))
      ((LinearMap.snd ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
        (T.comp (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n))))

/-- **The slot inclusion** `stairIncl V n s : V s →ₗ StairProd V n` — inject a single-boundary vector
into slot `s` of the staircase (zero elsewhere). Slot `0` is the head (`inl`); slot `j+1` recurses into
the tail via `inr`. Only meaningful for `s < n`; for `s ≥ n` it lands in the (subsingleton) tail. -/
def stairIncl (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    (n : ℕ) → (s : ℕ) → V s →ₗ[ℝ] StairProd V n
  | 0, _ => 0
  | (n + 1), 0 => LinearMap.inl ℝ (V 0) (StairProd (fun k => V (k + 1)) n)
  | (n + 1), (s + 1) =>
    (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
      (stairIncl (fun k => V (k + 1)) n s)

/-- **The slot projection** `stairProj V n s : StairProd V n →ₗ V s` — read boundary `s` off the
staircase. Slot `0` is the head (`fst`); slot `j+1` recurses via `snd`. -/
def stairProj (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    (n : ℕ) → (s : ℕ) → StairProd V n →ₗ[ℝ] V s
  | 0, _ => 0
  | (n + 1), 0 => LinearMap.fst ℝ (V 0) (StairProd (fun k => V (k + 1)) n)
  | (n + 1), (s + 1) =>
    (stairProj (fun k => V (k + 1)) n s).comp
      (LinearMap.snd ℝ (V 0) (StairProd (fun k => V (k + 1)) n))

/-- **Completeness of the slot decomposition** — any `x : StairProd V n` is the sum of its slot
inclusions: `x = Σ_{s : Fin n} stairIncl V n s (stairProj V n s x)`. Induction on `n`: at `n+1`, split
`x = (x.1, x.2)`; the head is slot `0` (`inl (fst x)`), and the tail expands by the IH, each tail slot
`j` re-included via `inr` (`= stairIncl (n+1) (j+1)`). -/
theorem stairProd_eq_sum_incl_proj (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    ∀ (n : ℕ) (x : StairProd V n),
      x = ∑ s : Fin n, (stairIncl V n s) (stairProj V n s x)
  | 0, x => by
      -- `StairProd V 0 = PUnit`; the empty sum is `0 = x` (subsingleton).
      haveI : Subsingleton (StairProd V 0) := (inferInstance : Subsingleton PUnit)
      rw [Fin.sum_univ_zero]
      exact Subsingleton.elim _ _
  | (n + 1), x => by
      -- `x = (x.1, x.2)`; head slot 0 = `inl x.1`, tail slots via IH re-included through `inr`.
      have hIH := stairProd_eq_sum_incl_proj (fun k => V (k + 1)) n x.2
      rw [Fin.sum_univ_succ]
      -- slot 0 term: `stairIncl (n+1) 0 (stairProj (n+1) 0 x) = inl x.1 = (x.1, 0)`.
      show x = (LinearMap.inl ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) x.1
          + ∑ i : Fin n, (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n))
              ((stairIncl (fun k => V (k + 1)) n i.val) (stairProj (fun k => V (k + 1)) n i.val x.2))
      rw [← map_sum]
      rw [show (∑ i : Fin n, (stairIncl (fun k => V (k + 1)) n i.val)
            (stairProj (fun k => V (k + 1)) n i.val x.2)) = x.2 from hIH.symm]
      refine Prod.ext ?_ ?_
      · show x.1 = x.1 + 0; rw [add_zero]
      · show x.2 = 0 + x.2; rw [zero_add]

/-- **`inr` as a sum of slot inclusions** — `inr vt = Σ_{j : Fin n} stairIncl V (n+1) (j+1) (stairProj
(V∘succ) n j vt)`. Apply `inr` (linear) to the tail completeness `stairProd_eq_sum_incl_proj`; each
`inr ∘ stairIncl (V∘succ) n j = stairIncl V (n+1) (j+1)` by def. -/
theorem stairInr_eq_sum_incl_proj (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    (n : ℕ) (vt : StairProd (fun k => V (k + 1)) n) :
    (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) vt
      = ∑ j : Fin n, (stairIncl V (n + 1) (j.val + 1))
          (stairProj (fun k => V (k + 1)) n j.val vt) := by
  conv_lhs => rw [stairProd_eq_sum_incl_proj (fun k => V (k + 1)) n vt]
  rw [map_sum]
  rfl

/-- **`StairLowerTriDiag` from per-slot block facts.** If, for the endomorphism `T`, every diagonal
slot block reads `genF`-diagonal (`stairProj s ∘ T ∘ stairIncl s = f s`) and every strictly-upper slot
block vanishes (`stairProj s' ∘ T ∘ stairIncl s = 0` for `s' < s`), then `StairLowerTriDiag V n f T`.
Induction on `n`: at `n+1`, the head-diag is the `s = 0` block, the upper block `fst ∘ T ∘ inr` = 0
comes from the `s' = 0 < s+1` upper facts (over all tail slots), and the tail endomorphism's blocks are
the `(s+1)`-shifted blocks of `T` (`stairIncl (s+1) = inr ∘ tailIncl s`, `stairProj (s+1) = tailProj s
∘ snd`), so the IH applies. -/
theorem stairLowerTriDiag_of_blocks (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    ∀ (n : ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (T : StairProd V n →ₗ[ℝ] StairProd V n),
      (∀ s, (stairProj V n s).comp (T.comp (stairIncl V n s)) = f s) →
      (∀ s s', s' < s → (stairProj V n s').comp (T.comp (stairIncl V n s)) = 0) →
      StairLowerTriDiag V n f T
  | 0, _, _, _, _ => trivial
  | (n + 1), f, T, hdiag, hupper => by
      refine ⟨?_, ?_, ?_⟩
      · -- head-diag: `fst ∘ T ∘ inl = f 0` is the `s = 0` diagonal block (stairProj/Incl 0 = fst/inl).
        exact hdiag 0
      · -- upper: `fst ∘ T ∘ inr = 0`. Expand the tail input over slots (`stairProd_eq_sum_incl_proj`):
        -- `inr vt = Σ_{j<n} stairIncl (n+1) (j+1) (stairProj (V∘succ) n j vt)`, and each
        -- `fst ∘ T ∘ stairIncl (n+1) (j+1) = stairProj 0 ∘ T ∘ stairIncl (j+1) = 0` (upper, `0<j+1`).
        apply LinearMap.ext
        intro vt
        show (LinearMap.fst ℝ (V 0) (StairProd (fun k => V (k + 1)) n))
            (T ((LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) vt)) = 0
        -- rewrite as `(fst ∘ₗ T) (inr vt)`, expand `inr vt` over slots, push through the linear map.
        rw [show (LinearMap.fst ℝ (V 0) (StairProd (fun k => V (k + 1)) n))
              (T ((LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) vt))
            = ((LinearMap.fst ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp T)
                ((LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) vt) from rfl,
          stairInr_eq_sum_incl_proj V n vt, map_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hj := hupper (j.val + 1) 0 (by omega)
        have := congrFun (congrArg (fun (m : _ →ₗ[ℝ] _) => (m : _ → _)) hj)
          (stairProj (fun k => V (k + 1)) n j.val vt)
        -- `((fst ∘ T) ∘ stairIncl (j+1)) = stairProj 0 ∘ T ∘ stairIncl (j+1) = 0` (upper 0<(j+1)).
        simpa only [LinearMap.comp_apply, stairProj] using this
      · -- tail: `StairLowerTriDiag (V∘succ) n (f∘succ) (snd ∘ T ∘ inr)`, by IH with the shifted blocks.
        refine stairLowerTriDiag_of_blocks (fun k => V (k + 1)) n (fun s => f (s + 1))
          ((LinearMap.snd ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
            (T.comp (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)))) ?_ ?_
        · intro s
          -- tail diag slot s = T's slot (s+1) diag: `tailProj s ∘ (snd ∘ T ∘ inr) ∘ tailIncl s`
          -- = `(tailProj s ∘ snd) ∘ T ∘ (inr ∘ tailIncl s)` = `stairProj (s+1) ∘ T ∘ stairIncl (s+1)`.
          have := hdiag (s + 1)
          simpa only [stairProj, stairIncl, LinearMap.comp_assoc] using this
        · intro s s' hs'
          have := hupper (s + 1) (s' + 1) (by omega)
          simpa only [stairProj, stairIncl, LinearMap.comp_assoc] using this

/-- **The reconstruction lemma**: a `StairLowerTriDiag`-`f` endomorphism `T` equals
`stairMap V n f (stairCouplingOf T)` — the couplings are captured automatically by `stairCouplingOf`,
so the crux `eihd_hD_gen` reduces to establishing `StairLowerTriDiag genV L genF T` (i.e. the two block
facts: head-diag `= genF s`, upper-block `= 0`, at every depth). Induction on `n`, peeling one
`lowerTri` per depth. -/
theorem stairMap_eq_of_lowerTriDiag (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] :
    ∀ (n : ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (T : StairProd V n →ₗ[ℝ] StairProd V n),
      StairLowerTriDiag V n f T → T = stairMap V n f (stairCouplingOf V n T)
  | 0, _, T, _ => by
      -- `StairProd V 0 = PUnit` is a subsingleton; any two maps agree.
      haveI : Subsingleton (StairProd V 0) := (inferInstance : Subsingleton PUnit)
      apply LinearMap.ext; intro x
      exact Subsingleton.elim _ _
  | (n + 1), f, T, hT => by
      obtain ⟨hdiag, hupper, htail⟩ := hT
      -- unfold `stairMap` and `stairCouplingOf` at `n+1`; the RHS is `lowerTri (f 0) (stairMap tail …)
      -- (coupling.1)`. Show `T = lowerTri …` by `LinearMap.ext` on `(v0, vtail)`, splitting via
      -- `hdiag` (head block), `hupper` (upper block = 0), and the tail IH on `snd ∘ T ∘ inr`.
      have hIH := stairMap_eq_of_lowerTriDiag (fun k => V (k + 1)) n (fun s => f (s + 1))
        ((LinearMap.snd ℝ (V 0) (StairProd (fun k => V (k + 1)) n)).comp
          (T.comp (LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)))) htail
      apply LinearMap.ext
      rintro ⟨v0, vt⟩
      -- decompose `(v0, vt) = inl v0 + inr vt`, push `T` through (map_add), and read the two components.
      have hTsplit : T (v0, vt)
          = T ((LinearMap.inl ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) v0)
            + T ((LinearMap.inr ℝ (V 0) (StairProd (fun k => V (k + 1)) n)) vt) := by
        rw [← map_add]; congr 1
        refine Prod.ext ?_ ?_
        · show v0 = _ + _; simp
        · show vt = _ + _; simp
      rw [hTsplit]
      -- LHS = T (inl v0) + T (inr vt); RHS (stairMap = lowerTri) = (f0 v0, tail vt + coupling v0).
      show T ((LinearMap.inl ℝ (V 0) _) v0) + T ((LinearMap.inr ℝ (V 0) _) vt)
        = ((f 0) v0, (stairMap (fun k => V (k + 1)) n (fun s => f (s + 1))
              (stairCouplingOf (fun k => V (k + 1)) n
                ((LinearMap.snd ℝ (V 0) _).comp (T.comp (LinearMap.inr ℝ (V 0) _)))) vt)
            + (LinearMap.snd ℝ (V 0) _).comp (T.comp (LinearMap.inl ℝ (V 0) _)) v0)
      refine Prod.ext ?_ ?_
      · -- fst: (fst (T (inl v0))) + (fst (T (inr vt))) = f0 v0 + 0
        show (T ((LinearMap.inl ℝ (V 0) _) v0)).1 + (T ((LinearMap.inr ℝ (V 0) _) vt)).1 = (f 0) v0
        have e0 : (T ((LinearMap.inl ℝ (V 0) _) v0)).1 = (f 0) v0 := by
          have := congrFun (congrArg (fun (m : _ →ₗ[ℝ] _) => (m : _ → _)) hdiag) v0
          simpa using this
        have e1 : (T ((LinearMap.inr ℝ (V 0) _) vt)).1 = 0 := by
          have := congrFun (congrArg (fun (m : _ →ₗ[ℝ] _) => (m : _ → _)) hupper) vt
          simpa using this
        rw [e0, e1, add_zero]
      · -- snd: (snd (T (inl v0))) + (snd (T (inr vt))) = tail vt + coupling v0
        show (T ((LinearMap.inl ℝ (V 0) _) v0)).2 + (T ((LinearMap.inr ℝ (V 0) _) vt)).2
          = (stairMap (fun k => V (k + 1)) n (fun s => f (s + 1))
              (stairCouplingOf (fun k => V (k + 1)) n
                ((LinearMap.snd ℝ (V 0) _).comp (T.comp (LinearMap.inr ℝ (V 0) _)))) vt)
            + ((LinearMap.snd ℝ (V 0) _).comp (T.comp (LinearMap.inl ℝ (V 0) _))) v0
        have etail : (T ((LinearMap.inr ℝ (V 0) _) vt)).2
            = (stairMap (fun k => V (k + 1)) n (fun s => f (s + 1))
                (stairCouplingOf (fun k => V (k + 1)) n
                  ((LinearMap.snd ℝ (V 0) _).comp (T.comp (LinearMap.inr ℝ (V 0) _)))) vt) := by
          have := congrFun (congrArg (fun (m : _ →ₗ[ℝ] _) => (m : _ → _)) hIH) vt
          simpa using this
        rw [etail, add_comm]
        rfl

/-- **The staircase coupling** `eihdcGen := stairCouplingOf (eInGen ∘ DtotGen ∘ eInGen.symm)` — the
head-into-tail chain feed read off the conjugated `DtotGen` (det-irrelevant). The general-`L` lift of
`RouteMHDtotEihd.eihdc_free`. -/
def eihdcGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    StairCoupling (genV M) L :=
  stairCouplingOf (genV M) L
    ((eihdOutGen M ha : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L)
      ∘ₗ DtotGen M ha y₀
      ∘ₗ ((eInGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ)))

/-- **The block identity `eihd_hD_gen`** — `eihdOutGen ∘ DtotGen ∘ eInGen.symm = stairMap genV L genF`.
The general-`L` lift of `RouteMEihdFreePoint.eihd_hD_free`: each diagonal block of `DtotGen` (in the
collected `genV` coords) is `genF k` (`schurFrameDeriv` on the frame ⊕ id on the lift); the couplings
are the chain feed. THE CRUX — the per-interior-boundary Schur-frame collapse of the `chainA` layer
fderiv, generalizing `layer0SchurMap_fderiv_collapse`. LOAD-BEARING RESIDUAL.

The soundness of the STATEMENT (`diag(T) k = genF k`, i.e. the diagonal block genuinely collapses to
`schurFrameDeriv_k ⊕ id`) is argued against the actual defs in the **`genF` docstring** — the WHY: the
`−Nblk_s·Wblk_s` coupling reads slot-`(s−1)` coords (`Nblk_s = readN⟨s−1⟩` via
`genBlkFlatLive_Nblk_succ`; `Wblk_s` in slot `s−1` by the stagger) so it is strictly lower / det-invisible,
`Cgen` carries no same-slot `Wblk` term, and the off-by-one gather makes the lift half `id`. Read `genF`
for the auditable trace. -/
theorem eihd_hD_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    (eihdOutGen M ha : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L)
        ∘ₗ DtotGen M ha y₀
        ∘ₗ ((eInGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))
      = stairMap (genV M) L (genF M ha y₀) (eihdcGen M ha y₀) := by
  -- THE CRUX, reduced to the per-boundary lower-triangular-with-diagonal fact via the banked
  -- reconstruction lemma. `eihdcGen := stairCouplingOf … T` with `T` the conjugated `DtotGen`, so
  -- `stairMap genV L genF eihdcGen = stairMap genV L genF (stairCouplingOf L T)`; `stairMap_eq_of_lowerTriDiag`
  -- gives `T = stairMap genV L genF (stairCouplingOf L T)` FROM `StairLowerTriDiag genV L genF T`.
  set T := ((eihdOutGen M ha : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L)
      ∘ₗ DtotGen M ha y₀
      ∘ₗ ((eInGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))) with hT
  show T = stairMap (genV M) L (genF M ha y₀) (eihdcGen M ha y₀)
  -- `eihdcGen = stairCouplingOf genV L T` (defeq: same `T`).
  have hcoupling : eihdcGen M ha y₀ = stairCouplingOf (genV M) L T := rfl
  rw [hcoupling]
  refine stairMap_eq_of_lowerTriDiag (genV M) L (genF M ha y₀) T ?_
  -- REMAINING: `StairLowerTriDiag genV L genF T` — per depth, (i) frame-diag `fst∘T∘inl = genF 0`,
  -- (ii) upper `fst∘T∘inr = 0`, (iii) tail recursion. SOUNDNESS CONFIRMED (2026-07-01, two decorrelated
  -- Codex xhigh passes): `diag(T) s = genF s` GENUINELY holds. The decisive fact is the chain-reader
  -- INDEX SHIFT `Nblk_s = readN⟨s−1⟩` (`genBlkFlatLive_Nblk_succ`: `.Nblk (k+1) = readN⟨k⟩`): the
  -- layer-s KEPT block is `Cgen(s+1) − Nblk_s·Wblk_s = schurFrameProd(readK⟨s⟩,readX⟨s⟩,readN⟨s⟩,readE⟨s⟩)
  -- − readN⟨s−1⟩·Wblk_s`. `readN⟨s−1⟩` is a slot-(s−1) frame coord and `Wblk_s` is (by the STAGGER) a
  -- slot-(s−1) lift coord, so BOTH `−N·W` coupling terms are strictly OFF-DIAGONAL (slot s−1 → s, lower)
  -- ⇒ absent from the diagonal (slot s→s) block. `Cgen` uses `Bmat/Nblk/Rmat` (NOT `Wblk`), so no
  -- same-slot `Wblk` spoiler — the ONLY same-slot frame contribution is the `Cgen(s+1)` Schur-frame
  -- fderiv = `schurFrameDeriv_s` (the L=2 `gate_schurCore_eq`/`layer0SchurMap_fderiv_collapse`). The
  -- lift diag is genuinely `id`: slot-s lift input = `Wblk_{s+1}` = the bottom rows of layer s+1's
  -- output verbatim, and the off-by-one gather (`liftGatherFinL`) routes that output back to slot s
  -- (input=output slot). So `genF s = schurFrameDeriv_s ⊕ id` IS the diagonal; the `−N·W`/`−N·δW`
  -- couplings are the head-into-tail chain feed captured by `eihdcGen` (det-invisible). NOT green-but-wrong.
  -- LEAN CONSTRUCTION (proof-engineering, math done): needs general-L analogues of the L=2
  -- `eihdT_free_eq_packStair_fderiv` (express `T w = packStairGen (fderiv BparamsLeafGen y₀ (eInGen.symm w))`),
  -- `BparamsLeaf_fderiv_layer` (per-layer fderiv via `hasFDerivAt_chainA`), and per-slot `packLayer` reads —
  -- a multi-hundred-LoC fderiv development (own tide). Reduction to this single isolated goal is banked.
  sorry

/-! ## Generic `IsCoordLE` atoms for the `eihd_hreg_gen` coordinate-permutation route

The regauge `eihdOutGen.symm ∘ₗ eInGen` is a coordinate permutation of the flat space; we certify it
via the `RouteMHregPerm.IsCoordLE` toolkit. Both `eInGen` and `packStairGen` are `≪≫ₗ`-chains of
shape-changing atoms (`piCurry`/`piCongrRight`/`piToStair`/`piProdSplit`/`sumArrowLequivProdArrow`/
`reindexLinearEquiv`/`flatMatLEGen`/`packRowSplitGen`), each of which is `IsCoordLE` for the right
`→ℝ` charts. Below are the general-`L` atom certificates + the recursive `stairChartGen` on
`StairProd genV L`; composing them by `IsCoordLE.trans`/`.symm` feeds `hreg_of_exists_funCongrLeft`.
The `sigmaChart`/`prodChart` charts pin the `→ℝ` coordinatizations of the arrow-shaped intermediates. -/

/-- **The Σ-flat chart** on a Pi-of-arrows `∀ i : ι, (κ i → ℝ)` — reshape to the flat arrow
`(Σ i, κ i) → ℝ` via `piCurry.symm` (uncurry). The canonical `→ℝ` chart for the reindex atoms. -/
def sigmaChart {ι : Type} (κ : ι → Type) :
    ((i : ι) → κ i → ℝ) ≃ₗ[ℝ] ((Σ i : ι, κ i) → ℝ) :=
  (LinearEquiv.piCurry ℝ (fun (i : ι) (_ : κ i) => ℝ)).symm

/-- `sigmaChart` reads coordinate `⟨i, j⟩` from the `i`-th arrow at `j` (`rfl`, `Sigma.uncurry`). -/
theorem sigmaChart_apply {ι : Type} (κ : ι → Type) (f : (i : ι) → κ i → ℝ) (p : Σ i : ι, κ i) :
    sigmaChart κ f p = f p.1 p.2 := rfl

/-- `sigmaChart.symm` writes the flat arrow back into the `i`-th slot (`rfl`, `Sigma.curry`). -/
theorem sigmaChart_symm_apply {ι : Type} (κ : ι → Type) (g : (Σ i : ι, κ i) → ℝ)
    (i : ι) (j : κ i) : (sigmaChart κ).symm g i j = g ⟨i, j⟩ := rfl

/-- **Atom: `piReindexOfSigma` is a coordinate permutation** — with the `sigmaChart` charts on both
Pi-of-arrows endpoints, `piReindexOfSigma d e σ` reads output `⟨i, j⟩` from input `σ ⟨i, j⟩`. -/
theorem isCoordLE_piReindexOfSigma {ι : Type} (d e : ι → ℕ)
    (σ : (Σ i : ι, Fin (d i)) ≃ (Σ i : ι, Fin (e i))) :
    IsCoordLE (sigmaChart (fun i => Fin (d i))) (sigmaChart (fun i => Fin (e i)))
      (piReindexOfSigma d e σ) := by
  refine isCoordLE_of_read σ.symm ?_
  intro f p
  -- `sigmaChart e (piReindexOfSigma d e σ (sigmaChart d).symm f) p = f (σ.symm p)`, by `Sigma.curry/uncurry`.
  rfl

/-- **Atom: `piCurry` is a coordinate permutation** — with `refl` on the flat `(Σ i, κ i) → ℝ` side and
`sigmaChart` on the curried `∀ i, κ i → ℝ` side, `piCurry` is the identity coordinate map (σ = `refl`;
`sigmaChart = piCurry.symm`, so `sigmaChart ∘ piCurry = id`). -/
theorem isCoordLE_piCurry {ι : Type} (κ : ι → Type) :
    IsCoordLE (LinearEquiv.refl ℝ ((Σ i : ι, κ i) → ℝ)) (sigmaChart κ)
      (LinearEquiv.piCurry ℝ (fun (i : ι) (_ : κ i) => ℝ)) := by
  refine isCoordLE_of_read (Equiv.refl _) ?_
  intro f p
  -- `sigmaChart (piCurry f) p = (piCurry.symm (piCurry f)) p = f p`.
  show (sigmaChart κ) ((LinearEquiv.piCurry ℝ (fun (i : ι) (_ : κ i) => ℝ)) f) p = f p
  rw [sigmaChart, LinearEquiv.symm_apply_apply]

/-- **The per-slot-charted Pi chart** on `∀ i : ι, A i` — chart each factor by `cx i : A i ≃ₗ (κ i → ℝ)`
(`piCongrRight`), then flatten to `(Σ i, κ i) → ℝ` (`sigmaChart`). The `→ℝ` chart the `piCongrRight`
atom uses on both endpoints. -/
def piArrowChart {ι : Type} {A : ι → Type} {κ : ι → Type}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
    (cx : (i : ι) → A i ≃ₗ[ℝ] (κ i → ℝ)) :
    ((i : ι) → A i) ≃ₗ[ℝ] ((Σ i : ι, κ i) → ℝ) :=
  (LinearEquiv.piCongrRight cx) ≪≫ₗ sigmaChart κ

/-- `piArrowChart` reads coordinate `⟨i, j⟩` as the `i`-th factor's chart at `j` (`rfl` after
`piCongrRight`/`sigmaChart` unfold). -/
theorem piArrowChart_apply {ι : Type} {A : ι → Type} {κ : ι → Type}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
    (cx : (i : ι) → A i ≃ₗ[ℝ] (κ i → ℝ)) (f : (i : ι) → A i) (p : Σ i : ι, κ i) :
    piArrowChart cx f p = cx p.1 (f p.1) p.2 := rfl

/-- **Atom: `piCongrRight` is a coordinate permutation** — if each `φ i` is a coordinate permutation for
charts `cx i`/`cy i`, then `piCongrRight φ` is one for `piArrowChart cx`/`piArrowChart cy`, with σ the
Σ-map `⟨i, k⟩ ↦ ⟨i, σᵢ k⟩` induced by the per-slot `σᵢ`. -/
theorem isCoordLE_piCongrRight {ι : Type} {A B : ι → Type} {α β : ι → Type}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℝ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℝ (B i)]
    (cx : (i : ι) → A i ≃ₗ[ℝ] (α i → ℝ)) (cy : (i : ι) → B i ≃ₗ[ℝ] (β i → ℝ))
    (φ : (i : ι) → A i ≃ₗ[ℝ] B i)
    (hφ : ∀ i, IsCoordLE (cx i) (cy i) (φ i)) :
    IsCoordLE (piArrowChart cx) (piArrowChart cy) (LinearEquiv.piCongrRight φ) := by
  -- collect the per-slot index permutations `σ i : β i ≃ α i` (by choice).
  choose σ hσ using hφ
  refine isCoordLE_of_read (Equiv.sigmaCongrRight σ) ?_
  intro f p
  obtain ⟨i, k⟩ := p
  -- output coord ⟨i,k⟩ = cy i (φ i (cx i.symm (f∘slot i))) k = (per-slot read) = f ⟨i, σ i k⟩.
  have hi := LinearEquiv.ext_iff.mp (hσ i) (fun j => f ⟨i, j⟩)
  have hval := congrFun hi k
  -- `hval : (cx i.symm ≪≫ φ i ≪≫ cy i) (fun j => f ⟨i,j⟩) k = funCongrLeft (σ i) (fun j => f ⟨i,j⟩) k`
  simpa only [piArrowChart, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, sigmaChart,
    LinearEquiv.piCurry_symm_apply, Sigma.uncurry, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, Equiv.sigmaCongrRight_apply] using hval

/-- **Atom: `sumArrowLequivProdArrow` is a coordinate permutation** — with `refl` on the sum-arrow side
and `prodChart refl refl` on the product side, it reads through the `Sum.inl/inr` split. σ = `id`. -/
theorem isCoordLE_sumArrow {α β : Type} :
    IsCoordLE (LinearEquiv.refl ℝ (α ⊕ β → ℝ))
      (prodChart (LinearEquiv.refl ℝ (α → ℝ)) (LinearEquiv.refl ℝ (β → ℝ)))
      (LinearEquiv.sumArrowLequivProdArrow α β ℝ ℝ) := by
  refine isCoordLE_of_read (Equiv.refl (α ⊕ β)) ?_
  intro f k
  rcases k with a | b
  · rw [prodChart_apply_inl]; rfl
  · rw [prodChart_apply_inr]; rfl

/-- **Atom: `piProdSplit` is a coordinate permutation** — `(∀ i, (α i → ℝ) × (β i → ℝ))` (charted by
`piArrowChart (prodChart refl refl)`, flat index `Σ i, α i ⊕ β i`) splits to `(∀ i, α i → ℝ) × (∀ i, β i
→ ℝ)` (charted `prodChart (sigmaChart α) (sigmaChart β)`, flat index `(Σ i, α i) ⊕ (Σ i, β i)`). σ is the
Σ/⊕ regroup `⟨i, inl a⟩ ↦ inl ⟨i,a⟩`, `⟨i, inr b⟩ ↦ inr ⟨i,b⟩`. -/
theorem isCoordLE_piProdSplit {ι : Type} (α β : ι → Type) :
    IsCoordLE (piArrowChart (fun i => prodChart (LinearEquiv.refl ℝ (α i → ℝ))
        (LinearEquiv.refl ℝ (β i → ℝ))))
      (prodChart (sigmaChart α) (sigmaChart β))
      (piProdSplit (fun i => α i → ℝ) (fun i => β i → ℝ)) := by
  -- σ : (Σ i, α i) ⊕ (Σ i, β i) ≃ Σ i, α i ⊕ β i — the Σ/⊕ regroup (`Equiv.sigmaSumDistrib.symm`).
  refine isCoordLE_of_read (Equiv.sigmaSumDistrib (fun i => α i) (fun i => β i)).symm ?_
  intro f k
  rcases k with ⟨i, a⟩ | ⟨i, b⟩
  · rw [prodChart_apply_inl]
    show ((piProdSplit (fun i => α i → ℝ) (fun i => β i → ℝ))
        ((piArrowChart (fun i => prodChart (LinearEquiv.refl ℝ (α i → ℝ))
          (LinearEquiv.refl ℝ (β i → ℝ)))).symm f)).1 i a = _
    rfl
  · rw [prodChart_apply_inr]
    show ((piProdSplit (fun i => α i → ℝ) (fun i => β i → ℝ))
        ((piArrowChart (fun i => prodChart (LinearEquiv.refl ℝ (α i → ℝ))
          (LinearEquiv.refl ℝ (β i → ℝ)))).symm f)).2 i b = _
    rfl

/-! ### The recursive staircase chart + the `piToStair` atom -/

/-- **The recursive `→ℝ` chart on `StairProd V n`**, from a per-slot chart family `cV k : V k ≃ₗ (κ k
→ ℝ)`. At `n = 0` it is `punitChart` (`PUnit ≃ Fin 0 → ℝ`); at `n+1`, `prodChart (cV 0) (recurse on the
tail)`. The `stairFlatIdx` index type accumulates the head/tail `⊕`. -/
def stairFlatIdx (κ : ℕ → Type) : ℕ → Type
  | 0 => Fin 0
  | (n + 1) => κ 0 ⊕ stairFlatIdx (fun k => κ (k + 1)) n

/-- The recursive staircase chart `StairProd V n ≃ₗ (stairFlatIdx κ n → ℝ)`. -/
def stairChartGen (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    {κ : ℕ → Type} (cV : (k : ℕ) → V k ≃ₗ[ℝ] (κ k → ℝ)) :
    (n : ℕ) → StairProd V n ≃ₗ[ℝ] (stairFlatIdx κ n → ℝ)
  | 0 => punitChart
  | (n + 1) =>
    prodChart (cV 0) (stairChartGen (fun k => V (k + 1)) (fun k => cV (k + 1)) n)

/-- **`headTailFinPi` is a coordinate permutation** — the `Fin.cons` head/tail split, between
`piArrowChart cV` (flat index `Σ k:Fin (n+1), κ k.val`) and `prodChart (cV 0) (piArrowChart (cV∘succ))`
(flat index `κ 0 ⊕ Σ i:Fin n, κ (i+1)`). σ is the `Fin.cases` regroup. -/
theorem isCoordLE_headTailFinPi (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    {κ : ℕ → Type} (cV : (k : ℕ) → V k ≃ₗ[ℝ] (κ k → ℝ)) (n : ℕ) :
    IsCoordLE (piArrowChart (fun k : Fin (n + 1) => cV k.val))
      (prodChart (cV 0) (piArrowChart (fun i : Fin n => cV (i.val + 1))))
      (headTailFinPi V n) := by
  -- σ : (κ 0 ⊕ Σ i:Fin n, κ (i+1)) ≃ Σ k:Fin (n+1), κ k.val — head at 0, tail at succ.
  refine isCoordLE_of_read
    { toFun := fun s => match s with
        | Sum.inl a => ⟨0, a⟩
        | Sum.inr ⟨i, a⟩ => ⟨i.succ, a⟩
      invFun := fun p => Fin.cases (fun a => Sum.inl a) (fun i a => Sum.inr ⟨i, a⟩) p.1 p.2
      left_inv := by rintro (a | ⟨i, a⟩) <;> simp [Fin.cases_succ]
      right_inv := by
        rintro ⟨k, a⟩
        refine Fin.cases ?_ (fun i => ?_) k a
        · intro a; rfl
        · intro a; simp [Fin.cases_succ] } ?_
  intro f k
  rcases k with a | ⟨i, a⟩
  · rw [prodChart_apply_inl]
    show (cV 0) ((piArrowChart (fun k : Fin (n + 1) => cV k.val)).symm f 0) a = f ⟨0, a⟩
    show (cV 0) ((cV 0).symm (fun j => f ⟨0, j⟩)) a = f ⟨0, a⟩
    rw [LinearEquiv.apply_symm_apply]
  · rw [prodChart_apply_inr]
    show (piArrowChart (fun i : Fin n => cV (i.val + 1)))
        ((headTailFinPi V n) ((piArrowChart (fun k : Fin (n + 1) => cV k.val)).symm f)).2 ⟨i, a⟩ = _
    show (cV (i.val + 1)) ((cV (i.val + 1)).symm (fun j => f ⟨i.succ, j⟩)) a = f ⟨i.succ, a⟩
    rw [LinearEquiv.apply_symm_apply]

/-- **Atom: `piToStair` is a coordinate permutation** — recursion on `n`. `piToStair V (n+1) =
headTailFinPi ≪≫ (refl.prodCongr (piToStair tail))`; the head factor is `IsCoordLE.refl`, the tail is the
IH, and `headTailFinPi` is `isCoordLE_headTailFinPi`, composed by `IsCoordLE.trans`. The charts are
`piArrowChart cV` (in) and `stairChartGen cV` (out). -/
theorem isCoordLE_piToStair (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    {κ : ℕ → Type} (cV : (k : ℕ) → V k ≃ₗ[ℝ] (κ k → ℝ)) :
    (n : ℕ) → IsCoordLE (piArrowChart (fun k : Fin n => cV k.val)) (stairChartGen V cV n)
      (piToStair V n)
  | 0 => by
      -- both index types (`stairFlatIdx κ 0 = Fin 0` and `Σ i:Fin 0, κ i.val`) are empty; σ = the
      -- unique equiv between empty types (`stairFlatIdx κ 0` is defeq `Fin 0`).
      haveI : IsEmpty (stairFlatIdx κ 0) := (inferInstance : IsEmpty (Fin 0))
      refine ⟨Equiv.equivOfIsEmpty (stairFlatIdx κ 0) (Σ i : Fin 0, κ i.val), ?_⟩
      ext f i; exact i.elim0
  | (n + 1) => by
      -- `piToStair V (n+1) = headTailFinPi ≪≫ (refl.prodCongr (piToStair tail n))`.
      have hstep : piToStair V (n + 1)
          = (headTailFinPi V n) ≪≫ₗ
            ((LinearEquiv.refl ℝ (V 0)).prodCongr (piToStair (fun k => V (k + 1)) n)) := rfl
      rw [hstep]
      have hhead : IsCoordLE (cV 0) (cV 0) (LinearEquiv.refl ℝ (V 0)) := IsCoordLE.refl (cV 0)
      have htail := isCoordLE_piToStair (fun k => V (k + 1)) (fun k => cV (k + 1)) n
      have hprod := isCoordLE_prodCongr hhead htail
      -- `stairChartGen V cV (n+1) = prodChart (cV 0) (stairChartGen tail (n))` (rfl).
      exact (isCoordLE_headTailFinPi V cV n).trans hprod

/-! ### The per-slot matrix atoms for `packStairGen` (steps 0/1/2) -/

/-- **Atom: a `matChart`-charted matrix reshape reading each output entry from a single input entry is a
coordinate permutation.** For `e : Matrix (Fin a)(Fin b) ≃ₗ Matrix (Fin a')(Fin b')`, if `(e Mat) i j`
reads `Mat` at `(τ (i,j)).1 (τ (i,j)).2` for a bijection `τ : Fin a' × Fin b' ≃ Fin a × Fin b`, then
`IsCoordLE (matChart a b) (matChart a' b') e` (the σ is the `finProdFinEquiv`-conjugate of τ). -/
theorem isCoordLE_matReshape (a b a' b' : ℕ)
    (e : Matrix (Fin a) (Fin b) ℝ ≃ₗ[ℝ] Matrix (Fin a') (Fin b') ℝ)
    (τ : (Fin a' × Fin b') ≃ (Fin a × Fin b))
    (hread : ∀ (Mat : Matrix (Fin a) (Fin b) ℝ) (i : Fin a') (j : Fin b'),
      e Mat i j = Mat (τ (i, j)).1 (τ (i, j)).2) :
    IsCoordLE (matChart a b) (matChart a' b') e := by
  refine isCoordLE_of_read
    ((finProdFinEquiv (m := a') (n := b')).symm.trans (τ.trans finProdFinEquiv)) ?_
  intro f m
  -- output flat coord m ↦ matrix entry (finProdFinEquiv.symm m) ↦ read via τ ↦ input flat coord.
  rw [matChart_apply a' b' (e ((matChart a b).symm f)) m, hread]
  -- `(matChart a b).symm f`: entry `(p,q)` is `f (finProdFinEquiv (p,q))`.
  have hsym : ∀ (p : Fin a) (q : Fin b), (matChart a b).symm f p q = f (finProdFinEquiv (p, q)) := by
    intro p q
    have : matChart a b ((matChart a b).symm f) = f := (matChart a b).apply_symm_apply f
    have h2 := matChart_apply a b ((matChart a b).symm f) (finProdFinEquiv (p, q))
    rw [this] at h2
    simpa only [Equiv.symm_apply_apply] using h2.symm
  rw [hsym]
  rfl

/-- **Atom: `flatMatLEGen.symm` (matrix → flat arrow) is a coordinate permutation** — chart the matrix
side by `matChart a b`, the arrow side by `refl`; σ = `id` (`matChart = flatMatLEGen.symm`). -/
theorem isCoordLE_flatMatLEGen_symm (a b : ℕ) :
    IsCoordLE (matChart a b) (LinearEquiv.refl ℝ (Fin (a * b) → ℝ)) (flatMatLEGen a b).symm := by
  refine isCoordLE_of_read (Equiv.refl (Fin (a * b))) ?_
  intro f m
  -- `matChart = (flatMatLE).symm = (flatMatLEGen).symm`; `flatMatLEGen.symm ((matChart).symm f) = f`.
  show (flatMatLEGen a b).symm ((matChart a b).symm f) m = f m
  rw [show (matChart a b).symm = flatMatLEGen a b from by
      rw [matChart, LinearEquiv.symm_symm]; rfl]
  rw [LinearEquiv.symm_apply_apply]

/-- The kept-block read of `packRowSplitGen s` — `(packRowSplitGen s Mat).1 i j` reads row
`finSumFinEquiv (inl i)` (recast by `genWidthEq`) at column `j`. -/
theorem packRowSplitGen_read_kept (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (s : Fin L)
    (Mat : Matrix (Fin (Wext M s.val)) (Fin (Wext M (s.val + 1))) ℝ)
    (i : Fin (Text M (tach M) (s.val + 1))) (j : Fin (Wext M (s.val + 1))) :
    (packRowSplitGen M ha s Mat).1 i j
      = Mat (Fin.cast (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
          (finSumFinEquiv (Sum.inl i))) j := by
  show ((Matrix.ofLinearEquiv ℝ) ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ _)
      ((Matrix.ofLinearEquiv ℝ).symm
        ((Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv.symm (Equiv.refl _))
          ((Matrix.reindexLinearEquiv ℝ ℝ
              (finCongr (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt).symm)
              (Equiv.refl _)) Mat)))).1) i j = _
  simp only [Matrix.coe_ofLinearEquiv, Matrix.of_apply,
    LinearEquiv.sumArrowLequivProdArrow_apply_fst, Matrix.coe_ofLinearEquiv_symm,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Matrix.submatrix_apply, Matrix.of_symm_apply,
    finCongr_symm, Equiv.symm_symm, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
    finCongr_apply]

/-- The lift-block read of `packRowSplitGen s` — `(packRowSplitGen s Mat).2 i j` reads row
`finSumFinEquiv (inr i)` (recast by `genWidthEq`) at column `j`. -/
theorem packRowSplitGen_read_lift (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (s : Fin L)
    (Mat : Matrix (Fin (Wext M s.val)) (Fin (Wext M (s.val + 1))) ℝ)
    (i : Fin (Wext M s.val - Text M (tach M) (s.val + 1))) (j : Fin (Wext M (s.val + 1))) :
    (packRowSplitGen M ha s Mat).2 i j
      = Mat (Fin.cast (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
          (finSumFinEquiv (Sum.inr i))) j := by
  show ((Matrix.ofLinearEquiv ℝ) ((LinearEquiv.sumArrowLequivProdArrow _ _ ℝ _)
      ((Matrix.ofLinearEquiv ℝ).symm
        ((Matrix.reindexLinearEquiv ℝ ℝ finSumFinEquiv.symm (Equiv.refl _))
          ((Matrix.reindexLinearEquiv ℝ ℝ
              (finCongr (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt).symm)
              (Equiv.refl _)) Mat)))).2) i j = _
  simp only [Matrix.coe_ofLinearEquiv, Matrix.of_apply,
    LinearEquiv.sumArrowLequivProdArrow_apply_snd, Matrix.coe_ofLinearEquiv_symm,
    Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_submatrix,
    Matrix.submatrix_apply, Matrix.of_symm_apply,
    finCongr_symm, Equiv.symm_symm, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply,
    finCongr_apply]

/-- **Atom: `packRowSplitGen s` is a coordinate permutation** — chart the input matrix by `matChart`,
the output `(kept × lift)` pair by `prodChart (matChart …) (matChart …)`. The read routes each output
row/col through `finSumFinEquiv`/`genWidthEq`; σ is the induced flat-index regroup. -/
theorem isCoordLE_packRowSplitGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (s : Fin L) :
    IsCoordLE (matChart (Wext M s.val) (Wext M (s.val + 1)))
      (prodChart (matChart (Text M (tach M) (s.val + 1)) (Wext M (s.val + 1)))
        (matChart (Wext M s.val - Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))))
      (packRowSplitGen M ha s) := by
  -- σ : (Fin (Text·Wext) ⊕ Fin ((Wext-Text)·Wext)) ≃ Fin (Wext s · Wext(s+1)) — via matChart/finSum.
  -- σ : (Fin(T·W) ⊕ Fin((Wₛ−T)·W)) ≃ Fin(Wₛ·W): unpack both summands, `sumProdDistrib.symm` to
  -- `(Fin T ⊕ Fin(Wₛ−T)) × Fin W`, glue rows by `finSumFinEquiv`+`genWidthEq`, repack.
  let s1 : (Fin (Text M (tach M) (s.val + 1) * Wext M (s.val + 1)) ⊕
      Fin ((Wext M s.val - Text M (tach M) (s.val + 1)) * Wext M (s.val + 1))) ≃
      ((Fin (Text M (tach M) (s.val + 1)) × Fin (Wext M (s.val + 1))) ⊕
        (Fin (Wext M s.val - Text M (tach M) (s.val + 1)) × Fin (Wext M (s.val + 1)))) :=
    Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm
  let s2 := (Equiv.sumProdDistrib (Fin (Text M (tach M) (s.val + 1)))
      (Fin (Wext M s.val - Text M (tach M) (s.val + 1))) (Fin (Wext M (s.val + 1)))).symm
  let s3 := Equiv.prodCongr (finSumFinEquiv (m := Text M (tach M) (s.val + 1))
      (n := Wext M s.val - Text M (tach M) (s.val + 1))) (Equiv.refl (Fin (Wext M (s.val + 1))))
  let s4 := Equiv.prodCongr (finCongr (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt))
      (Equiv.refl (Fin (Wext M (s.val + 1))))
  let s5 := finProdFinEquiv (m := Wext M s.val) (n := Wext M (s.val + 1))
  refine isCoordLE_of_read (s1.trans (s2.trans (s3.trans (s4.trans s5)))) ?_
  intro f k
  rcases k with a | b
  · rw [prodChart_apply_inl, matChart_apply, packRowSplitGen_read_kept]
    have hsym : ∀ (p : Fin (Wext M s.val)) (q : Fin (Wext M (s.val + 1))),
        (matChart (Wext M s.val) (Wext M (s.val + 1))).symm f p q = f (finProdFinEquiv (p, q)) := by
      intro p q
      have h2 := matChart_apply (Wext M s.val) (Wext M (s.val + 1))
        ((matChart (Wext M s.val) (Wext M (s.val + 1))).symm f) (finProdFinEquiv (p, q))
      rw [(matChart (Wext M s.val) (Wext M (s.val + 1))).apply_symm_apply f] at h2
      simpa only [Equiv.symm_apply_apply] using h2.symm
    rw [hsym]
    simp only [s1, s2, s3, s4, s5, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.prodCongr_apply, Prod.map, Equiv.sumProdDistrib_symm_apply_left,
      finSumFinEquiv_apply_left, finCongr_apply, Equiv.refl_apply]
  · rw [prodChart_apply_inr, matChart_apply, packRowSplitGen_read_lift]
    have hsym : ∀ (p : Fin (Wext M s.val)) (q : Fin (Wext M (s.val + 1))),
        (matChart (Wext M s.val) (Wext M (s.val + 1))).symm f p q = f (finProdFinEquiv (p, q)) := by
      intro p q
      have h2 := matChart_apply (Wext M s.val) (Wext M (s.val + 1))
        ((matChart (Wext M s.val) (Wext M (s.val + 1))).symm f) (finProdFinEquiv (p, q))
      rw [(matChart (Wext M s.val) (Wext M (s.val + 1))).apply_symm_apply f] at h2
      simpa only [Equiv.symm_apply_apply] using h2.symm
    rw [hsym]
    simp only [s1, s2, s3, s4, s5, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.prodCongr_apply, Prod.map, Equiv.sumProdDistrib_symm_apply_right,
      finSumFinEquiv_apply_right, finCongr_apply, Equiv.refl_apply]

/-- **Atom: the step-0 width-recast `reindexLinearEquiv (finCongr h1) (finCongr h2)`** is a coordinate
permutation — chart both matrix sides by `matChart`, τ = `(finCongr h1.symm) × (finCongr h2.symm)`. -/
theorem isCoordLE_matReindexFinCongr {a b a' b' : ℕ} (h1 : a = a') (h2 : b = b') :
    IsCoordLE (matChart a b) (matChart a' b')
      (Matrix.reindexLinearEquiv ℝ ℝ (finCongr h1) (finCongr h2)) := by
  refine isCoordLE_matReshape a b a' b' _
    (Equiv.prodCongr (finCongr h1.symm) (finCongr h2.symm)) ?_
  intro Mat i j
  rw [Matrix.reindexLinearEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [finCongr_symm, Equiv.prodCongr_apply, Prod.map, finCongr_apply]

/-! ### The `genV` chart family + the `eInGen`/`packStairGen` `IsCoordLE` certificates -/

/-- The per-slot `→ℝ` chart on `genV M k = (Fin (schurDim k) → ℝ) × (Fin (liftDim k) → ℝ)` — the
`prodChart` of the two `refl` arrow charts, to `(Fin (schurDim k) ⊕ Fin (liftDim k)) → ℝ`. -/
def genVChart (M : Fin (L + 1) → ℕ) (k : ℕ) :
    genV M k ≃ₗ[ℝ] ((Fin (schurDim M (tDesc M (tach M)) k) ⊕ Fin (liftDim M (tDesc M (tach M)) k)) → ℝ) :=
  prodChart (LinearEquiv.refl ℝ (Fin (schurDim M (tDesc M (tach M)) k) → ℝ))
    (LinearEquiv.refl ℝ (Fin (liftDim M (tDesc M (tach M)) k) → ℝ))

/-- **`eInGen` is a coordinate permutation** — `IsCoordLE refl (stairChartGen genV genVChart L) (eInGen)`.
Assembles the four `eInGen` atoms (`funCongrLeft chartIdxEquiv.symm`, `piCurry`, `piCongrRight
sumArrow`, `piToStair`) by `IsCoordLE.trans`. -/
theorem isCoordLE_eInGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    IsCoordLE (LinearEquiv.refl ℝ (Fin (routeMAmbient M) → ℝ))
      (stairChartGen (genV M) (genVChart M) L) (eInGen M ha) := by
  -- eInGen = A ≪≫ B ≪≫ C ≪≫ D (funCongrLeft, piCurry, piCongrRight sumArrow, piToStair).
  set κ : Fin L → Type := fun k => Fin (schurDim M (tDesc M (tach M)) k.val) ⊕
      Fin (liftDim M (tDesc M (tach M)) k.val) with hκ
  -- A : IsCoordLE refl refl (funCongrLeft chartIdxEquiv.symm), σ = chartIdxEquiv.symm.
  have hA : IsCoordLE (LinearEquiv.refl ℝ (Fin (routeMAmbient M) → ℝ))
      (LinearEquiv.refl ℝ (ChartIdx M (tDesc M (tach M)) → ℝ))
      (LinearEquiv.funCongrLeft ℝ ℝ (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm) :=
    isCoordLE_funCongrLeft (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL)
  -- B : IsCoordLE refl (sigmaChart κ) piCurry.
  have hB : IsCoordLE (LinearEquiv.refl ℝ ((Σ k : Fin L, κ k) → ℝ)) (sigmaChart κ)
      (LinearEquiv.piCurry ℝ (fun (k : Fin L) (_ : κ k) => ℝ)) := isCoordLE_piCurry κ
  -- C : IsCoordLE (piArrowChart refl-per-slot) (piArrowChart genVChart) (piCongrRight sumArrow).
  have hC : IsCoordLE (piArrowChart (fun k : Fin L => LinearEquiv.refl ℝ (κ k → ℝ)))
      (piArrowChart (fun k : Fin L => genVChart M k.val))
      (LinearEquiv.piCongrRight (fun k : Fin L =>
        LinearEquiv.sumArrowLequivProdArrow (Fin (schurDim M (tDesc M (tach M)) k.val))
          (Fin (liftDim M (tDesc M (tach M)) k.val)) ℝ ℝ)) := by
    refine isCoordLE_piCongrRight _ _ _ (fun k => ?_)
    -- each slot: sumArrowLequivProdArrow, charts refl / genVChart (= prodChart refl refl).
    rw [genVChart]
    exact isCoordLE_sumArrow
  -- D : IsCoordLE (piArrowChart genVChart) (stairChartGen genV genVChart L) piToStair.
  have hD : IsCoordLE (piArrowChart (fun k : Fin L => genVChart M k.val))
      (stairChartGen (genV M) (genVChart M) L) (piToStair (genV M) L) :=
    isCoordLE_piToStair (genV M) (genVChart M) L
  -- eInGen = A ≪≫ B ≪≫ C ≪≫ D.
  have heq : eInGen M ha
      = (LinearEquiv.funCongrLeft ℝ ℝ (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm)
          ≪≫ₗ (LinearEquiv.piCurry ℝ (fun (k : Fin L) (_ : κ k) => ℝ))
          ≪≫ₗ (LinearEquiv.piCongrRight (fun k : Fin L =>
              LinearEquiv.sumArrowLequivProdArrow (Fin (schurDim M (tDesc M (tach M)) k.val))
                (Fin (liftDim M (tDesc M (tach M)) k.val)) ℝ ℝ))
          ≪≫ₗ piToStair (genV M) L := rfl
  rw [heq]
  exact hA.trans (hB.trans (hC.trans hD))

/-- The `Params M` `→ℝ` chart used for `packStairGen` — the per-layer `matChart`, flattened. -/
def paramsMatChart (M : Fin (L + 1) → ℕ) :
    Params M ≃ₗ[ℝ] ((Σ s : Fin L, Fin (M s.castSucc * M s.succ)) → ℝ) :=
  piArrowChart (fun s : Fin L => matChart (M s.castSucc) (M s.succ))

/-- **`packStairGen` is a coordinate permutation** — `IsCoordLE (paramsMatChart) (stairChartGen genV
genVChart L) (packStairGen)`. Threads the seven `packStairGen` steps through the per-slot matrix atoms
+ the `piProdSplit`/`piReindexOfSigma`/`piToStair` atoms by `IsCoordLE.trans`. -/
theorem isCoordLE_packStairGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L) :
    IsCoordLE (paramsMatChart M) (stairChartGen (genV M) (genVChart M) L)
      (packStairGen M ha hL) := by
  -- abbreviations for the per-slot flat dims / charts along the chain.
  set schD : Fin L → ℕ := fun s => schurDim M (tDesc M (tach M)) s.val with hschD
  set lftD : Fin L → ℕ := fun s => liftDim M (tDesc M (tach M)) s.val with hlftD
  set lblk : Fin L → ℕ := fun s => (Wext M s.val - Text M (tach M) (s.val + 1)) * Wext M (s.val + 1)
    with hlblk
  -- S0: piCongrRight (matReindexFinCongr) : paramsMatChart ⟶ piArrowChart (matChart (Wext ..)).
  have hS0 : IsCoordLE (paramsMatChart M)
      (piArrowChart (fun s : Fin L => matChart (Wext M s.val) (Wext M (s.val + 1))))
      (LinearEquiv.piCongrRight (fun s : Fin L =>
        Matrix.reindexLinearEquiv ℝ ℝ
          (finCongr (show M s.castSucc = Wext M s.val by rw [Wext_apply M s.val (by omega)]; rfl))
          (finCongr (show M s.succ = Wext M (s.val + 1) by
            rw [Wext_apply M (s.val + 1) (by omega)]; rfl)))) :=
    isCoordLE_piCongrRight _ _ _ (fun s => isCoordLE_matReindexFinCongr _ _)
  -- S1: piCongrRight packRowSplitGen : ⟶ piArrowChart (prodChart matChart matChart).
  have hS1 : IsCoordLE (piArrowChart (fun s : Fin L => matChart (Wext M s.val) (Wext M (s.val + 1))))
      (piArrowChart (fun s : Fin L =>
        prodChart (matChart (Text M (tach M) (s.val + 1)) (Wext M (s.val + 1)))
          (matChart (Wext M s.val - Text M (tach M) (s.val + 1)) (Wext M (s.val + 1)))))
      (LinearEquiv.piCongrRight (fun s : Fin L => packRowSplitGen M ha s)) :=
    isCoordLE_piCongrRight _ _ _ (fun s => isCoordLE_packRowSplitGen M ha s)
  -- S2: piCongrRight (flatMatLEGen.symm × flatMatLEGen.symm) : ⟶ piArrowChart (prodChart refl refl).
  have hS2 : IsCoordLE (piArrowChart (fun s : Fin L =>
        prodChart (matChart (Text M (tach M) (s.val + 1)) (Wext M (s.val + 1)))
          (matChart (Wext M s.val - Text M (tach M) (s.val + 1)) (Wext M (s.val + 1)))))
      (piArrowChart (fun s : Fin L =>
        prodChart (LinearEquiv.refl ℝ (Fin (schD s) → ℝ)) (LinearEquiv.refl ℝ (Fin (lblk s) → ℝ))))
      (LinearEquiv.piCongrRight (fun s : Fin L =>
        (flatMatLEGen (Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))).symm.prodCongr
          (flatMatLEGen (Wext M s.val - Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))).symm)) := by
    refine isCoordLE_piCongrRight _ _ _ (fun s => ?_)
    exact isCoordLE_prodCongr (isCoordLE_flatMatLEGen_symm _ _) (isCoordLE_flatMatLEGen_symm _ _)
  -- S3: piProdSplit : ⟶ prodChart (sigmaChart schD) (sigmaChart lblk).
  have hS3 : IsCoordLE
      (piArrowChart (fun s : Fin L =>
        prodChart (LinearEquiv.refl ℝ (Fin (schD s) → ℝ)) (LinearEquiv.refl ℝ (Fin (lblk s) → ℝ))))
      (prodChart (sigmaChart (fun s : Fin L => Fin (schD s)))
        (sigmaChart (fun s : Fin L => Fin (lblk s))))
      (piProdSplit (fun s : Fin L => Fin (schD s) → ℝ) (fun s : Fin L => Fin (lblk s) → ℝ)) :=
    isCoordLE_piProdSplit (fun s : Fin L => Fin (schD s)) (fun s : Fin L => Fin (lblk s))
  -- S4: refl.prodCongr (piReindexOfSigma liftGatherFinL) : ⟶ prodChart (sigmaChart schD) (sigmaChart lftD).
  have hS4 : IsCoordLE
      (prodChart (sigmaChart (fun s : Fin L => Fin (schD s)))
        (sigmaChart (fun s : Fin L => Fin (lblk s))))
      (prodChart (sigmaChart (fun s : Fin L => Fin (schD s)))
        (sigmaChart (fun s : Fin L => Fin (lftD s))))
      ((LinearEquiv.refl ℝ ((s : Fin L) → Fin (schD s) → ℝ)).prodCongr
        (piReindexOfSigma (fun s : Fin L => lblk s) (fun s : Fin L => lftD s)
          (liftGatherFinL M ha hL))) :=
    isCoordLE_prodCongr (IsCoordLE.refl _)
      (isCoordLE_piReindexOfSigma (fun s : Fin L => lblk s) (fun s : Fin L => lftD s)
        (liftGatherFinL M ha hL))
  -- S5: piProdSplit.symm : ⟶ piArrowChart (prodChart refl refl) = piArrowChart genVChart.
  have hS5 : IsCoordLE
      (prodChart (sigmaChart (fun s : Fin L => Fin (schD s)))
        (sigmaChart (fun s : Fin L => Fin (lftD s))))
      (piArrowChart (fun s : Fin L =>
        prodChart (LinearEquiv.refl ℝ (Fin (schD s) → ℝ)) (LinearEquiv.refl ℝ (Fin (lftD s) → ℝ))))
      (piProdSplit (fun s : Fin L => Fin (schD s) → ℝ) (fun s : Fin L => Fin (lftD s) → ℝ)).symm :=
    (isCoordLE_piProdSplit (fun s : Fin L => Fin (schD s)) (fun s : Fin L => Fin (lftD s))).symm
  -- S6: piToStair : ⟶ stairChartGen genV genVChart L.
  have hS6 : IsCoordLE (piArrowChart (fun s : Fin L => genVChart M s.val))
      (stairChartGen (genV M) (genVChart M) L) (piToStair (genV M) L) :=
    isCoordLE_piToStair (genV M) (genVChart M) L
  -- packStairGen = S0 ≪≫ S1 ≪≫ S2 ≪≫ S3 ≪≫ S4 ≪≫ S5 ≪≫ S6.
  have heq : packStairGen M ha hL
      = (LinearEquiv.piCongrRight (fun s : Fin L =>
          Matrix.reindexLinearEquiv ℝ ℝ
            (finCongr (show M s.castSucc = Wext M s.val by rw [Wext_apply M s.val (by omega)]; rfl))
            (finCongr (show M s.succ = Wext M (s.val + 1) by
              rw [Wext_apply M (s.val + 1) (by omega)]; rfl))))
        ≪≫ₗ (LinearEquiv.piCongrRight (fun s : Fin L => packRowSplitGen M ha s))
        ≪≫ₗ (LinearEquiv.piCongrRight (fun s : Fin L =>
            (flatMatLEGen (Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))).symm.prodCongr
              (flatMatLEGen (Wext M s.val - Text M (tach M) (s.val + 1)) (Wext M (s.val + 1))).symm))
        ≪≫ₗ (piProdSplit (fun s : Fin L => Fin (Text M (tach M) (s.val + 1) * Wext M (s.val + 1)) → ℝ)
            (fun s : Fin L => Fin ((Wext M s.val - Text M (tach M) (s.val + 1)) * Wext M (s.val + 1)) → ℝ))
        ≪≫ₗ ((LinearEquiv.refl ℝ ((s : Fin L) →
              Fin (Text M (tach M) (s.val + 1) * Wext M (s.val + 1)) → ℝ)).prodCongr
            (piReindexOfSigma
              (fun k : Fin L => (Wext M k.val - Text M (tach M) (k.val + 1)) * Wext M (k.val + 1))
              (fun k : Fin L => liftDim M (tDesc M (tach M)) k.val)
              (liftGatherFinL M ha hL)))
        ≪≫ₗ (piProdSplit (fun s : Fin L => Fin (schurDim M (tDesc M (tach M)) s.val) → ℝ)
            (fun s : Fin L => Fin (liftDim M (tDesc M (tach M)) s.val) → ℝ)).symm
        ≪≫ₗ (piToStair (genV M) L) := rfl
  rw [heq]
  exact hS0.trans (hS1.trans (hS2.trans (hS3.trans (hS4.trans (hS5.trans hS6)))))

/-- The `FlatIdx ≃ Σ s, Fin (M s.cast · M s.succ)` regroup — combine each `(⟨s,i⟩, j)` into `⟨s,
finProdFinEquiv (i,j)⟩`. Bridges `paramsEquivFlatLinear`'s `FlatIdx` layout with `paramsMatChart`'s
per-layer flat layout. -/
def flatIdxRegroup (M : Fin (L + 1) → ℕ) :
    FlatIdx M ≃ (Σ s : Fin L, Fin (M s.castSucc * M s.succ)) where
  toFun := fun q => ⟨q.1.1, finProdFinEquiv (q.1.2, q.2)⟩
  invFun := fun p => ⟨⟨p.1, (finProdFinEquiv.symm p.2).1⟩, (finProdFinEquiv.symm p.2).2⟩
  left_inv := fun q => by
    obtain ⟨⟨s, i⟩, j⟩ := q
    show (⟨⟨s, (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1⟩,
        (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2⟩ : FlatIdx M) = ⟨⟨s, i⟩, j⟩
    rw [Equiv.symm_apply_apply]
  right_inv := fun p => by
    obtain ⟨s, m⟩ := p
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

/-- **Atom: `paramsEquivFlatLinear` is a coordinate permutation** — `IsCoordLE (paramsMatChart M) refl
(paramsEquivFlatLinear M)`. Both read Params layer `s` entry `(i,j)`; σ = `equivFin FlatIdx ≪≫
flatIdxRegroup` (output flat coord `n` reads Params layer `s = (regroup (equivFin.symm n)).1` at the
`finProdFinEquiv`-unpacked entry). -/
theorem isCoordLE_paramsEquivFlatLinear (M : Fin (L + 1) → ℕ) :
    IsCoordLE (paramsMatChart M) (LinearEquiv.refl ℝ (Fin (flatDim M) → ℝ))
      (paramsEquivFlatLinear M) := by
  refine isCoordLE_of_read
    ((Fintype.equivFin (FlatIdx M)).symm.trans (flatIdxRegroup M)) ?_
  intro f n
  -- LHS: `paramsEquivFlatLinear (paramsMatChart.symm f) n`; RHS: `f (σ n)`.
  show (paramsEquivFlatLinear M) ((paramsMatChart M).symm f) n = _
  -- `paramsEquivFlatLinear P n = P s i j` at `⟨⟨s,i⟩,j⟩ = (equivFin FlatIdx).symm n` (defeq via the
  -- two `piCurry.symm` uncurryings + `funCongrLeft`); `(paramsMatChart.symm f) s i j = f ⟨s,
  -- finProdFinEquiv (i,j)⟩` (defeq via `sigmaChart.symm` + `matChart.symm = flatMatLEGen`).
  rw [show (paramsEquivFlatLinear M) ((paramsMatChart M).symm f) n
      = ((paramsMatChart M).symm f) ((Fintype.equivFin (FlatIdx M)).symm n).1.1
          ((Fintype.equivFin (FlatIdx M)).symm n).1.2 ((Fintype.equivFin (FlatIdx M)).symm n).2
    from rfl]
  -- unpack the Params slot read through `paramsMatChart.symm` = `piCongrRight matChart.symm ∘ sigmaChart.symm`.
  set q := (Fintype.equivFin (FlatIdx M)).symm n with hq
  -- `(sigmaChart κ).symm f q.1.1 = fun m => f ⟨q.1.1, m⟩` (Sigma.curry); `matChart.symm = flatMatLEGen`.
  show (matChart (M q.1.1.castSucc) (M q.1.1.succ)).symm
      ((sigmaChart (fun s : Fin L => Fin (M s.castSucc * M s.succ))).symm f q.1.1) q.1.2 q.2 = _
  rw [show ((sigmaChart (fun s : Fin L => Fin (M s.castSucc * M s.succ))).symm f q.1.1)
      = (fun m => f ⟨q.1.1, m⟩) from rfl]
  rw [show (matChart (M q.1.1.castSucc) (M q.1.1.succ)).symm
      = flatMatLEGen (M q.1.1.castSucc) (M q.1.1.succ) from by rw [matChart, LinearEquiv.symm_symm]; rfl]
  -- `flatMatLEGen a b g i j = g (finProdFinEquiv (i,j))` — the flat entry read.
  rw [show (flatMatLEGen (M q.1.1.castSucc) (M q.1.1.succ)) (fun m => f ⟨q.1.1, m⟩) q.1.2 q.2
      = (fun m => f ⟨q.1.1, m⟩) (finProdFinEquiv (q.1.2, q.2)) from
    flatMatLE_apply (M q.1.1.castSucc) (M q.1.1.succ) (fun m => f ⟨q.1.1, m⟩) q.1.2 q.2]
  rfl

/-- **The regauge abs-det-`1`** `eihd_hreg_gen` — `|det (eihdOutGen.symm ∘ eInGen)| = 1`. The
general-`L` lift of `RouteMHregPerm.eihd_hreg` (a slot-reindex is measure/det-1). LOAD-BEARING
RESIDUAL. -/
theorem eihd_hreg_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    |LinearMap.det
        (((eihdOutGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))
        ∘ₗ ((eInGen M ha) : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L))| = 1 := by
  -- The regauge `eihdOutGen.symm ∘ eInGen` is a coordinate permutation `funCongrLeft σ` of the flat
  -- space; `|det| = 1` via `hreg_of_exists_funCongrLeft`, assembled from the three `IsCoordLE`
  -- certificates `isCoordLE_eInGen`/`isCoordLE_packStairGen`/`isCoordLE_paramsEquivFlatLinear` by
  -- `.trans`/`.symm` (`eihdOutGen = paramsEquivFlatLinear.symm ≪≫ packStairGen`). Lift of `eihd_hreg`.
  refine hreg_of_exists_funCongrLeft (genV M) (eInGen M ha) (eihdOutGen M ha) ?_
  -- IsCoordLE refl refl (eInGen ≪≫ eihdOutGen.symm) ⟹ ∃ σ, eihdOutGen.symm ∘ₗ eInGen = funCongrLeft σ.
  have hcoord : IsCoordLE (LinearEquiv.refl ℝ (Fin (routeMAmbient M) → ℝ))
      (LinearEquiv.refl ℝ (Fin (routeMAmbient M) → ℝ)) (eInGen M ha ≪≫ₗ (eihdOutGen M ha).symm) := by
    -- eihdOutGen.symm = packStairGen.symm ≪≫ paramsEquivFlatLinear (unfold eihdOutGen).
    have heihd : (eihdOutGen M ha).symm
        = (packStairGen M ha ha.hL).symm ≪≫ₗ paramsEquivFlatLinear M := by
      rw [eihdOutGen, LinearEquiv.trans_symm]
      congr 1
    rw [heihd]
    exact (isCoordLE_eInGen M ha).trans
      (((isCoordLE_packStairGen M ha ha.hL).symm).trans (isCoordLE_paramsEquivFlatLinear M))
  obtain ⟨σ, hσ⟩ := hcoord
  refine ⟨σ, ?_⟩
  rw [show ((eihdOutGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))
        ∘ₗ ((eInGen M ha) : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L)
      = ((eInGen M ha ≪≫ₗ (eihdOutGen M ha).symm :
            (Fin (routeMAmbient M) → ℝ) ≃ₗ[ℝ] (Fin (routeMAmbient M) → ℝ)) :
          (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ)) from rfl]
  have hthis := hσ
  rw [show (LinearEquiv.refl ℝ (Fin (routeMAmbient M) → ℝ)).symm ≪≫ₗ
        (eInGen M ha ≪≫ₗ (eihdOutGen M ha).symm) ≪≫ₗ LinearEquiv.refl ℝ (Fin (routeMAmbient M) → ℝ)
      = (eInGen M ha ≪≫ₗ (eihdOutGen M ha).symm) from by ext g; rfl] at hthis
  rw [hthis]

/-! ## The headline: `DtotGen_abs_det` -/

/-- **`DtotGen_abs_det`** — the general-`L` boundary-factor determinant (Factor 1). Given the conjugacy
`eihd_hD_gen`, the per-boundary dets `genF_abs_det`, and the regauge `eihd_hreg_gen`, the determinant
of `DtotGen ha y₀` is the multi-boundary Schur value

  `∏_{s : Fin L} |det (readK y₀ s)|^{(Text(s+1) − Text(s+2)) + (Wext(s+1) − Text(s+2))}`.

Via the general spine `stairMap_abs_det_twoConj` on `eihd_hD_gen`, the per-boundary block dets
`genF_abs_det` folding the product to the readers. The general-`L` lift of
`RouteMEihdFreePoint.Dtot_abs_det_free`. -/
theorem DtotGen_abs_det (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (DtotGen M ha y₀)|
      = ∏ s : Fin L, |(Matrix.of (readK M (tach M) ha y₀ s)).det|
          ^ ((Text M (tach M) (s.val + 1) - Text M (tach M) (s.val + 2))
            + (Wext M (s.val + 1) - Text M (tach M) (s.val + 2))) := by
  rw [stairMap_abs_det_twoConj (genV M) L (genF M ha y₀) (eihdcGen M ha y₀)
        (eInGen M ha) (eihdOutGen M ha) (DtotGen M ha y₀) (eihd_hD_gen M ha y₀)
        (eihd_hreg_gen M ha)]
  exact Finset.prod_congr rfl (fun s _ => genF_abs_det M ha y₀ s)

end DLNFibre.DLN.RLCT

end
