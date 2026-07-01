import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenBase
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenChart
import DLNFibre.DLN.RLCT.Validate.RouteMSchurStairDet
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Validate.RouteMChainFDerivValue
import DLNFibre.DLN.RLCT.Validate.RouteMReaderFDeriv
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear

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

/-- **The regauge abs-det-`1`** `eihd_hreg_gen` — `|det (eihdOutGen.symm ∘ eInGen)| = 1`. The
general-`L` lift of `RouteMHregPerm.eihd_hreg` (a slot-reindex is measure/det-1). LOAD-BEARING
RESIDUAL. -/
theorem eihd_hreg_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    |LinearMap.det
        (((eihdOutGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))
        ∘ₗ ((eInGen M ha) : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L))| = 1 := by
  -- The regauge `eihdOutGen.symm ∘ eInGen` is a slot↔(staggered)Params-layer coordinate REINDEX —
  -- a signed permutation of coords, det ±1 (abs 1). NO LONGER trivial `= id` (eihdOutGen ≠ eInGen now;
  -- eOut is the STAGGERED pack). Route: it's `funCongrLeft` of an index `Equiv`, so `det = ±1` via the
  -- `IsCoordLE`/`hreg_of_exists_funCongrLeft` infra (`RouteMHregPerm`, `isCoordLE_of_read`).
  -- MISSING: certify the composite as a coordinate reindex (det ±1) — lift of `RouteMHregPerm.eihd_hreg`.
  sorry

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
