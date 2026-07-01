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

## Status (ROUND-2 corrected: staggered output pack; 4 residuals)

`DtotGen_abs_det` is PROVEN sorry-free MODULO the 4 residuals below: the general spine
`stairMap_abs_det_twoConj` is threaded and `genF_abs_det` folds the per-block dets to the readers
(`∏_{s : Fin L} |det (readK y₀ s)|^{r_s+c_s}`).

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

REMAINING (4 sorries, the corrected staggered-pack track — ROUTE B, Codex `high` verdict 2026-07-01):
* `packStairGen : Params M ≃ₗ StairProd genV L` — the staggered pack (Route B, ~120–160 LoC):
  (1) `piCongrRight` per-layer row-split `Matrix (Wext s)(Wext s+1) ≃ₗ kept_s × lift_s` (PROBE-CLEAN:
  `reindexLinearEquiv finSumFinEquiv.symm ≫ ofLinearEquiv.symm ≫ sumArrowLequivProdArrow ≫
  (ofLinearEquiv.prodCongr ofLinearEquiv)`); (2) the OFF-BY-ONE GATHER (lift `s ↦ s+1` via
  `LinearEquiv.piCongrLeft'` + the two 0-dim padded ends `lift 0 = 0`, `genLift (L−1) = 0` — the
  irreducible combinatorial core); (3) `piToStair`. This REPLACES the Route-A `outIdxToFlatIdx` index
  bijection (Codex: 200+ LoC Sigma bookkeeping — rejected).
* `eihdOutGen := packStairGen ∘ paramsEquivFlatLinear.symm` (thin — reuses the banked
  `paramsEquivFlatLinear` for flat↔Params, `routeMAmbient = flatDim` by `finCongr`).
* `eihd_hreg_gen` — `|det (eihdOutGen.symm ∘ eInGen)| = 1`: the slot↔staggered-layer reindex is a
  coord permutation (det ±1), via `RouteMHregPerm`'s `IsCoordLE`/`isCoordLE_of_read` infra. (No longer
  the trivial `= id` — that was the wrong-design artefact.)
* `eihd_hD_gen` — **THE CRUX**: `eihdOutGen ∘ DtotGen ∘ eInGen.symm = stairMap genV L genF eihdcGen`.
  Via `stairMap_eq_of_lowerTriDiag`, reduces to `StairLowerTriDiag genV L genF T`: per boundary (i)
  upper-block = 0 + (ii) diag = genF s (`Cgen` non-recursive = boundary-s Schur block → schurFrameDeriv_s;
  consumes chart's/the fderiv per-boundary collapse). Foundation banked: reader atoms + `hasFDerivAt_chainA`
  + `reindexLs` + `genF`. VERIFY-FIRST-confirmed: staggered dims = genV (17/9/0) exactly.

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
The `readK/X/N k` are read at the free point `y₀`. -/
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

/-- **The staggered pack** `packStairGen : Params M ≃ₗ StairProd genV L` — the CORRECT Params-layer →
staircase reshape. ROUTE B (Codex `high` verdict 2026-07-01: cleaner than the Route-A `ChartIdx ≃ FlatIdx`
index bijection, ~120–160 LoC): (1) `piCongrRight` split each layer into `kept_s × lift_s` (probe-clean
row-split above); (2) the OFF-BY-ONE GATHER — reindex the lift Pi `s ↦ s+1` so slot `s` gets
`lift(layer s+1)` (via `LinearEquiv.piCongrLeft'` on the lift index; the nonzero lifts are layers
`1..L−1 ≃ pred → slots 0..L−2`, with `lift 0 = 0`-dim [`Wext0−Text1=0`] and `genLift (L−1) = 0`-dim
[leaf] the two padded ends — `Subsingleton` closures); (3) `piToStair (genV M) L`. LOAD-BEARING RESIDUAL:
the row-split + the gather (the gather is the irreducible combinatorial core, per Codex). -/
def packStairGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    Params M ≃ₗ[ℝ] StairProd (genV M) L :=
  -- MISSING (Route B): piCongrRight (per-layer row-split) ≫ off-by-one lift gather (piCongrLeft' + 0-dim
  -- padding) ≫ piToStair. Row-split probe-clean; gather = the hard core.
  sorry

/-- **The staggered output pack** `eihdOutGen : (Fin (routeMAmbient M) → ℝ) ≃ₗ StairProd genV L` — the
CORRECT output reshape. `eihdOutGen := packStairGen ∘ paramsEquivFlatLinear.symm` (the controller's
directive; reuses the banked `paramsEquivFlatLinear : Params M ≃ₗ (Fin flatDim → ℝ)` for the
flat↔Params grouping, `routeMAmbient M = flatDim M` by `finCongr`). LOAD-BEARING RESIDUAL (thin — the
content is in `packStairGen`). -/
def eihdOutGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    (Fin (routeMAmbient M) → ℝ) ≃ₗ[ℝ] StairProd (genV M) L :=
  -- MISSING: packStairGen M ha ∘ paramsEquivFlatLinear.symm (through finCongr routeMAmbient=flatDim).
  sorry

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
fderiv, generalizing `layer0SchurMap_fderiv_collapse`. LOAD-BEARING RESIDUAL. -/
theorem eihd_hD_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y₀ : Fin (routeMAmbient M) → ℝ) :
    (eihdOutGen M ha : (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] StairProd (genV M) L)
        ∘ₗ DtotGen M ha y₀
        ∘ₗ ((eInGen M ha).symm : StairProd (genV M) L →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))
      = stairMap (genV M) L (genF M ha y₀) (eihdcGen M ha y₀) :=
  -- THE CRUX. MISSING: per-interior-boundary Schur-frame collapse — the fderiv diagonal block of
  -- `Agen s = chainA(readN s)(readW s)(Cgen (s+1))`, in `genV` coords, is `genF s`.
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
