import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction
import DLNFibre.DLN.RLCT.Validate.RouteMBridge

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMLayerValue` — the R1 VALUE lane on the layer atlas

The migration of the R1 value/recursion lane off the fixed-arity `ChainDimSplit`/`routeStep`
carrier (whose general `branch` arm is the documented `sorry` in `RouteMRecursion.lean` — the
encoding the fixed-arity carrier structurally cannot express) onto the PROVEN layer-collapsing
atlas `routeLayerAtlas` (`RouteMLayerSplit.lean`, 0 sorry). This file is PARALLEL: it does not
touch the old inductive; it re-points the value lane to the banked atlas, exposing the chart
family in EXACTLY the `(ι, d, k, h)`-tuple shape `routeM_rlctAtOn_eq_iInf`/`resolution_charts`
consume.

## What this banks (sorry-free, axioms = the single S2 `monomial_rlct`)

- `layerD`/`layerK`/`layerH` — the per-leaf `(d, k, h)` accessors of `routeLayerAtlas M`, the
  chart family in the bridge's tuple shape.
- `routeLayerAtlas_isResolutionAtlas` — `IsResolutionAtlas M (layer family)` (the two value
  clauses `threshold_ge`/`achiever`), built from the banked `routeLayerAtlasAcc_leaf_singleton` /
  `_achiever` + `monomialThreshold_singleton`. Replaces the `sorryAx`-tainted
  `routeMGeneralValue`/`routeM_value_eq` (which fold over `routeMIota M`, whose value reduces
  through the open `routeStep` branch).
- `routeLayerAtlas_value_eq_lambdaCore` — `⨅ monomialThreshold = ofReal(lambdaCore M)` over the
  layer family (via `resolution_value_of_atlas` ∘ the atlas above). The R1 value target,
  delivered by the layer-collapsing atlas.

## The residual (NOT closed here — the SEPARATE cover lane)

`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold` — an equality whose VALUE is this
lane (`= ½·minAdm = lambdaCore`) but whose `rlctAtOn = ⨅` content is the ANALYTIC COVER: the two
measure-theoretic legs of `IsRouteMCover` (`cover_le` finiteness, `cover_ge_div` divergence). The
value lane carries NO measure-theoretic information about the loss; it cannot supply the cover. So
`resolution_charts_of_layerCover` reduces `resolution_charts` to EXACTLY one residual hypothesis —
an `IsRouteMCover` over the layer family's `(ι, d, k, h)` — making the missing obligation crisp
and pinned to the precise chart family the cover proof must target (no interface drift). The
general-`M` `IsRouteMCover` is the SEPARATE 2nd lane (#104, only `(2,2,2)` is hand-built); it is
NOT started here.
-/

open scoped ENNReal BigOperators
open MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The layer atlas's chart family in the bridge's `(ι, d, k, h)` tuple shape

`routeLayerAtlas M : LayerChartFamily` carries `ι` + `data : ι → MonoData`. The bridge
`routeM_rlctAtOn_eq_iInf` and the gate `resolution_charts` consume the SPLIT tuple `(d, k, h)`.
These accessors expose it in that shape, fixing the exact family the cover lane must target. -/

/-- The per-leaf chart dimension of the layer-collapsing atlas. -/
noncomputable def layerD (M : Fin (L + 1) → ℕ) (i : (routeLayerAtlas M).ι) : ℕ :=
  ((routeLayerAtlas M).data i).d

/-- The per-leaf loss-base exponents `k` of the layer-collapsing atlas. -/
noncomputable def layerK (M : Fin (L + 1) → ℕ) (i : (routeLayerAtlas M).ι) :
    Fin (layerD M i) → ℕ :=
  ((routeLayerAtlas M).data i).k

/-- The per-leaf Jacobian exponents `h` of the layer-collapsing atlas. -/
noncomputable def layerH (M : Fin (L + 1) → ℕ) (i : (routeLayerAtlas M).ι) :
    Fin (layerD M i) → ℕ :=
  ((routeLayerAtlas M).data i).h

/-- `ι` of the layer atlas is a `Fintype` (the atlas field). The bridge's `[Fintype ι]`. -/
noncomputable instance instFintypeLayerIota (M : Fin (L + 1) → ℕ) :
    Fintype ((routeLayerAtlas M).ι) :=
  (routeLayerAtlas M).fintype

/-- `ι` of the layer atlas is `Nonempty` (the atlas field). The bridge's `[Nonempty ι]` for the
achiever-side `iInf_le`. -/
instance instNonemptyLayerIota (M : Fin (L + 1) → ℕ) : Nonempty ((routeLayerAtlas M).ι) :=
  (routeLayerAtlas M).nonempty

/-! ## The `IsResolutionAtlas` instance from the layer atlas (the value clauses, sorry-free)

The two clauses `IsResolutionAtlas` consumes — uniform `threshold_ge` (no undershoot) and the
`achiever` (no over-estimate) — both keyed to `m₀ = (Adm M).inf' Mval = minAdm M`. Built from the
banked single-divisor leaf facts of the layer atlas (`routeLayerAtlasAcc_leaf_singleton` /
`_achiever`) + `monomialThreshold_singleton`. This is the genuine value content the
`sorryAx`-tainted `routeMGeneralValue` only delivered conditionally on the open `routeStep`
branch. -/

/-- **The layer-collapsing atlas IS a resolution atlas** (for non-degenerate `1 ≤ minAdm M`). Every
leaf's single-divisor threshold is `≥ ½·minAdm` (`threshold_ge`, from the leaf's `minAdm ≤ c` +
`monomialThreshold_singleton`), and the achiever leaf hits `= ½·minAdm` (`achiever`, from
`routeLayerAtlasAcc_achiever` + `layerLeafMin M 0 = minAdm M`). Sorry-free; the value residual (the
`achiever` "reached" obligation the old lane carried) is DISCHARGED here — the layer recursion's
`_achiever` constructs the achiever leaf explicitly. -/
theorem routeLayerAtlas_isResolutionAtlas (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
    IsResolutionAtlas M (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M) where
  threshold_ge := by
    intro i
    obtain ⟨c, hc, hcge⟩ := routeLayerAtlasAcc_leaf_singleton M 0 i
    have hmin0 : layerLeafMin M 0 = minAdm M := by rw [layerLeafMin_eq]; omega
    have hge : minAdm M ≤ c := by rwa [hmin0] at hcge
    have hthr : monomialThreshold (layerD M i) (layerK M i) (layerH M i) = (c : ℝ≥0∞) / 2 := by
      unfold layerD layerK layerH
      rw [show ((routeLayerAtlas M).data i) = MonoData.foldDivisors [c] from hc]
      exact monomialThreshold_singleton c (le_trans hpos hge)
    -- m₀ = ((Adm M).inf' Mval).toNat = minAdm M (defeq).
    show (((minAdm M : ℕ) : ℝ≥0∞)) / 2 ≤ _
    rw [hthr]
    exact ENNReal.div_le_div_right (by exact_mod_cast hge) 2
  achiever := by
    obtain ⟨i, hi⟩ := routeLayerAtlasAcc_achiever M 0
    have hmin0 : layerLeafMin M 0 = minAdm M := by rw [layerLeafMin_eq]; omega
    refine ⟨i, ?_⟩
    have hthr :
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) = (minAdm M : ℝ≥0∞) / 2 := by
      unfold layerD layerK layerH
      rw [show ((routeLayerAtlas M).data i)
          = MonoData.foldDivisors [layerLeafMin M 0] from hi, hmin0]
      exact monomialThreshold_singleton (minAdm M) hpos
    show monomialThreshold (layerD M i) (layerK M i) (layerH M i) = (((minAdm M : ℕ) : ℝ≥0∞)) / 2
    exact hthr

/-! ## The migrated value lane: `⨅ monomialThreshold = ofReal(lambdaCore M)` -/

/-- **The R1 value-fold over the layer atlas** (the migrated value lane). The `⨅` over the
layer-collapsing chart family of the per-leaf `monomialThreshold` is `ofReal(lambdaCore M)` (for
non-degenerate `1 ≤ minAdm M`). Via `resolution_value_of_atlas` ∘
`routeLayerAtlas_isResolutionAtlas`. This is the value `resolution_charts`'s RHS lands on —
delivered SORRY-FREE by the layer-collapsing atlas, replacing the
`routeMGeneralValue`/`routeM_value_eq` fold over `routeMIota M` (which inherited `sorryAx` through
the open `routeStep` branch). -/
theorem routeLayerAtlas_value_eq_lambdaCore (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
    (⨅ i : (routeLayerAtlas M).ι, monomialThreshold (layerD M i) (layerK M i) (layerH M i))
      = ENNReal.ofReal (lambdaCore M : ℝ) :=
  resolution_value_of_atlas M (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M)
    (routeLayerAtlas_isResolutionAtlas M hpos)

/-- The same value as `½·minAdm M` (the `ENNReal` half-of-codim form), an alternate phrasing
matching `routeLayerAtlas_value` directly. -/
theorem routeLayerAtlas_value_eq_half_minAdm (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
    (⨅ i : (routeLayerAtlas M).ι, monomialThreshold (layerD M i) (layerK M i) (layerH M i))
      = (minAdm M : ℝ≥0∞) / 2 := by
  show (⨅ i : (routeLayerAtlas M).ι,
      monomialThreshold ((routeLayerAtlas M).data i).d
        ((routeLayerAtlas M).data i).k ((routeLayerAtlas M).data i).h) = _
  exact routeLayerAtlas_value M hpos

/-! ## The R1 gate reduced to EXACTLY the layer-family cover (the crisp residual)

`resolution_charts` is `rlctAtOn(core) = ⨅ monomialThreshold`. The VALUE (`= ½·minAdm = lambdaCore`)
is the lane above; the `rlctAtOn = ⨅` content is the ANALYTIC COVER (`IsRouteMCover`'s two legs).
This theorem closes `resolution_charts` GIVEN that cover for the layer family — pinning the single
residual obligation to the precise `(ι, d, k, h)` the cover proof must target (Codex-flagged
anti-drift). The cover itself is the SEPARATE 2nd lane (#104). -/

/-- **`resolution_charts` reduced to the layer-family cover.** Given an `IsRouteMCover` for the flat
core `routeMCore M` over the bounded box `routeMBaseNbhd M` with the layer atlas's chart family
`(ι, layerD, layerK, layerH)`, the R1 gate's existential holds: there is a chart family whose
`⨅ monomialThreshold` is the core RLCT at the deepest point. Via `routeM_rlctAtOn_eq_iInf` (the
bridge) ∘ `rlctAtOn_routeMCore_transport` (flat ↔ params). The residual `hcover` is the ONLY missing
piece — the value lane is fully discharged. This makes the R1 gate's remaining obligation crisp:
build `IsRouteMCover` for THIS family. -/
theorem resolution_charts_of_layerCover (M : Fin (L + 1) → ℕ)
    (hcover : IsRouteMCover (routeMCore M) (routeMBaseNbhd M) (routeLayerAtlas M).ι
      (layerD M) (layerK M) (layerH M)) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params M =>
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A) (fun _ => 0 : Params M)
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  refine ⟨(routeLayerAtlas M).ι, (routeLayerAtlas M).fintype, layerD M, layerK M, layerH M, ?_⟩
  have hbridge := routeM_rlctAtOn_eq_iInf (routeMCore M) (routeMBaseNbhd M)
    (routeLayerAtlas M).ι (layerD M) (layerK M) (layerH M) hcover
  rw [← rlctAtOn_routeMCore_transport M]
  exact hbridge

/-! ## Non-vacuity: the layer value lane fires on the `(2,2,2)` anchor -/

/-- **Non-vacuity (the `(2,2,2)` anchor).** The migrated value lane folds `(2,2,2)` to `3/2`:
`⨅ monomialThreshold = ½·minAdm(2,2,2) = 3/2 = lambdaCore(2,2,2)`, confirming the lane is
non-vacuous and reproduces the headline. (`minAdm(2,2,2) = 3`.) Routed through the `½·minAdm` form
(`Nat` cast). -/
theorem routeLayerAtlas_value_eq_lambdaCore_M222 :
    (⨅ i : (routeLayerAtlas (![2, 2, 2] : Fin 3 → ℕ)).ι,
        monomialThreshold (layerD (![2, 2, 2] : Fin 3 → ℕ) i)
          (layerK (![2, 2, 2] : Fin 3 → ℕ) i) (layerH (![2, 2, 2] : Fin 3 → ℕ) i))
      = 3 / 2 := by
  rw [routeLayerAtlas_value_eq_half_minAdm (![2, 2, 2] : Fin 3 → ℕ) (by decide)]
  norm_num [show minAdm (![2, 2, 2] : Fin 3 → ℕ) = 3 from by decide]

end DLNFibre.DLN.RLCT
