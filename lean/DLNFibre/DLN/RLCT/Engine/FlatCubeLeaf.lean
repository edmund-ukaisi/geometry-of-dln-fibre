import DLNFibre.DLN.RLCT.Engine.PivotLeafClauses

/-!
# `DLNFibre.DLN.RLCT.Engine.FlatCubeLeaf` — the flat-cube `LeafData` smart-constructor (rung 3)

Construction-INDEPENDENT leaf-emission infrastructure (controller steer): `buildTree`'s leaf
emission calls ONE constructor and inherits the FIVE free per-leaf `ChartBridge` conjuncts
(measurable + bounded + the three coordinate clauses), discharged via `PivotLeafClauses`. The THREE
chart-data-fed Props (`LeafPullback`, `LeafJacobian`, the a.e.-`InjOn` clause) stay as HYPOTHESIS
slots — rung-3 proper fills them per leaf.

* `flatCubeLeafData` assembles a contract-shaped `LeafData`: flat-cube `srcBox` at radius `R`; the
  B' split's t̃=0 analytic enumeration (`numDiv`/`divExp`/`divProfile`) + full-ledger sides
  (`fullNumDiv`/…) both supplied; `chartMap` is a FREE field (its ψ∘β shape lives in the
  `LeafJacobian` hypothesis, so a gauge ψ-factor needs no field change here).
* `flatCubeLeafData_perLeafClause` proves the full 8-conjunct per-leaf `ChartBridge` clause for the
  constructed leaf: the 5 free clauses discharged, the 3 fed ones passed through.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **The flat-cube `LeafData` smart-constructor**: a contract-shaped leaf with
`srcBox = paramsEquivFlat ⁻¹' cubeBox (flatDim M) R` and all other fields supplied (B' t̃=0 analytic
side + full-ledger side; `chartMap` free). -/
noncomputable def flatCubeLeafData
    (numDiv : ℕ) (divExp : Fin numDiv → ℕ) (cleared : ℕ) (divProfile : Fin numDiv → (Fin L → ℕ))
    (fullNumDiv : ℕ) (fullDivExp : Fin fullNumDiv → ℕ)
    (fullDivProfile : Fin fullNumDiv → (Fin L → ℕ))
    (numB : ℕ) (bExp : Fin numB → (Fin numDiv → ℕ)) (bChain : Monotone bExp)
    (chartMap : Params M → Params M) (R : ℝ) (resRank : ℕ)
    (divCoord : Fin numDiv → Fin (flatDim M)) (resCoord : Fin resRank → Fin (flatDim M)) :
    LeafData M where
  numDiv := numDiv; divExp := divExp; cleared := cleared; divProfile := divProfile
  fullNumDiv := fullNumDiv; fullDivExp := fullDivExp; fullDivProfile := fullDivProfile
  numB := numB; bExp := bExp; bChain := bChain
  chartMap := chartMap
  srcBox := ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R
  resRank := resRank; divCoord := divCoord; resCoord := resCoord

/-- **The per-leaf `ChartBridge` clause for a flat-cube leaf** — the packaging the controller asked
for. The 5 FREE clauses (`MeasurableSet`, bounded-in-flat-cube, `Injective` div/res, `Disjoint`) are
discharged from `PivotLeafClauses`; the 3 CHART-DATA-FED clauses (a.e.-`InjOn`, `LeafPullback`,
`LeafJacobian`) are hypotheses. `buildTree` calls this once per emitted leaf. -/
theorem flatCubeLeafData_perLeafClause
    (numDiv : ℕ) (divExp : Fin numDiv → ℕ) (cleared : ℕ) (divProfile : Fin numDiv → (Fin L → ℕ))
    (fullNumDiv : ℕ) (fullDivExp : Fin fullNumDiv → ℕ)
    (fullDivProfile : Fin fullNumDiv → (Fin L → ℕ))
    (numB : ℕ) (bExp : Fin numB → (Fin numDiv → ℕ)) (bChain : Monotone bExp)
    (chartMap : Params M → Params M) {R : ℝ} (resRank : ℕ)
    (divCoord : Fin numDiv → Fin (flatDim M)) (resCoord : Fin resRank → Fin (flatDim M))
    (hR : 0 < R) (hdiv : Function.Injective divCoord) (hres : Function.Injective resCoord)
    (hne : ∀ k j, divCoord k ≠ resCoord j)
    (hInj : ∃ N : Set (Params M), volume N = 0 ∧
      Set.InjOn (flatCubeLeafData numDiv divExp cleared divProfile fullNumDiv fullDivExp
        fullDivProfile numB bExp bChain chartMap R resRank divCoord resCoord).chartMap
        ((flatCubeLeafData numDiv divExp cleared divProfile fullNumDiv fullDivExp fullDivProfile
          numB bExp bChain chartMap R resRank divCoord resCoord).srcBox \ N))
    (hpull : LeafPullback (flatCubeLeafData numDiv divExp cleared divProfile fullNumDiv fullDivExp
      fullDivProfile numB bExp bChain chartMap R resRank divCoord resCoord))
    (hjac : LeafJacobian (flatCubeLeafData numDiv divExp cleared divProfile fullNumDiv fullDivExp
      fullDivProfile numB bExp bChain chartMap R resRank divCoord resCoord)) :
    (let l := flatCubeLeafData numDiv divExp cleared divProfile fullNumDiv fullDivExp fullDivProfile
      numB bExp bChain chartMap R resRank divCoord resCoord
     MeasurableSet l.srcBox ∧
       (∃ R' : ℝ, 0 < R' ∧ l.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R') ∧
       Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
       Disjoint (Set.range l.divCoord) (Set.range l.resCoord) ∧
       (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn l.chartMap (l.srcBox \ N)) ∧
       LeafPullback l ∧ LeafJacobian l) :=
  ⟨flatCubeSrcBox_measurableSet R, flatCubeSrcBox_bounded hR, hdiv, hres,
    coords_disjoint_of_ne divCoord resCoord hne, hInj, hpull, hjac⟩

end DLNFibre.DLN.RLCT.Engine
