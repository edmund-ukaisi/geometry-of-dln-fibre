import DLNFibre.DLN.RLCT.Engine.EngineDefs

/-!
# `DLNFibre.DLN.RLCT.Engine.ChartBridgeWiring` — the whole-`ChartBridge` wiring skeleton (rung 3)

The typed/sorried/wired assembly (controller answer (a)): `chartBridge_of_pieces` builds
`ChartBridge M t` from the coverage pieces, so the discharge closes the moment the o5 realization
supplies them. Per the ANTI-VACUITY PIN: every fed Prop is stated against the FOLD-FORM chart
`χ : LeafData M → (Params M → Params M)` (a PARAMETER), never the leaf record's placeholder
`chartMap` field. The stored/fold coherence `l.chartMap = χ l` bridges to the `ChartBridge` clauses
(which read `l.chartMap`). Parametrized by `χ`, so it survives either architect resolution
(buildTree fills `chartMap` with the real fold, or `ChartBridge`'s hole quantifies over the fold).

`LeafPullbackWith`/`LeafJacobianWith` are the fold-form variants of `EngineDefs.LeafPullback`/
`LeafJacobian` (`χ` in place of `l.chartMap`); `LeafPullback l = LeafPullbackWith l l.chartMap` by
`rfl` (same body), so the bridge is a rewrite along the coherence.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open MeasureTheory Set

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **Fold-form `LeafPullback`**: `EngineDefs.LeafPullback` with the chart `χ` in place of the leaf
record's `chartMap` field (anti-vacuity: stated against the fold-form, not the placeholder). -/
def LeafPullbackWith (l : LeafData (L := L) M) (χ : Params M → Params M) : Prop :=
  ∃ (residualCore : Params M → ℝ) (lo hi : ℝ), 0 < lo ∧
    ∀ w ∈ l.srcBox,
      frobSq (prod M (χ w))
          = (∏ k : Fin l.numDiv, (paramsEquivFlat M w (l.divCoord k)) ^ 2) * residualCore w ∧
      lo * residualBaseForm l w ≤ residualCore w ∧ residualCore w ≤ hi * residualBaseForm l w

/-- **Fold-form `LeafJacobian`**: `EngineDefs.LeafJacobian` with `χ` in place of `chartMap`. -/
def LeafJacobianWith (l : LeafData (L := L) M) (χ : Params M → Params M) : Prop :=
  ∃ (β ψ ψsymm : Params M → Params M)
    (Dβ Dψ : Params M → (Params M →L[ℝ] Params M)) (lo hi : ℝ), 0 < lo ∧
    (∀ w ∈ l.srcBox, χ w = ψ (β w)) ∧
    (∀ w ∈ l.srcBox, HasFDerivAt β (Dβ w) w ∧
      |(Dβ w).det|
        = ∏ k : Fin l.numDiv, |paramsEquivFlat M w (l.divCoord k)| ^ (l.divExp k - 1)) ∧
    (∀ v ∈ β '' l.srcBox, ψsymm (ψ v) = v ∧ ψ (ψsymm v) = v ∧
      HasFDerivAt ψ (Dψ v) v ∧ lo ≤ |(Dψ v).det| ∧ |(Dψ v).det| ≤ hi)

/-- `LeafPullback l = LeafPullbackWith l l.chartMap` (same body) — fold-form at the stored chart. -/
theorem leafPullback_eq_with (l : LeafData (L := L) M) :
    LeafPullback l = LeafPullbackWith l l.chartMap := rfl

/-- `LeafJacobian l = LeafJacobianWith l l.chartMap` (same body). -/
theorem leafJacobian_eq_with (l : LeafData (L := L) M) :
    LeafJacobian l = LeafJacobianWith l l.chartMap := rfl

/-- **The whole-`ChartBridge` wiring skeleton.** Given a fold-form chart assignment `χ`, the
stored/fold coherence `hχ : l.chartMap = χ l`, the `leafPaths` coherence clause `hpath`, the
image-cover over `χ` (`himg`), and the per-leaf pieces over `χ` (`hleaf`: five free clauses + the
three o5-fed Props `a.e.-InjOn`/`LeafPullbackWith`/`LeafJacobianWith`), `ChartBridge M t` holds. The
fed Props enter ONLY through `hleaf`, over `χ` — o5 discharges them over the real charts. -/
theorem chartBridge_of_pieces (t : ResolutionTree M) (χ : LeafData M → (Params M → Params M))
    (hχ : ∀ l ∈ ResolutionTree.leaves t, l.chartMap = χ l)
    (hpath : ∀ p ∈ ResolutionTree.leafPaths (id : Params M → Params M) t, p.1.chartMap = p.2)
    (himg : ∃ U : Set (Params M), IsOpen U ∧
      {A : Params M | A ∈ paramsBoxM M 1 ∧ frobSq (prod M A) = 0} ⊆ U ∧
      U ⊆ ⋃ l ∈ ResolutionTree.leaves t, χ l '' l.srcBox)
    (hleaf : ∀ l ∈ ResolutionTree.leaves t,
      MeasurableSet l.srcBox ∧
        (∃ R : ℝ, 0 < R ∧ l.srcBox ⊆ ⇑(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) R) ∧
        Function.Injective l.divCoord ∧ Function.Injective l.resCoord ∧
        Disjoint (Set.range l.divCoord) (Set.range l.resCoord) ∧
        (∃ N : Set (Params M), volume N = 0 ∧ Set.InjOn (χ l) (l.srcBox \ N)) ∧
        LeafPullbackWith l (χ l) ∧ LeafJacobianWith l (χ l)) :
    ChartBridge M t := by
  refine ⟨?_, ?_, hpath⟩
  · -- image-cover: rewrite `χ l '' srcBox` to `l.chartMap '' srcBox` via `hχ`
    obtain ⟨U, hUopen, hzero, hsub⟩ := himg
    refine ⟨U, hUopen, hzero, hsub.trans (Set.iUnion₂_mono fun l hl => le_of_eq ?_)⟩
    rw [hχ l hl]
  · intro l hl
    obtain ⟨hm, hb, hdi, hri, hdis, hinj, hpull, hjac⟩ := hleaf l hl
    refine ⟨hm, hb, hdi, hri, hdis, ?_, ?_, ?_⟩
    · rw [hχ l hl]; exact hinj
    · rw [leafPullback_eq_with l, hχ l hl]; exact hpull
    · rw [leafJacobian_eq_with l, hχ l hl]; exact hjac

end DLNFibre.DLN.RLCT.Engine
