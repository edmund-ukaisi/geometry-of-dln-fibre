import DLNFibre.DLN.RLCT.Engine.GeoChart
import DLNFibre.DLN.RLCT.Validate.RouteMConjBlock

/-!
# `DLNFibre.DLN.RLCT.Engine.GeoJacobianSpec` — the per-edge fold-Jacobian atom (t11)

This module was the fill-target for the fold-Jacobian SPECIFY (coverage-t08 → t11): the accumulation
identity `|det D(path-fold)| = ∏_k |z_k|^{divExp k − 1}` over `geometricLeafPaths`. In grinding the
PROVE, t11 established the load-bearing **per-edge det atom** (below, `geoChartMap_fderiv_det`) — the
elder's chart-by-chart Jacobian, made honest in Lean — and, in doing so, surfaced that the SPECIFY's
top-level statement is **false as written** and rests on an unbuilt construction. The three findings
(Codex-corroborated, `threads/10-coverage/codex/fold-jacobian-scoping-answer.md`):

1. **The `∀ t` top-level statement is false.** For `t = .leaf l`, the composite is `id`
   (`|det D id| = 1`) while the RHS `∏_k |z_{divCoord k}|^{divExp k − 1}` is a nonconstant monomial
   whenever `l.numDiv ≥ 1` and some `divExp k ≥ 2` (it vanishes on the divisor). The sibling cover
   SPECIFY `geoAtlas_imageCover` carries `htree : t = buildTree M (conOracle M) s`; the fold-det
   SPECIFY omitted it. Even `htree` at an arbitrary `s` is insufficient (a non-root `s` already carries
   divisors the composite does not blow up) — the honest scope is the root `conRoot` + a coherence.

2. **The ledger↔geometry match is a separate coherence cocycle, not chain-rule + atoms.** The chain
   rule over the fold yields a product of per-node factors `|z_{cNodeOf(n_j)(pivot_j)}(w_j)|^{…}`
   evaluated at INTERMEDIATE points `w_j` and indexed by the PATH PIVOTS. Matching that to the leaf's
   ledger `∏_k |z_{divCoord k}(w)|^{divExp k − 1}` (source `w`, ledger divisors) needs a one-step
   relative-Jacobian cocycle telescoping from `conRoot = 1` (the `stepUpdate` reindexing + accumulated
   exponents). Chain rule alone carries no `stepUpdate` information — this content is stronger than the
   map-fidelity clause (D).

3. **The current `geoAtlas` cannot satisfy `LeafJacobian` for the fan-out pieces (upstream defect).**
   `geoAtlas` sets each piece to `{ leaf with chartMap := composite }`, so every fan-out copy of a leaf
   shares the SAME `leaf.divCoord`; but the fan-out over `p : Fin (dCenterOfEdge …)` gives each copy a
   DIFFERENT exceptional coordinate `cNodeOf … (offset+p)` (`cNodeOf` is injective). So `LeafJacobian`'s
   `|det Dβ| = ∏_k |z_{divCoord k}|^{divExp k − 1}` (fixed `divCoord`) fails for every piece whose pivot
   ≠ the birth-corner pivot. The corrected `ChartBridge` design already calls for **per-pivot**
   `divCoord` (`EngineDefs.lean` clause (B) note: "per-pivot `divCoord` dissolves the frozen type's
   piecewise failure"); `geometricLeafPaths`/`geoAtlas` must re-derive each piece's `divCoord`/`divExp`
   from its pivots rather than inherit the leaf's. That is a construction fix in `GeoChart.lean`
   (upstream of this leaf module).

**What is banked here (all sorry-free):** the per-edge det atom + its two coordinate lemmas. The atom
is construction-stable (it is a fact about `geoChartMap`, unaffected by findings 1–3) and is the
reusable Jacobian workhorse any correctly-constructed fold consumes:

    |det D(geoChartMap … g) w| = |paramsEquivFlat M w (cNodeOf g.node hd ⟨g.pivot⟩)| ^ (dCenterOfNode − 1)

via t09's q-conjugation trio (`conjBlock_*` from `RouteMConjBlock`, which is definitionally
`geoChartMap`'s on-cone `q.symm ∘ (pivotChart × id) ∘ q`) + `abs_det_fderiv`-class `pivotChartDeriv_det`.
The top-level fold-det theorem is deferred pending the controller's decision on the finding-3
construction fix and the finding-2 cocycle (both surfaced to team-lead).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open scoped BigOperators

variable {L : ℕ} {M : Fin (L + 1) → ℕ}

/-- **`centerPerm.symm` reads `Sum.inl i` to the center coordinate `c i`.** The bookkeeping fact the
`qOfCenter` first-component read needs: the center permutation sends the `i`-th `inl` slot back to the
selector's flat coordinate. -/
theorem centerPerm_symm_inl (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (i : Fin d) :
    (centerPerm M c hinj).symm (Sum.inl i) = c i := by
  classical
  unfold centerPerm
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
    Sum.map_inl, Equiv.sumCompl_apply_inl, Equiv.ofInjective_apply]

/-- **The first component of `qOfCenterCLE` reads the center coordinate.** `(qOfCenterCLE M c hinj w).1 i
= z_{c i}(w)` — the `q`-split sends `Params M` to the `d` center coords named by `c` (its first factor)
times the rest, and the `i`-th center coord is the flat read of `w` at `c i`. -/
theorem qOfCenterCLE_fst_apply (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) (w : Params M) (i : Fin d) :
    (qOfCenterCLE M c hinj w).1 i = paramsEquivFlat M w (c i) := by
  have hcoe : ⇑(LinearEquiv.piCongrLeft ℝ (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
      (centerPerm M c hinj)) = ⇑(Equiv.piCongrLeft (fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
      (centerPerm M c hinj)) := rfl
  unfold qOfCenterCLE
  simp only [ContinuousLinearEquiv.trans_apply, LinearEquiv.coe_toContinuousLinearEquiv',
    paramsEquivFlatCLE_coe, LinearEquiv.sumArrowLequivProdArrow_apply_fst, hcoe]
  rw [show (Sum.inl i : Fin d ⊕ Fin (flatDim M - d))
        = centerPerm M c hinj ((centerPerm M c hinj).symm (Sum.inl i)) from
      (Equiv.apply_symm_apply _ _).symm]
  rw [Equiv.piCongrLeft_apply_apply, centerPerm_symm_inl]

/-- **The per-edge fold-Jacobian atom** (on-cone). The Fréchet-derivative determinant of a single
geometric blow-up chart `geoChartMap … g` is the monomial `|z_pivot(w)|^{d_center − 1}` in the flat
coordinate `cNodeOf g.node ⟨g.pivot⟩` that the node blows up (the exceptional divisor of the chosen
pivot chart), where `d_center = dCenterOfNode g.node`. Proven by q-CONJUGATION: `geoChartMap … g` is
definitionally the `conjBlockMap`-shape `q.symm ∘ (pivotChart ⟨g.pivot⟩ ×ˢ id) ∘ q` with
`q = qNodeOf g.node hd` a LINEAR homeomorphism (fderiv the fixed CLE `qOfCenterCLE`), so
`conjBlock_abs_det` cancels the two CLE dets and reads off `pivotChartDeriv`'s
`|z|^{d−1}` at the prefix block `(q w).1 = z_{cNodeOf ⟨pivot⟩}`. -/
theorem geoChartMap_fderiv_det (g : GeoChart M) (w : Params M)
    (hd : dCenterOfNode M g.node ≤ flatDim M) (hp : g.pivot < dCenterOfNode M g.node) :
    |(fderiv ℝ (geoChartMap (dCenterOfNode M) (qNodeOf M) g) w).det|
      = |paramsEquivFlat M w (cNodeOf M g.node hd ⟨g.pivot, hp⟩)| ^ (dCenterOfNode M g.node - 1) := by
  have hinj : Function.Injective (cNodeOf M g.node hd) := cNodeOf_injective M g.node hd
  have hfun : geoChartMap (dCenterOfNode M) (qNodeOf M) g
      = conjBlockMap (qOfCenterCLE M (cNodeOf M g.node hd) hinj)
          (pivotChart (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) := by
    unfold geoChartMap qNodeOf conjBlockMap
    rw [dif_pos hd, dif_pos hp]
    rfl
  have hfd : HasFDerivAt (geoChartMap (dCenterOfNode M) (qNodeOf M) g)
      (conjBlockDeriv (qOfCenterCLE M (cNodeOf M g.node hd) hinj)
        (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) w) w := by
    rw [hfun]
    exact conjBlock_hasFDerivAt _ _ _ (pivotChart_hasFDerivAt _) w
  rw [hfd.fderiv]
  have hJ : ∀ b : Fin (dCenterOfNode M g.node) → ℝ,
      |LinearMap.det (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)) b).toLinearMap|
        = |b ⟨g.pivot, hp⟩| ^ (dCenterOfNode M g.node - 1) := by
    intro b
    rw [show LinearMap.det
          (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)) b).toLinearMap
        = (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)) b).det from rfl,
      pivotChartDeriv_det _ b, abs_pow]
  have hconj := conjBlock_abs_det (qOfCenterCLE M (cNodeOf M g.node hd) hinj)
    (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node)))
    (fun b => |b ⟨g.pivot, hp⟩| ^ (dCenterOfNode M g.node - 1)) hJ w
  rw [show (conjBlockDeriv (qOfCenterCLE M (cNodeOf M g.node hd) hinj)
        (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) w).det
      = LinearMap.det (conjBlockDeriv (qOfCenterCLE M (cNodeOf M g.node hd) hinj)
        (pivotChartDeriv (⟨g.pivot, hp⟩ : Fin (dCenterOfNode M g.node))) w).toLinearMap from rfl]
  rw [hconj]
  simp only [qOfCenterCLE_fst_apply]

end DLNFibre.DLN.RLCT.Engine
