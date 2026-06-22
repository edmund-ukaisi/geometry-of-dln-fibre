import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion
import DLNFibre.DLN.RLCT.Validate.RouteMState

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMRecursion` — the Route-M recursion REBASED onto `ChainDimSplit`

The recursion DRIVER for the general-M resolution, rebased onto crux2's banked `ChainDimSplit`
(controller seam decision g156: crux2 = the per-step additive straighten/descent over `ChainDimSplit`;
fm3 = the blow-up cover / `⨅`-min over pivot branches, layered on top). This file replaces the parallel
`RouteState`/`routeMeasure`/`routeRel_wf` machinery (which duplicated `ChainDimSplit`'s state-transition —
Codex-flagged sync liability) with the `ChainDimSplit`-based termination.

## What is shared vs owned (the seam, g155–g157)
- **crux2 owns** `ChainDimSplit` (the one-step width split `drop + red = M`, `L` fixed, `ΣM`-decreasing),
  its transport lemmas (`rlctAtOn_reduced_transport`, `schur_recursion_step_sound`/`_squeeze`), and the
  per-step `hGne`. `ChainDimSplit` is only ever CONSUMED in `GeneralR1Recursion`, never constructed there.
- **fm3 owns** (here + `RouteMState`): the iterated recursion over `ChainDimSplit` (terminating on `ΣM`),
  the per-node pivot BRANCHING (the `⨅`-min over pivot cells — `ChainDimSplit` is single-path), and the
  `MonoData` accumulation (`appendDivisor`/`foldDivisors`, `RouteMState.lean`, driver-agnostic, banked).

## Termination (the only piece banked here so far)
The recursion descends `M ↦ S.red` via a `ChainDimSplit M`. Termination is the `ΣM`-drop: `hdrops`
(`0 < Σ drop`) + `hsum` (`drop + red = M`) give `Σ red < Σ M`. This is the reusable, construction-agnostic
foundation — `redM_widthSum_lt` below names it (it was inlined in crux2's `schur_straighten_of_data`).
-/

open scoped BigOperators
namespace DLNFibre.DLN.RLCT

/-- The total width `Σ M` — the recursion's termination measure (rebased: replaces `RouteState.widthSum`,
now keyed to `ChainDimSplit`'s `ΣM`-drop rather than a parallel `RouteState`). -/
def chainWidthSum {L : ℕ} (M : Fin (L + 1) → ℕ) : ℕ := ∑ s, M s

/-- **The `ChainDimSplit` termination measure drops.** A reduction `S : ChainDimSplit M` strictly
decreases the total width: `Σ S.red < Σ M`. From `hsum` (`drop + red = M`) and `hdrops` (`0 < Σ drop`).
The well-founded measure for the iterated Route-M recursion (was inlined in `schur_straighten_of_data`;
named here as the reusable, split-construction-agnostic foundation). -/
theorem ChainDimSplit.redM_widthSum_lt {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) :
    chainWidthSum S.red < chainWidthSum M := by
  unfold chainWidthSum
  have hle : ∑ s, S.red s ≤ ∑ s, M s :=
    Finset.sum_le_sum fun s _ => by have := S.hsum s; omega
  have hne : ∑ s, S.red s ≠ ∑ s, M s := by
    intro hEq
    have hdrop0 : ∑ s, S.drop s = 0 := by
      have hadd : ∑ s, S.drop s + ∑ s, S.red s = ∑ s, M s := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun s _ => S.hsum s
      omega
    exact absurd hdrop0 (by have := S.hdrops; omega)
  omega

/-! ## The well-founded recursion carrier (rebased: replaces `RouteState`/`routeRel_wf`)

The iterated Route-M recursion descends over the width vector `M : Fin (L+1) → ℕ` (`L` fixed — the
`ChainDimSplit` reduction is width-only), terminating on `chainWidthSum`. `chainRel` is the strict
`ΣM`-decrease; `chainRel_wf` (its well-foundedness) is the carrier for the `WellFounded.fix` that builds
the chart family — the split-construction-agnostic recursion skeleton. Any `ChainDimSplit M`-driven step
descends along `chainRel` by `redM_widthSum_lt`, so the recursion is well-founded whoever constructs the
per-node split. -/

/-- The recursion's well-founded relation on width vectors (fixed `L`): strict `ΣM`-decrease. -/
def chainRel {L : ℕ} (N M : Fin (L + 1) → ℕ) : Prop := chainWidthSum N < chainWidthSum M

/-- `chainRel` is well-founded (pullback of `<` on `ℕ` along `chainWidthSum`). The carrier for the
iterated Route-M `WellFounded.fix`, replacing the parallel `routeRel_wf`. -/
theorem chainRel_wf {L : ℕ} : WellFounded (@chainRel L) :=
  InvImage.wf chainWidthSum wellFounded_lt

/-- A `ChainDimSplit M` descends along `chainRel` (its reduced widths are `chainRel`-below `M`). The
bridge from crux2's one-step split to the recursion's descent proof — the `WellFounded.fix` recursive
call on `S.red` is justified by this, independent of how `S` is constructed. -/
theorem ChainDimSplit.redM_chainRel {L : ℕ} {M : Fin (L + 1) → ℕ} (S : ChainDimSplit M) :
    chainRel S.red M :=
  S.redM_widthSum_lt

end DLNFibre.DLN.RLCT
