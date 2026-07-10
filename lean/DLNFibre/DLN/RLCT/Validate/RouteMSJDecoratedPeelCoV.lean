import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelCoV` — the peel CoV-Jacobian, isolated

**Thread `genm-decbuild`, working structure (route (b), controller-directed 2026-07-10).** This
module wires the whole R1-UPPER endgame `DecoratedPeelCoV → DecoratedPeelStep → ∀M
RouteMBoxThresholdFinite M = (□)`, and reduces the sole analytic gap to a PER-CHART residual via the
banked pivot-chart cover. It is the formaliser's WORKING structure — NOT for canonical integration
(the controller keeps canonical at `(□)`-modulo-`DecoratedPeelStep`, the sorry-free conditional of
`RouteMSJDecoratedRec`).

## The structure

* **`DecoratedPeelCoV`** (`Prop`): for every `≥ 3`-width `M`, box-finiteness of EVERY reduced chain
  `redChain t M` (all cuts `t`) implies box-finiteness of the trivial decoration on `M` below
  `carrierThreshold M = ½·minAdm M`. (`∀ t` — the pivot cover sums over all cuts.)
* **`decoratedPeelCoV_imp_decoratedPeelStep`** (sorry-free): `DecoratedPeelCoV → DecoratedPeelStep`,
  the driver's IH supplying every `redChain t M`.
* **`GammaPeelFromRedChain`** (`Prop`, the PER-CHART residual): from reduced-chain finiteness, each
  `gammaPeelIntegral M t ρ κ c' < ⊤` below `½·minAdm M`.
* **`decoratedPeelCoV_of_gammaPeel`** (sorry-free): `GammaPeelFromRedChain → DecoratedPeelCoV`, via
  the banked cover `sjBoundaryPeel` + `trivial_integral_eq`. The cover reduction is PROVED.
* **`gammaPeelFromRedChain := sorry`** — the SINGLE named gap (per-chart), consumed by
  `decoratedPeelCoV`, `decoratedPeelStep_of_coV`, `routeMBoxThresholdFinite_decorated`.

## The per-chart residual and the corner

`GammaPeelFromRedChain` is discharged per chart by the built CoV pipeline (absorption,
`lintegral_box_le_absorption`, radial, Γ-peel Regime-A/B, reduced-chain IH). Its `{B₀ ≠ 0}` part
follows once the Q_b rank-stratification (corner cover, Phase-2 piece 8) lands; the irreducible
`{B₀ = 0}` deeper corner strata (`{rank Q_b ≤ b−2}`, `b ≥ 2`) are the `DeeperStrataResolution`
gap (cornrev: the linchpin `minAdm ≤ corner-codim` is a tautology — codim ≠ finiteness-½codim), the
target of the peelcert deeper-strata resolution.

Axiom-clean for everything EXCEPT `gammaPeelFromRedChain` (and consumers), which carry `sorryAx` —
the one isolated per-chart gap, by design.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The load-bearing single-peel change-of-variables (the isolated gap).** For every `≥ 3`-width
chain `M`, box-finiteness of EVERY reduced chain `redChain t M` (one fewer layer, all cuts `t`)
implies box-finiteness of the trivial decoration on `M` below `carrierThreshold M`. The pivot-chart
cover (`sjBoundaryPeel`) sums over ALL cuts `t`, so each chart reduces to its own `redChain t M`;
the hypothesis quantifies over all `t`, not one binding cut. The content is the exact peel
CoV (radial blow-up + monomial Jacobian + fresh-block Schur `rowMix`, block-split identifying the
pivot block with `redChain t M`, Gram absorbed into the shared-divisor support, threshold shift
`½·peelCharge` inside the CoV) — an EXACT factoring, no Hölder split. -/
def DecoratedPeelCoV : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
    (∀ t : ℕ, RouteMBoxThresholdFinite (redChain t M)) →
    DecoratedBoxThresholdFinite (SJDecoration.trivial M)

/-- **The wiring — `DecoratedPeelCoV → DecoratedPeelStep` (sorry-free).** For a `≥ 3`-width chain
with box-finiteness of every one-shorter chain (the strong IH), the trivial decoration on `M` is
box-finite: every reduced chain `redChain t M` is one shorter, so the IH gives its box-finiteness,
which `DecoratedPeelCoV` consumes (over all cuts `t`). -/
theorem decoratedPeelCoV_imp_decoratedPeelStep (h : DecoratedPeelCoV) : DecoratedPeelStep := by
  intro L M hIH
  exact h M (fun t => hIH (redChain t M))

/-- **The per-chart peel residual (the gap after the cover reduction).** Given box-finiteness
of every reduced chain `redChain t M`, each pivot-chart integral `gammaPeelIntegral M t ρ κ c'`
is finite below `½·minAdm M`. This is the per-chart content the CoV pipeline delivers (absorption
`freedSchurLoss_absorption` + Jacobian `lintegral_box_le_absorption` + radial + Γ-peel Regime-A/B +
reduced-chain IH). Its `{B₀ ≠ 0}` part is dischargeable by the built CoV foundation once the Q_b
rank-stratification (corner cover, Phase-2 piece 8) lands; the irreducible `{B₀ = 0}` deeper corner
strata (`{rank Q_b ≤ b−2}`, `b ≥ 2`) are the genuine `DeeperStrataResolution` gap (cornrev: linchpin
`minAdm ≤ corner-codim` is a tautology — codim ≠ finiteness-to-½codim). -/
def GammaPeelFromRedChain : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
    (∀ t : ℕ, RouteMBoxThresholdFinite (redChain t M)) →
    ∀ (t : ℕ), 1 ≤ t → t ≤ min (M 0) (M 1) →
      ∀ (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : NNReal),
        (c' : ℝ) < (minAdm M : ℝ) / 2 →
        gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤

/-- **The cover reduction — `GammaPeelFromRedChain → DecoratedPeelCoV` (sorry-free).** The banked
pivot-chart cover `sjBoundaryPeel` bounds `routeMLayerBoxIntegral M` by the finite sum of per-chart
peeled integrals over all cuts `t ∈ Icc 1 (min M₀ M₁)`; each is finite by the residual (using the
reduced-chain finiteness), a finite sum of finite terms is finite. The trivial decoration's integral
IS `routeMLayerBoxIntegral M` (`trivial_integral_eq`); `carrierThreshold M = ½·minAdm M`. -/
theorem decoratedPeelCoV_of_gammaPeel (h : GammaPeelFromRedChain) : DecoratedPeelCoV := by
  intro L M hred c' hc'
  have hthr : (c' : ℝ) < (minAdm M : ℝ) / 2 := hc'
  rw [trivial_integral_eq M (c' : ℝ)]
  refine lt_of_le_of_lt (sjBoundaryPeel M c' hthr) ?_
  refine ENNReal.sum_lt_top.mpr (fun t ht => ?_)
  rw [Finset.mem_Icc] at ht
  refine ENNReal.sum_lt_top.mpr (fun ρ _ => ?_)
  refine ENNReal.sum_lt_top.mpr (fun κ _ => ?_)
  exact h M hred t ht.1 ht.2 ρ κ c' hthr

/-- **The per-chart residual (the isolated gap).** `gammaPeelFromRedChain : GammaPeelFromRedChain` —
the single named `sorry`. The cover reduction above is PROVED, so the gap is now per-chart (more
granular than `decoratedPeelCoV`). NOT for integration to canonical. -/
theorem gammaPeelFromRedChain : GammaPeelFromRedChain := by
  sorry

/-- **The peel CoV, on-branch (gated on the per-chart gap).** Composes the cover reduction with the
per-chart residual. -/
theorem decoratedPeelCoV : DecoratedPeelCoV :=
  decoratedPeelCoV_of_gammaPeel gammaPeelFromRedChain

/-- **The decorated single-peel step, on-branch (gated on one gap).** Composes `decoratedPeelCoV`
through the wiring. -/
theorem decoratedPeelStep_of_coV : DecoratedPeelStep :=
  decoratedPeelCoV_imp_decoratedPeelStep decoratedPeelCoV

/-- **`(□)` on-branch — `∀M, RouteMBoxThresholdFinite M`, gated on the one gap `decoratedPeelCoV`.**
Composes the decorated step through the T0 driver `routeMBoxThresholdFinite_of_decoratedPeel` (the
banked sorry-free arity recursion). This is the paper's `(□)`, unconditional on-branch modulo the
single isolated CoV-Jacobian `sorry`. -/
theorem routeMBoxThresholdFinite_decorated (M : Fin (L + 1) → ℕ) : RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_decoratedPeel decoratedPeelStep_of_coV M

end DLNFibre.DLN.RLCT
