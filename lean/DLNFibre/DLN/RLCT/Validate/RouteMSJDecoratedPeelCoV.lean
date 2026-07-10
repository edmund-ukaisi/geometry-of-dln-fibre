import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelCoV` — the peel CoV-Jacobian, isolated

**Thread `genm-decbuild`, working structure (route (b), controller-directed 2026-07-10).** This
module isolates the SOLE remaining analytic content of `(□)` to ONE named, sorry-carrying Lean
statement, `DecoratedPeelCoV`, and wires the whole endgame modulo it: `DecoratedPeelCoV →
DecoratedPeelStep → ∀M RouteMBoxThresholdFinite M` = `(□)`.

**This module carries the ONE named `sorry` (`decoratedPeelCoV`).** It is the formaliser's WORKING
structure — NOT for integration to canonical (the controller keeps canonical at
`(□)`-modulo-`DecoratedPeelStep`, the clean sorry-free conditional of `RouteMSJDecoratedRec`). The
`sorry` is the target of a decorrelated pen-and-paper (witness seat: exhibit the descent + exact
Jacobian + reduced-loss = `redChain`-decoration on the `(2,2,1)` bottleneck, then generalize;
obstruction fallback: a scoped no-go + sufficient conditions). The formaliser fills the `sorry` from
the resulting certificate.

## The isolated gap

* **`DecoratedPeelCoV`** — the load-bearing single-peel change-of-variables, as a `Prop`. For every
  `≥ 3`-width chain `M` there is a binding cut `t ≤ min(M₀,M₁)` such that: IF the REDUCED chain
  `redChain t M` (one fewer layer) is box-finite (`RouteMBoxThresholdFinite`), THEN the trivial
  decoration on `M` is box-finite below `carrierThreshold M = ½·minAdm M`.

  The content packed into its proof (the `sorry`, the pen-and-paper's target) is the EXACT peel
  change of variables: the radial blow-up of the front factor `A₀` on the rank-`t` chart (a monomial
  Jacobian), the fresh-block Schur `rowMix` (`R = A⁻¹·B`, `hsh` free post-radial), and the
  block-split IDENTIFYING the pivot block's product with `redChain t M`'s product. The threshold
  shift `c' ↦ c' − ½·peelCharge M t` (which keeps `c'` below the reduced threshold, banked
  `carrierThreshold_shift`) lives INSIDE the CoV, so the clean full-threshold box-finiteness of
  `redChain t M` is the exact hypothesis the parent needs. The Gram weight
  `det(Q_b Q_bᵀ)^{−(M₀−t)/2}` is ABSORBED into the carrier's shared-divisor support (never a
  detached det-Gram field), so the peel is an EXACT monomial factoring — no Hölder split — evading
  binding-cut saturation `minAdm M = peelCharge + minAdm(redChain t M)` that makes a black-box IH
  bound infeasible.

* **`decoratedPeelCoV_imp_decoratedPeelStep`** — the wiring (sorry-free): `DecoratedPeelCoV →
  DecoratedPeelStep`. The strong IH the arity recursion supplies covers `redChain t M` (one
  shorter), which is exactly the hypothesis `DecoratedPeelCoV`'s implication consumes.

* **`decoratedPeelCoV` / `routeMBoxThresholdFinite_decorated`** — the endgame gated on the one gap:
  `decoratedPeelCoV : DecoratedPeelCoV := sorry` is the single named analytic hole; composing it
  through the wiring + the T0 driver `routeMBoxThresholdFinite_of_decoratedPeel` gives `∀M,
  RouteMBoxThresholdFinite M` = `(□)`, on-branch, gated on that one `sorry`.

Axiom-clean for everything EXCEPT `decoratedPeelCoV` (and its consumers), which carry `sorryAx` —
the one isolated gap, by design.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The load-bearing single-peel change-of-variables (the isolated gap).** For every `≥ 3`-width
chain `M` there is a binding cut `t ≤ min(M₀,M₁)` such that box-finiteness of the reduced chain
`redChain t M` implies box-finiteness of the trivial decoration on `M` below `carrierThreshold M`.
The content is the exact peel CoV (radial blow-up + monomial Jacobian + fresh-block Schur `rowMix`,
block-split identifying the pivot block with `redChain t M`, Gram absorbed into the shared-divisor
support, threshold shift `½·peelCharge` inside the CoV) — an EXACT factoring, no Hölder split. -/
def DecoratedPeelCoV : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
    ∃ t : ℕ, t ≤ min (M 0) (M 1) ∧
      (RouteMBoxThresholdFinite (redChain t M) →
        DecoratedBoxThresholdFinite (SJDecoration.trivial M))

/-- **The wiring — `DecoratedPeelCoV → DecoratedPeelStep` (sorry-free).** For a `≥ 3`-width chain
with box-finiteness of every one-shorter chain (the strong IH), the trivial decoration on `M` is
box-finite: pick the binding cut `t` from `DecoratedPeelCoV`; the reduced chain `redChain t M` is
one shorter, so the IH supplies its box-finiteness, which the peel implication consumes. -/
theorem decoratedPeelCoV_imp_decoratedPeelStep (h : DecoratedPeelCoV) : DecoratedPeelStep := by
  intro L M hIH
  obtain ⟨t, _ht, himp⟩ := h M
  exact himp (hIH (redChain t M))

/-- **The isolated analytic gap (pen-and-paper target).** `decoratedPeelCoV : DecoratedPeelCoV`
— the single named `sorry`. Everything else in the R1-UPPER `(□)` chain is proved sorry-free modulo
this one statement. NOT for integration to canonical (the controller keeps canonical at
`(□)`-modulo-`DecoratedPeelStep`). -/
theorem decoratedPeelCoV : DecoratedPeelCoV := by
  sorry

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
