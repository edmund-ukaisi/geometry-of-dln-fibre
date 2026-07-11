import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated
import DLNFibre.DLN.RLCT.Validate.RouteMSJJointReduce

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec` — the decorated-recursion driver (R1-UPPER)

**Thread `genm-decbuild`, the native decorated R-BLOWUP route → `(□)`.** Tile 0: turn the prose
`decorated_peel_step` recursion into a **proved conditional**. This module STATES the single
remaining analytic contract as a Lean `Prop` (`DecoratedPeelStep`) and proves — sorry-free, MODULO
that one `Prop` — the general-`L` box-finiteness `∀M, RouteMBoxThresholdFinite M` = the paper's
`(□)`, plus the per-chart peel finiteness that `sjJointResolution` (`RouteMSJResolution:803`) needs.
It re-architects the R1-UPPER endgame: `(□)` is now gated on the DECORATED single-peel `Prop`,
descending on chain arity via `redChain` — NOT on the gammaPeel `sjJointResolution` sorry (which
becomes retro-fillable via the built bridge `sjJointResolution_of_boxThresholdFinite`).

## What this module establishes (all sorry-free)

* **`DecoratedPeelStep`** — the SOLE remaining analytic contract, stated once. For every `≥ 3`-width
  chain `M`, GIVEN box-finiteness `RouteMBoxThresholdFinite` for every one-shorter chain (the strong
  IH), the TRIVIAL decoration on `M` is finite below `carrierThreshold M = ½·minAdm M`. Its eventual
  proof is ONE decorated peel at the binding cut `u★`: clear-first scalar Schur elim (`rowMix`, tile
  T2) → radial attach (`radialAttach`, banked T3) → block-split regime A/B incl. the `c' = pq/2`
  boundary (tile T4), landing on `redChain u★ M` at threshold shifted by `½·peelCharge`
  (`carrierThreshold_shift`, banked), then the one-shorter IH closes it. The `Prop` is phrased via
  `DecoratedBoxThresholdFinite (trivial M)` (not `RouteMBoxThresholdFinite M`) precisely so the
  prover unfolds the decoration and peels it.

* **`decoratedPeelStep_imp_sjStepHyp`** — `DecoratedPeelStep → SJStepHyp`, via the banked π=∅
  recovery `decoratedBoxThresholdFinite_trivial_iff`. The decorated step delivers the
  gammaPeel-route step contract.

* **`routeMBoxThresholdFinite_of_decoratedPeel`** — the driver: `DecoratedPeelStep → ∀L, ∀M,
  RouteMBoxThresholdFinite M` = `(□)` MODULO the one `Prop`. Reuses the banked sorry-free wrapper
  `routeMBoxThresholdFinite_of_step` (strong induction on chain arity) with the `L = 1` free-matrix
  Morse base `sjBase1_freeMatrix` (banked). NO analytic content of its own.

* **`gammaPeelIntegral_lt_top_of_decoratedPeel`** — the decorated route discharges the exact
  `sjJointResolution` obligation: `DecoratedPeelStep` ⟹ every per-`(t,ρ,κ)`-chart peeled integral is
  finite below threshold, via the built bridge `sjJointResolution_of_boxThresholdFinite`
  (`RouteMSJJointReduce`). Shows `803` is obsolete (retro-fillable), without touching it.

## The sole gap after this tile

`DecoratedPeelStep` is the ONLY open analytic content of the R1-UPPER `(□)` chain. Everything above
it is proved here sorry-free and axiom-clean. Later tiles discharge it: T2 the analytic-`R`
`rowMix`, T3 the radial wiring (banked `radialAttach_integral`), T4 the block-split regime A/B (the
genuinely-new heart), T5 the terminal base — the arity-2 leaf of the driver is already the banked
free-matrix Morse `sjBase1_freeMatrix`, so the single peel + one-shorter IH close each `≥ 3`-width
chain WITHOUT an internal recursion.

S2-FREE: definitions + banked compositions; no `monomial_rlct`, no `cited_aoyagi_dln`. Axiom-clean
`[propext, Classical.choice, Quot.sound]` for every unconditional statement here.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## The single decorated-peel contract (`decorated_peel_step`, the sole analytic gap) -/

/-- **The decorated single-peel contract (`decorated_peel_step`).** For every `≥ 3`-width chain `M`,
GIVEN box-finiteness `RouteMBoxThresholdFinite` for every one-shorter chain (the strong IH the arity
recursion supplies), the TRIVIAL decoration on `M` is finite below its carrier threshold
`carrierThreshold M = ½·minAdm M`.

This is the SOLE remaining analytic content of the R1-UPPER `(□)`. Its intended proof is ONE
decorated peel at the binding cut `u★ ≤ min(M₀,M₁)` (`exists_binding_cut`): the clear-first scalar
Schur elimination (`SJDecoration`/`rowMix`), the radial attach (`radialAttach`, multiplying the loss
by `u₀²`), and the block-split regime A/B (the `c' = pq/2` boundary correctly excluded by strict
`c' < ½·minAdm`), landing the reduced integrand on `redChain u★ M` at threshold shifted down by
`½·peelCharge M u★` (`carrierThreshold_shift`) — where the one-shorter IH
`RouteMBoxThresholdFinite (redChain u★ M)` closes it. The peel descends chain arity by one
(`redChain` has one fewer layer), so it is NON-circular: it does not route through
`sjJointResolution`. -/
def DecoratedPeelStep : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ),
    (∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M') →
    DecoratedBoxThresholdFinite (SJDecoration.trivial M)

/-! ## The driver — `(□)` PROVED MODULO `DecoratedPeelStep` -/

/-- **The decorated step delivers the `(S,J)` step contract.** `DecoratedPeelStep → SJStepHyp`: for
a `≥ 3`-width chain with box-finiteness of every one-shorter chain, box-finiteness of `M` holds —
because the decorated trivial-decoration finiteness IS `RouteMBoxThresholdFinite M` (the banked π=∅
recovery `decoratedBoxThresholdFinite_trivial_iff`). -/
theorem decoratedPeelStep_imp_sjStepHyp (h : DecoratedPeelStep) : SJStepHyp := by
  intro L M hIH
  exact (decoratedBoxThresholdFinite_trivial_iff M).mp (h M hIH)

/-- **The decorated-recursion driver — `(□)` MODULO `DecoratedPeelStep`.** Given the single
decorated-peel contract, the general-`L` box-finiteness `RouteMBoxThresholdFinite M` holds for every
width vector `M`. Reuses the banked sorry-free wrapper `routeMBoxThresholdFinite_of_step` (strong
induction on chain arity: `L = 0` vacuous, `L = 1` the free-matrix Morse base `sjBase1_freeMatrix`,
`L ≥ 2` the decorated step), carrying NO analytic content of its own. This is the paper's `(□)`,
proved modulo the one stated analytic `Prop`. -/
theorem routeMBoxThresholdFinite_of_decoratedPeel (h : DecoratedPeelStep) :
    ∀ {L : ℕ} (M : Fin (L + 1) → ℕ), RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_step (decoratedPeelStep_imp_sjStepHyp h) sjBase1_freeMatrix

/-! ## The decorated route discharges the `sjJointResolution` obligation (803 is obsolete) -/

/-- **The decorated route closes the exact `sjJointResolution` goal.** Given `DecoratedPeelStep`,
every per-`(t,ρ,κ)`-chart peeled integral `gammaPeelIntegral M t ρ κ c'` is finite below
`½·minAdm M`. Composes the driver (box-finiteness of the SAME chain `M`) with the built monotonicity
bridge `sjJointResolution_of_boxThresholdFinite` (`RouteMSJJointReduce`,
`gammaPeelIntegral ≤ box integral`). This is the sorry at `RouteMSJResolution:803` — shown OBSOLETE
(retro-fillable) by the decorated route, without touching it. -/
theorem gammaPeelIntegral_lt_top_of_decoratedPeel (h : DecoratedPeelStep)
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤ :=
  sjJointResolution_of_boxThresholdFinite M
    (routeMBoxThresholdFinite_of_decoratedPeel h M) t ρ κ c' hc'

/-! ## The Q2-CORRECTED DECORATED recursion — `DecoratedDescent` (the plain-IH `DecoratedPeelStep`
above is now DEAD)

**genm-sj5-descent, cover §7.5 audit Q2 (task #141).** The plain-IH `DecoratedPeelStep` above is a
sound-but-DEAD conditional: its antecedent `∀M', RouteMBoxThresholdFinite M'` (a PLAIN, undecorated IH)
is UNPROVABLE for the peel. cover's Q2 finding: the peel emits `[reduced integrand]·[truncated H⁻⁴]`,
and at the zero-slack binding cut (`c'−½peelCharge ↗ ½·minAdm(redChain)`) a plain reduced-chain IH has
NO budget for the extra Gram weight `H⁻⁴`. So the induction hypothesis must be DECORATED — carrying the
truncated Gram weight through the `SJDecoration` carrier (jac monomial + shared-divisor structure). This
is exactly what `SJDecoration`/`DecoratedBoxThresholdFinite` (`RouteMSJDecorated`) were built for; the
plain-IH `DecoratedPeelStep` under-used them.

This section re-states the contract as a DECORATED recursion, ABSTRACTING the admissibility predicate
`adm` so the driver is fully mechanical (def-independent). The SPECIFIC admissible family — the
base-audit fidelity core (`genm-sj5-cover` audits its def + base before the full spine proof is trusted)
— is supplied separately (untracked until audited); it must (i) contain `SJDecoration.trivial`, (ii) be
peel-closed, (iii) have a provable leaf base (`sjLoss_terminal` + free-matrix Morse). `DecoratedDescent`
bundles the three; `routeMBoxThresholdFinite_of_decoratedDescent` discharges `(□)` modulo it.
S2-FREE: definitions + mechanical arity strong-induction + the banked π=∅ recovery. -/

/-- **The DECORATED inductive STEP contract, parameterised by an admissibility predicate `adm`.** For a
`≥ 3`-width chain `M`, GIVEN the DECORATED strong IH — box-finiteness for every `adm`-admissible
decoration of every one-shorter chain — every `adm`-admissible decoration of `M` is finite below its
carrier threshold. The decorated replacement for the plain `SJStepHyp`: the IH carries the truncated
Gram weight `H⁻⁴` inside the `SJDecoration` (jac + carrier), which the plain IH could not (Q2). -/
def DecoratedStepHyp (adm : ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), SJDecoration M → Prop) : Prop :=
  ∀ (L : ℕ) (M : Fin (L + 1 + 1 + 1) → ℕ),
    (∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D') →
    ∀ (D : SJDecoration M), adm (L + 1 + 1) M D → DecoratedBoxThresholdFinite D

/-- **The DECORATED leaf base contract (`L = 1`, single free matrix).** Every `adm`-admissible
decoration of every two-width chain is finite below its carrier threshold. The decorated replacement for
`SJBaseHyp`: stronger than the plain free-matrix Morse base — the fully-resolved admissible members are
the banked monomial terminal `sjLoss_terminal_lintegral_lt_top`. -/
def DecoratedBaseHyp (adm : ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), SJDecoration M → Prop) : Prop :=
  ∀ (M : Fin (1 + 1) → ℕ) (D : SJDecoration M), adm 1 M D → DecoratedBoxThresholdFinite D

/-- **The DECORATED-recursion driver (mechanical, `adm`-abstract).** Strong induction on chain arity:
`n = 0` vacuous (`carrierThreshold = ½·minAdm = 0`, decoration-independent), `n = 1` the decorated leaf
base, `n ≥ 2` the decorated step (its decorated strong IH is the induction hypothesis one arity lower).
Carries NO analytic content — mirrors `routeMBoxThresholdFinite_of_step`, one level up (decorated). -/
theorem decoratedBoxThresholdFinite_of_decoratedStep
    {adm : ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), SJDecoration M → Prop}
    (hstep : DecoratedStepHyp adm) (hbase : DecoratedBaseHyp adm) :
    ∀ (n : ℕ) (M : Fin (n + 1) → ℕ) (D : SJDecoration M),
      adm n M D → DecoratedBoxThresholdFinite D := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · -- `n = 0`: threshold `½·minAdm M = 0`, so `c' < 0` is unsatisfiable (vacuous).
      intro M D _hD c' hc'
      exfalso
      have h0 : minAdm M = 0 := by
        have hz : ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat = 0 := by
          obtain ⟨T, _, hT⟩ := Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)
          rw [hT]; simp [Mval]
        unfold minAdm; exact hz
      rw [carrierThreshold, h0] at hc'
      simp only [Nat.cast_zero, zero_div] at hc'
      exact absurd hc' (not_lt.mpr c'.coe_nonneg)
    · -- `n = 1`: the decorated leaf base.
      intro M D hD; exact hbase M D hD
    · -- `n = k + 2`: the decorated step, fed the one-arity-lower decorated IH.
      intro M D hD
      exact hstep k M (fun M' D' hD' => ih (k + 1) (by omega) M' D' hD') D hD

/-- **`(□)` from the decorated step + base + trivial-admissibility (mechanical).** Specialises the
decorated driver to the trivial decoration (admissible by `htriv`) and recovers the plain box-finiteness
via the banked π=∅ recovery `decoratedBoxThresholdFinite_trivial_iff`. -/
theorem routeMBoxThresholdFinite_of_decoratedStep
    {adm : ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), SJDecoration M → Prop}
    (htriv : ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), adm n M (SJDecoration.trivial M))
    (hstep : DecoratedStepHyp adm) (hbase : DecoratedBaseHyp adm) :
    ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), RouteMBoxThresholdFinite M := by
  intro n M
  exact (decoratedBoxThresholdFinite_trivial_iff M).mp
    (decoratedBoxThresholdFinite_of_decoratedStep hstep hbase n M
      (SJDecoration.trivial M) (htriv n M))

/-- **The Q2-corrected sole analytic contract `DecoratedDescent`.** There EXISTS an admissibility
predicate `adm` that (i) contains the trivial decoration, (ii) supports the decorated step, and (iii)
supports the decorated leaf base. The `SJDecoration`-faithful replacement for the (now-dead) plain
`DecoratedPeelStep` — the truncated Gram weight `H⁻⁴` rides in `adm`'s carrier/jac. The remaining
analytic mountain is EXHIBITING such an `adm` (the base-audit fidelity core + the decorated peel proof
`DecoratedStepHyp`). -/
def DecoratedDescent : Prop :=
  ∃ adm : ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), SJDecoration M → Prop,
    (∀ (n : ℕ) (M : Fin (n + 1) → ℕ), adm n M (SJDecoration.trivial M)) ∧
      DecoratedStepHyp adm ∧ DecoratedBaseHyp adm

/-- **The DECORATED-recursion driver — `(□)` MODULO `DecoratedDescent`.** Given the Q2-corrected
decorated contract, `RouteMBoxThresholdFinite M` holds for every width vector `M`. This RE-POINTS the
`(□)` chain off the dead plain `routeMBoxThresholdFinite_of_decoratedPeel` (whose `DecoratedPeelStep`
antecedent is unprovable, Q2) onto the decorated recursion. Mechanical — the analytic content is entirely
in `DecoratedDescent`. -/
theorem routeMBoxThresholdFinite_of_decoratedDescent (h : DecoratedDescent) :
    ∀ (n : ℕ) (M : Fin (n + 1) → ℕ), RouteMBoxThresholdFinite M := by
  obtain ⟨adm, htriv, hstep, hbase⟩ := h
  exact routeMBoxThresholdFinite_of_decoratedStep htriv hstep hbase

end DLNFibre.DLN.RLCT
