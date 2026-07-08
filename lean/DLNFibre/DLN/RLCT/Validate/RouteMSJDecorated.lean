import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMSJLinGen
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated` — the decorated finiteness predicate (R1-UPPER)

**Thread `genm-sjbuild2`, the native decorated R-BLOWUP route → `sjJointResolution`.** The Lean-ready
encoding of the decorated finiteness predicate pinned by `genm-r1predicate/cert.md` (design FULLY PINNED,
decorrelated-Codex-confirmed) and gated by `genm-sjbuild2/step0-terminal-bridge.md` (STEP-0 GATE PASS:
the terminal count↔monomial bridge is uniform; the carrier threshold depends only on `remChain`, not the
decoration).

## The pinned design (what this module encodes)

The faithful decorated inductive object is the **generator-carrier loss predicate**, NOT the separable
`Wπ(u)·frobSq(prod(remChain))^{−c'}` weight-times-original-loss form (that drops the anisotropy `Γ·Q_b`
and the shared-divisor structure — the divergent pointwise route on the rank-deficient-`Q_b` locus). The
loss is the banked `SJLinGenState.loss` (`RouteMSJLinGen`): monomial-prefix × linear-residual, generator
by generator, with the shared-divisor support recorded per generator.

* **`carrierThreshold M = ½·minAdm M`** (piece 1) — the codim budget the recursion descends on.
* **`carrierThreshold_shift`** (piece 4) — the banked soundness cast: `carrierThreshold M − ½·peelCharge
  M u ≤ carrierThreshold (redChain u M)` (= `half_minAdm_sub_half_peelCharge_le`, banked `0/171`), so a
  coupling exponent `c' < carrierThreshold M` shifted by `½·peelCharge` stays below the reduced threshold.
* **`SJDecoration M`** (piece 2) — the buildable decoration: the banked `SJLinGenState` carrier (shared-
  divisor support + linear residual) + the accumulated Jacobian-exponent vector `jac` + the integration
  domain (deeper/active params). **NOT** a `det(Q_b Q_bᵀ)` Gram field (the atom trap).
* **`DecoratedBoxThresholdFinite M D`** (piece 3) — the load-bearing inductive statement: below
  `carrierThreshold M`, the accumulated Jacobian monomial times the CARRIER loss to the `−c'` integrates
  finitely over the chart domain.
* **`SJDecoration.trivial M`** + **`decoratedBoxThresholdFinite_trivial_iff`** (piece 7 base) — at `d = 0`
  (no exceptional coordinates, `jac` empty, carrier = the identity `ofMatrix` at the full product), the
  decorated integral IS `routeMLayerBoxIntegral M c' 1`, so the predicate LITERALLY recovers
  `RouteMBoxThresholdFinite M`. This is the π=∅ consumer's foundation, proved sorry-free.

## What is NOT here (the remaining mountain — pieces 5/6, reported precisely)

The genuinely-new CoV — `decorated_peel_step` (clear-first scalar Schur elimination → radial attach →
block split → regime A/B, INCLUDING the `c' = pq/2` boundary ε-argument) and the full well-founded
recursion discharging `sjJointResolution` — is the ~65–75% genuinely-new construction (decorrelated
Codex, `genm-sjcarrier4/scope-answer.md`). It is UNBANKED and multi-tide. `sjJointResolution`
(`RouteMSJResolution`) stays the single named analytic sorry, UNTOUCHED, until the recursion genuinely
lands. This module supplies the validated ENCODING (structures + predicate + soundness cast + π=∅
recovery) the mountain builds on.

S2-FREE: definitions + banked casts + measure-plumbing for the `d = 0` collapse; no `monomial_rlct`,
no `cited_aoyagi_dln`. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Piece 1/4 — the carrier threshold and its banked soundness shift -/

/-- **The carrier threshold** `carrierThreshold M = ½·minAdm M` — HALF the minimal admissible codim
of the (remaining) chain. The exponent budget the decorated recursion descends on (verified
`= Θ(M,π)` in `genm-r1predicate/cert.md`, `3592/3592`). -/
noncomputable def carrierThreshold (M : Fin (L + 1) → ℕ) : ℝ := (minAdm M : ℝ) / 2

/-- **The carrier-threshold soundness shift (piece 4).** A coupling exponent below the parent
threshold, shifted down by `½·peelCharge`, stays below the reduced-chain threshold:
`carrierThreshold M − ½·peelCharge M u ≤ carrierThreshold (redChain u M)`. This is the banked
`half_minAdm_sub_half_peelCharge_le` (soundness gate `0/171`), cast into the `carrierThreshold`
abbreviation — the subordination the recursion hands to the strong IH at the reduced chain. -/
theorem carrierThreshold_shift (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) :
    carrierThreshold M - (peelCharge M u : ℝ) / 2 ≤ carrierThreshold (redChain u M) := by
  unfold carrierThreshold
  exact half_minAdm_sub_half_peelCharge_le M u hu

/-- **The carrier threshold is nonnegative.** -/
theorem carrierThreshold_nonneg (M : Fin (L + 1) → ℕ) : 0 ≤ carrierThreshold M := by
  unfold carrierThreshold; positivity

/-! ## Piece 2 — the decoration (the generator carrier + accumulated Jacobian + chart domain) -/

/-- **The buildable decoration (native R-BLOWUP / Aoyagi `diag(b)`).** The banked `SJLinGenState`
carrier (shared-divisor support `supp` + linear-residual `coeff`, generator by generator) together with
the accumulated Jacobian-exponent vector `jac : Fin d → ℕ` and the integration domain (the deeper/active
params `Z` restricted to `dom`, mapped into the carrier's spectator/active inputs by `ctx`). It is the
generator-carrier the anisotropy + shared-divisor facts FORCE — NOT a `det(Q_b Q_bᵀ)` Gram atom and NOT a
scalar `diag(b)` weight (a scalar cannot express the `min_i` over `supp`, `RouteMSJLedger` DATA-A). -/
structure SJDecoration {L : ℕ} (M : Fin (L + 1) → ℕ) : Type 1 where
  /-- The number of accumulated exceptional coordinates. -/
  d : ℕ
  /-- Spectator (absorbed-gauge / downstream) index type. -/
  ζ : Type
  /-- Still-active linear-variable index type. -/
  ν : Type
  /-- Generator index type. -/
  ι : Type
  /-- `Fintype` on the active variables (the residual sum ranges over `ν`). -/
  fν : Fintype ν
  /-- `Fintype` on the generators (the loss sum ranges over `ι`). -/
  fι : Fintype ι
  /-- The generator carrier: shared-divisor support + linear residual. -/
  carrier : SJLinGenState ζ ν ι d
  /-- The accumulated resolution-Jacobian exponent vector `h`. -/
  jac : Fin d → ℕ
  /-- The deeper/active parameter space integrated over. -/
  Z : Type
  /-- The measure structure on the deeper space. -/
  mZ : MeasureSpace Z
  /-- How a deeper-param point supplies the carrier's `(spectator, active)` inputs. -/
  ctx : Z → ζ × (ν → ℝ)
  /-- The chart domain of the resolved-so-far coordinates. -/
  dom : Set Z
  /-- **Measurability of the carrier residual in the deeper parameter.** For each generator `i`, the
  linear-residual value `residual (ctx z).1 (ctx z).2 i` is a measurable function of `z`. The spectator
  index type `ζ` carries no measurable structure and `coeff : ζ → ι → ν → ℝ` is arbitrary, so this must
  be recorded on the carrier — it is the honest measurability datum the decorated box-integral factoring
  (Tonelli / `lintegral_const_mul`) needs; from it the decorated loss `decLoss` is jointly measurable in
  `(z, u)` (the exceptional monomial prefix is continuous in `u`). -/
  residualMeas :
    letI : MeasureSpace Z := mZ
    letI : Fintype ν := fν
    ∀ i : ι, Measurable (fun z : Z => carrier.residual (ctx z).1 (ctx z).2 i)

/-- **The decorated loss at a point** — the carrier loss `SJLinGenState.loss` evaluated at the
exceptional coordinates `u`, in the deeper-param context `z` (via `ctx`). Faithful by construction: it
IS `carrier.loss`, never `frobSq(prod(remChain))` times a detached weight. -/
noncomputable def SJDecoration.decLoss (D : SJDecoration M) (u : Fin D.d → ℝ) (z : D.Z) : ℝ :=
  letI := D.fν; letI := D.fι
  D.carrier.loss u (D.ctx z).1 (D.ctx z).2

/-! ## Piece 3 — the decorated finiteness predicate -/

/-- **The decorated box-integral** below exponent `c'`: the accumulated Jacobian monomial
`∏_ℓ |u_ℓ|^{jac_ℓ}` times the CARRIER loss to the `−c'`, integrated over the exceptional coordinates
(`unitBox d`) and the deeper params (`dom`). The weight and the loss are NOT separable in the original
matrices — the `u` are the exceptional coordinates shared INTO `carrier.loss` (they factor cleanly only
at the terminal, post `sjLoss_factor`). -/
noncomputable def SJDecoration.integral (D : SJDecoration M) (c' : ℝ) : ℝ≥0∞ :=
  letI := D.mZ
  ∫⁻ z in D.dom, ∫⁻ u in unitBox D.d,
    ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c'))

/-- **The decorated finiteness predicate (the load-bearing inductive statement).** Below the carrier
threshold `carrierThreshold M = ½·minAdm M`, the decorated box-integral is finite. Specialises to the
original product-loss finiteness `RouteMBoxThresholdFinite M` at the trivial decoration (`π = ∅`), and to
the pure-monomial terminal at the fully-resolved leaf. -/
def DecoratedBoxThresholdFinite (D : SJDecoration M) : Prop :=
  ∀ c' : NNReal, (c' : ℝ) < carrierThreshold M → D.integral (c' : ℝ) < ⊤

/-! ## Piece 7 base — the trivial decoration and the π=∅ recovery (`RouteMBoxThresholdFinite`) -/

/-- **The trivial decoration at `π = ∅`.** No exceptional coordinates (`d = 0`, `jac` empty), the
identity `ofMatrix` carrier at the full layer product `prod M A` (support `≡ 0`), integration domain
the raw parameter box `paramsBoxM M 1`. The `ctx` reads the product entries as the active variables,
so the carrier loss is exactly `frobSq (prod M A)`. -/
noncomputable def SJDecoration.trivial (M : Fin (L + 1) → ℕ) : SJDecoration M where
  d := 0
  ζ := Unit
  ν := Fin (M 0) × Fin (M (Fin.last L))
  ι := Fin (M 0) × Fin (M (Fin.last L))
  fν := inferInstance
  fι := inferInstance
  carrier := SJLinGenState.ofMatrix (M 0) (M (Fin.last L))
  jac := ![]
  Z := Params M
  mZ := inferInstance
  ctx := fun A => ((), fun ik => prod M A ik.1 ik.2)
  dom := paramsBoxM M 1
  residualMeas := by
    haveI : OpensMeasurableSpace (Params M) :=
      inferInstanceAs (OpensMeasurableSpace
        (∀ s : Fin L, Fin (M s.castSucc) → Fin (M s.succ) → ℝ))
    intro ik
    simp only [SJLinGenState.residual_ofMatrix]
    exact ((continuous_prod M).matrix_elem ik.1 ik.2).measurable

/-- **The trivial decoration's loss IS the product loss.** `decLoss (trivial M) u A =
frobSq (prod M A)` for every `A` — the `ofMatrix` carrier at the product entries collapses (support
`≡ 0`, so every generator monomial is `1`; the residuals read off the entries). Via `loss_ofMatrix`. -/
theorem trivial_decLoss (M : Fin (L + 1) → ℕ) (u : Fin 0 → ℝ) (A : Params M) :
    (SJDecoration.trivial M).decLoss u A = frobSq (prod M A) := by
  unfold SJDecoration.decLoss SJDecoration.trivial
  simp only
  rw [SJLinGenState.loss_ofMatrix (M 0) (M (Fin.last L)) u
        (fun ik => prod M A ik.1 ik.2)]

/-- **The unit box in dimension `0` has full measure `1`** (empty product of `Icc 0 1` lengths). -/
theorem volume_unitBox_zero : (volume : Measure (Fin 0 → ℝ)) (unitBox 0) = 1 := by
  rw [unitBox, volume_pi_pi]
  simp

/-- **The π=∅ recovery (piece 7 base, the encoding validation).** The trivial decoration's integral
IS the layer-product box integral: `(trivial M).integral c' = routeMLayerBoxIntegral M c' 1`. The
inner `unitBox 0` integral collapses (empty Jacobian monomial `= 1`, full measure `1`), and the
carrier loss is `frobSq (prod M A)` (`trivial_decLoss`) — so the decorated object LITERALLY reduces
to the original target. -/
theorem trivial_integral_eq (M : Fin (L + 1) → ℕ) (c' : ℝ) :
    (SJDecoration.trivial M).integral c' = routeMLayerBoxIntegral M (c' : ℝ) 1 := by
  rw [SJDecoration.integral, routeMLayerBoxIntegral]
  refine setLIntegral_congr_fun (measurableSet_paramsBoxM M 1) (fun A _ => ?_)
  -- inner: the integrand is constant in `u` (`d = 0`, empty monomial), = `frobSq (prod M A)`.
  have h1 : ∀ u : Fin (SJDecoration.trivial M).d → ℝ,
      ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ ((SJDecoration.trivial M).jac ℓ))
          * ((SJDecoration.trivial M).decLoss u A) ^ (-c'))
        = ENNReal.ofReal ((frobSq (prod M A)) ^ (-c')) := by
    intro u
    rw [trivial_decLoss M u A, Finset.prod_eq_one (fun i (_ : i ∈ Finset.univ) => i.elim0), one_mul]
  rw [lintegral_congr h1, setLIntegral_const,
    show (SJDecoration.trivial M).d = 0 from rfl, volume_unitBox_zero, mul_one]

/-- **The predicate recovers `RouteMBoxThresholdFinite` at `π = ∅`.** `DecoratedBoxThresholdFinite
(trivial M) ↔ RouteMBoxThresholdFinite M` — the thresholds coincide (`carrierThreshold M =
½·minAdm M`) and the integrals coincide (`trivial_integral_eq`). The π=∅ consumer's foundation:
the decorated recursion, once it lands `DecoratedBoxThresholdFinite (trivial M)`, delivers
`RouteMBoxThresholdFinite M` with NO residual gap. -/
theorem decoratedBoxThresholdFinite_trivial_iff (M : Fin (L + 1) → ℕ) :
    DecoratedBoxThresholdFinite (SJDecoration.trivial M) ↔ RouteMBoxThresholdFinite M := by
  unfold DecoratedBoxThresholdFinite RouteMBoxThresholdFinite carrierThreshold
  constructor
  · intro h c' hc'
    have := h c' hc'
    rwa [trivial_integral_eq M (c' : ℝ)] at this
  · intro h c' hc'
    rw [trivial_integral_eq M (c' : ℝ)]
    exact h c' hc'

/-! ## Piece 5 sub-brick — the Case-2 radial attach at the decoration level (the CLEAR-FIRST radial)

The single radial factor of one decorated peel, lifted to the decoration. This is the (b)
attach-radial half of `decorated_peel_step` — the fresh fully-shared exceptional divisor `u₀`,
attached AFTER the clear-first scalar Schur elimination (the (a) `rowMix R` at constant support,
which carries the chart's analytic matrix `R` and is the deferred half). The generator-level
`loss_radialStep` (banked) threads through: attaching the radial multiplies the loss by `u₀²`. -/

/-- **The Case-2 radial attach on a decoration.** Prepend a fresh fully-shared exceptional divisor
(`d ↦ d+1`, `carrier ↦ radialStep`, `jac ↦ Fin.cons j₀`); the deeper data (`ζ ν ι`, domain, `ctx`)
is unchanged. The `radialStep` records the new divisor as shared by EVERY generator (order `1`) —
the `corankStep` `u²` factor made visible per generator (`RouteMSJLinGen`). NOT the full `extend`
(which additionally applies the clear-first `rowMix R` for the chart's Schur matrix `R`; that
analytic half is the deferred mountain). -/
noncomputable def SJDecoration.radialAttach (D : SJDecoration M) (j₀ : ℕ) : SJDecoration M where
  d := D.d + 1
  ζ := D.ζ
  ν := D.ν
  ι := D.ι
  fν := D.fν
  fι := D.fι
  carrier := D.carrier.radialStep
  jac := Fin.cons j₀ D.jac
  Z := D.Z
  mZ := D.mZ
  ctx := D.ctx
  dom := D.dom
  residualMeas := D.residualMeas

/-- **The radial attach multiplies the decorated loss by `u₀²`.** `(radialAttach D j₀).decLoss
(u₀ ::: u) z = u₀² · D.decLoss u z` — the generator-level `loss_radialStep` lifted to the
decoration. The fresh divisor is shared by all generators, so it factors cleanly out of the sum of
squares; this is the passive-prefactor identity the peel step's regime lemmas consume (the `u₀²`
the exponent shift `c' ↦ c' − ½·pq` acts on). -/
theorem radialAttach_decLoss (D : SJDecoration M) (j₀ : ℕ) (u₀ : ℝ) (u : Fin D.d → ℝ) (z : D.Z) :
    (D.radialAttach j₀).decLoss (Fin.cons u₀ u) z = u₀ ^ 2 * D.decLoss u z := by
  letI := D.fν; letI := D.fι
  unfold SJDecoration.decLoss SJDecoration.radialAttach
  exact D.carrier.loss_radialStep u₀ u (D.ctx z).1 (D.ctx z).2

/-- **The radial attach raises the exceptional count by one, recording the fresh shared divisor.**
`(radialAttach D j₀).d = D.d + 1`, and the fresh divisor's shared-divisor exponent is `1` (it
divides every generator to order `1`) — the DATA-A record a scalar weight cannot express. -/
theorem radialAttach_d (D : SJDecoration M) (j₀ : ℕ) : (D.radialAttach j₀).d = D.d + 1 := rfl

/-! ## Non-vacuity — a genuinely non-trivial (d = 1) decoration inhabitant -/

/-- **Non-vacuity of the radial attach.** From the trivial `(3,3,4)` decoration, attaching a single
Case-2 radial with Jacobian exponent `3` (the `pq = 4` front block, `jac = pq − 1 = 3`) gives a
decoration with `d = 1` and decorated loss `u₀² · frobSq (prod M A)` — a genuinely non-trivial
inhabitant exercising the radial machinery (not the degenerate `d = 0` case), on the STEP-0 anchor. -/
example (u₀ : ℝ) (u : Fin 0 → ℝ) (A : Params (![3, 3, 4] : Fin 3 → ℕ)) :
    ((SJDecoration.trivial (![3, 3, 4] : Fin 3 → ℕ)).radialAttach 3).decLoss (Fin.cons u₀ u) A
      = u₀ ^ 2 * frobSq (prod (![3, 3, 4] : Fin 3 → ℕ) A) := by
  rw [radialAttach_decLoss, trivial_decLoss]

end DLNFibre.DLN.RLCT
