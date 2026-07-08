import DLNFibre.DLN.RLCT.Validate.RouteMSJLinGen
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge
import DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec` — the decorated R1-UPPER recursion (predicate layer)

**Thread `genm-sjbuild`, R1-UPPER CoV mountain → `sjJointResolution`.** The Lean-ready encoding of the
decorated finiteness recursion, per the pinned design certificate
(`expeditions/2026-06-20-aoyagi-full/threads/genm-r1predicate/cert.md`, decorrelated-Codex-confirmed) and
the STEP-0 verify-first gate (`threads/genm-sjbuild/step0-terminal-bridge.md`, GATE PASS).

## What this module supplies (the predicate layer — pieces 1, 3, 4)

The recursion is indexed by the **current (remaining) chain** `N` (the outer spine
`routeMBoxThresholdFinite_of_step` already does arity strong-induction on `N`, so the profile is implicit;
`N = remChain π`). This module supplies:

* **`carrierThreshold N = ½·minAdm N`** (piece 1) — the count-level RLCT budget of the remaining chain,
  the `c' <` bound of the decorated predicate.
* **`carrierThreshold_shift`** (piece 4) — the peel-charge soundness cast: one peel drops the budget by
  `½·peelCharge` and stays `≤` the reduced chain's budget. This is the banked
  `half_minAdm_sub_half_peelCharge_le` (`0/171`) in the recursion's terms; the exponent-shift
  `c' ↦ c' − ½·peelCharge` (regime A, `matBox_corank_residual_absZ_le`) lands below the reduced threshold.
* **`SJDecoration` / `DecoratedBoxThresholdFinite`** (pieces 2, 3, DEFINITIONS) — the shared-divisor
  GENERATOR-CARRIER predicate (the `SJLinGenState.loss`, NOT a separable Gram weight — the r1predicate
  headline; the separable form is the divergent pointwise route). The load-bearing inductive object.

## What this module does NOT yet supply (the mountain — pieces 5, 6, 7, reported precisely)

The genuinely-new CoV plumbing (~65–75% new, r1predicate/decorrelated-Codex): `decorated_peel_step`
(piece 5 — the anisotropy removal `frobSq(C·Qt+Γ·Q_b) ⤳ frobSq D + W'` at opaque widths, clear-first
ordering, the `c' = pq/2` boundary ε-argument), `decorated_base` (piece 6 — the terminal + the
count↔monomial bridge), and `routeMBoxThresholdFinite_of_decorated` (piece 7 — the `π = ∅` consumer that
discharges `sjJointResolution`). Those consume the banked bricks pinned in the `APIPins` section below.

**STEP-0 finding carried here (build-plan-relevant):** the three named anchors `(3,3,4)`, `(2,2,2,2)`,
`(3,3,3,4)` are ENTIRELY regime-A/B + free-matrix (no rank-deficient chart), so the monomial terminal
`sjLoss_terminal` is never reached on them — the bridge holds vacuously, threshold EXACTLY `½·minAdm`.
The monomial terminal is load-bearing only on rank-deficient chains (e.g. `(3,4,2)`); there the bridge
is banked at the model level by `routeLayerAtlas_value` (`⨅ over leaves monomialThreshold = ½·minAdm`).

S2-FREE: pure order algebra on `minAdm`/`peelCharge` + the carrier definitions; axiom-clean
`[propext, Classical.choice, Quot.sound]`. No `monomial_rlct`, no `cited_aoyagi_dln`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-! ## Piece 1 — the carrier threshold (the count-level RLCT budget of the remaining chain) -/

/-- **The carrier threshold** `carrierThreshold N = ½·minAdm N` — the count-level RLCT budget of the
remaining chain `N`, the `c' <` bound of the decorated finiteness predicate. At the root (`N = M`) it is
`½·minAdm M`, the geometric threshold `RouteMBoxThresholdFinite M` gates on. -/
noncomputable def carrierThreshold (N : Fin (L + 1) → ℕ) : ℝ := (minAdm N : ℝ) / 2

/-- The carrier threshold is nonnegative (`minAdm ≥ 0`). -/
theorem carrierThreshold_nonneg (N : Fin (L + 1) → ℕ) : 0 ≤ carrierThreshold N := by
  unfold carrierThreshold; positivity

/-- **The peel-charge soundness cast (piece 4).** One decorated peel at a legal cut `u` drops the carrier
budget by `½·peelCharge M u` and stays at or below the reduced chain's budget:

    carrierThreshold M − ½·peelCharge M u  ≤  carrierThreshold (redChain u M).

So a coupling exponent `c' < carrierThreshold M`, shifted by `½·peelCharge` (regime A,
`matBox_corank_residual_absZ_le`), stays `< carrierThreshold (redChain u M)` — the subordination the
decorated recursion hands to the reduced chain. The banked `half_minAdm_sub_half_peelCharge_le` (`0/171`)
in the recursion's terms. -/
theorem carrierThreshold_shift (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) :
    carrierThreshold M - (peelCharge M u : ℝ) / 2 ≤ carrierThreshold (redChain u M) :=
  half_minAdm_sub_half_peelCharge_le M u hu

/-! ## Non-vacuity — the binding-cut charge decompositions (STEP-0 arithmetic, Lean-certified) -/

/-- **Non-vacuity W1 — `(3,3,4)` binding cut `t = 1`.** The front peel emits block charge
`peelCharge = 4` (a genuine `2×2` corank block, `pq = 4`) and reduces to `(1,4)` with `minAdm = 4`; the
sum `4 + 4 = 8 = minAdm (3,3,4)` is the binding equality (the soundness gate is TIGHT here). The primary
inhabitant: a genuine `pq = 4` block, the regime-A exponent shift, a free-matrix terminal. -/
theorem binding_334 :
    peelCharge (![3, 3, 4] : Fin 3 → ℕ) 1 + minAdm (redChain 1 (![3, 3, 4] : Fin 3 → ℕ)) = 8
      ∧ minAdm (![3, 3, 4] : Fin 3 → ℕ) = 8 := by
  refine ⟨?_, by decide⟩
  decide

/-- **Non-vacuity W2 — `(2,2,2,2)` front binding cut `t = 1`.** The front peel emits block charge
`peelCharge = 1` (`1×1` corank) and reduces to `(1,2,2)` with `minAdm = 2`; `1 + 2 = 3 = minAdm (2,2,2,2)`
is binding. The multi-peel depth witness (two nested peels to a Morse leaf). -/
theorem binding_2222 :
    peelCharge (![2, 2, 2, 2] : Fin 4 → ℕ) 1 + minAdm (redChain 1 (![2, 2, 2, 2] : Fin 4 → ℕ)) = 3
      ∧ minAdm (![2, 2, 2, 2] : Fin 4 → ℕ) = 3 := by
  refine ⟨?_, by decide⟩
  decide

/-- **The carrier threshold at the anchors** (the `c' <` budgets the recursion runs against). -/
theorem carrierThreshold_334 : carrierThreshold (![3, 3, 4] : Fin 3 → ℕ) = 4 := by
  unfold carrierThreshold; rw [show minAdm (![3, 3, 4] : Fin 3 → ℕ) = 8 from by decide]; norm_num

theorem carrierThreshold_2222 : carrierThreshold (![2, 2, 2, 2] : Fin 4 → ℕ) = 3 / 2 := by
  unfold carrierThreshold; rw [show minAdm (![2, 2, 2, 2] : Fin 4 → ℕ) = 3 from by decide]; norm_num

/-! ## Pieces 2, 3 — the decoration + the decorated finiteness predicate (the load-bearing shape)

The r1predicate HEADLINE (decorrelated-Codex-confirmed): the faithful decorated inductive object is the
shared-divisor GENERATOR-CARRIER loss `SJLinGenState.loss`, NOT the separable
`Wπ(u)·frobSq(prod(remChain))^{−c'}` weight-form (that drops the anisotropic `Γ·Q_b` coupling + the
shared-divisor structure — the divergent pointwise route on the rank-deficient-`Q_b` locus). The
decoration carries, generator-by-generator, which exceptional divisor divides which generator
(`carrier.supp`) and the accumulated Jacobian exponents (`jac`). -/

/-- **The decoration** at the remaining chain `N`: the banked shared-divisor generator carrier
`SJLinGenState` (support map + linear residual, generator-by-generator) together with the accumulated
Jacobian-exponent vector `jac : Fin d → ℕ`, over a chart domain `dom` in the spectator×active
parameters. The `d` accumulated exceptional coordinates live on `unitBox d`; the spectator `ζ` (deeper
params) and active `ν` (current block) carry the measure. NOT a scalar `diag(b)` weight and NOT a
`det(Q_b Q_bᵀ)` Gram atom — the shared-divisor faithfulness lives in `carrier.supp` (the `min_i`,
`sharedDivisorExp`), which a scalar/Gram weight cannot express (r1predicate DATA-A). -/
structure SJDecoration {L : ℕ} (_N : Fin (L + 1) → ℕ) : Type 1 where
  /-- Number of accumulated exceptional coordinates (blow-up divisors). -/
  d : ℕ
  /-- Spectator/unit parameters (the downstream product, absorbed gauge); a value type with a measure. -/
  ζ : Type
  /-- Still-active linear-variable INDEX (the current block; `x : ν → ℝ` are its coordinates). -/
  ν : Type
  /-- Generator index. -/
  ι : Type
  /-- Measure on the spectator parameter values. -/
  instMζ : MeasureSpace ζ
  /-- The active block is a finite matrix (its coordinate index `ν` is finite). -/
  instFν : Fintype ν
  /-- The generators are finitely indexed. -/
  instFι : Fintype ι
  /-- The shared-divisor generator carrier (support map + linear residual). -/
  carrier : SJLinGenState ζ ν ι d
  /-- The accumulated resolution-Jacobian exponent vector `h` (the `Wπ` monomial weight). -/
  jac : Fin d → ℕ
  /-- The chart domain the carrier loss integrates over: spectator value × active coordinates. -/
  dom : Set (ζ × (ν → ℝ))

attribute [instance] SJDecoration.instMζ SJDecoration.instFν SJDecoration.instFι

/-- **The decorated finiteness predicate (the load-bearing inductive statement, piece 3).** Below the
carrier threshold `½·minAdm N`, the accumulated Jacobian monomial `∏_ℓ |u_ℓ|^{jac ℓ}` times the CARRIER
loss to the `−c'` integrates finitely over the chart domain and the accumulated exceptional coordinates
`unitBox d`. The loss is `SJLinGenState.loss` — the resolved-so-far monomial-prefix × linear-residual
per generator — NOT `frobSq(original reduced product)`. The weight `∏ u^{jac}` and the loss are NOT
separable-in-the-original-matrices: the `u` are shared into `carrier.loss` via `carrier.supp`; they
factor cleanly only after `sjLoss_factor` at the terminal. -/
def DecoratedBoxThresholdFinite {L : ℕ} (N : Fin (L + 1) → ℕ) (D : SJDecoration N) : Prop :=
  ∀ c' : NNReal, (c' : ℝ) < carrierThreshold N →
    ∫⁻ z in D.dom,
        (∫⁻ u in unitBox D.d,
          ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ))
            * (D.carrier.loss u z.1 z.2) ^ (-(c' : ℝ)))) < ⊤

/-! ## API pins — durable contracts for the banked bricks the mountain (pieces 5/6/7) consumes

Confirm the exact statements the CoV plumbing rides on exist with the expected types. Kept as durable
contracts (`docs/policies/statement-cards.md` / the `pre-stage API` discipline). -/

section APIPins

-- Piece 4 soundness gate (the ℕ form the threshold cast is built on).
example (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : u ≤ min (M 0) (M 1)) :
    minAdm M ≤ peelCharge M u + minAdm (redChain u M) :=
  minAdm_le_peelCharge_add_redChain M u hu

-- Piece 5 (peel step) regime A: the high-exponent shift `c' ↦ c' − pq/2` on a strictly-positive core.
example {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : (p * q : ℝ) / 2 < c') (T : ℝ) (hT : 0 < T)
    (W : Ω → ℝ) (hWpos : ∀ z, 0 < W z) (Z : Set Ω) :
    ∫⁻ z in Z, (∫⁻ D in matBox p q T, ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume) ∂μ
      ≤ ENNReal.ofReal (Cresid (p * q) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((W z) ^ (-(c' - (p * q : ℝ) / 2))) ∂μ :=
  matBox_corank_residual_absZ_le hp hq μ c' hc' T hT W hWpos Z

-- Piece 5/6 regime B: the low-exponent Morse dominance (any non-negative core; the terminate branch).
example {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : c' < (p * q : ℝ) / 2) (hc0 : 0 ≤ c') (T : ℝ) (hT : 0 < T)
    (W : Ω → ℝ) (hWnn : ∀ z, 0 ≤ W z) (Z : Set Ω) (hZ : μ Z < ⊤) :
    ∫⁻ z in Z, (∫⁻ D in matBox p q T, ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume) ∂μ < ⊤ :=
  matBox_corank_dominates_absZ_lt_top hp hq μ c' hc' hc0 T hT W hWnn Z hZ

-- Piece 6 monomial terminal: the shared-divisor normal-crossing endpoint (needs a dehomogenised gen).
example {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ} (e : SJSupport ι d) (h : Fin d → ℕ) (c' : NNReal)
    (hc'0 : 0 < c') (i₀ : ι) (h0 : ∀ ℓ, e i₀ ℓ = sharedDivisorExp e ℓ)
    (hthr : (c' : ℝ≥0∞) < monomialThreshold d (sharedDivisorExp e) h) :
    ∫⁻ u in unitBox d, ENNReal.ofReal ((sjLoss e u) ^ (-(c' : ℝ)) * (∏ ℓ, |u ℓ| ^ (h ℓ))) < ⊤ :=
  sjLoss_terminal_lintegral_lt_top e h c' hc'0 i₀ h0 hthr

-- Piece 7 base connection: the matrix-product loss IS the fresh carrier loss (the `π = ∅` entry point).
example {p n q : ℕ} (u : Fin 0 → ℝ) (A0 : Fin p → Fin n → ℝ) (Q : Fin n → Fin q → ℝ) :
    (SJLinGenState.ofMatrix p q).loss u () (fun ik => rmatMul A0 Q ik.1 ik.2) = frobSq (rmatMul A0 Q) :=
  SJLinGenState.loss_ofMatrix_product u A0 Q

end APIPins

end DLNFibre.DLN.RLCT
