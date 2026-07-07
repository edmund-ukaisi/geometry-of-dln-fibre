import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep
import DLNFibre.DLN.RLCT.Validate.Case222Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJTerminal` — the general-width `monomial × (unit ≥ 1)` terminal

**STEP-1 of the `SJState` recursion carrier** (`genm-sjcarrier2`; the R1-UPPER final gate). This module
verifies **option (a)** of the route-correction finding
(`expeditions/2026-06-20-aoyagi-full/threads/genm-sjclose/statement-card.md`): the `(2,2,2)`
`monomial × (unit ≥ 1)` terminal (`Case222Resolution.blockForm_step3` + `step3_unit_ge_one` +
`Case222Cover.integrableOn_monomial_mul_unit_iff`) **LIFTS to general (opaque `Fintype`) widths**.

The terminal of the pure `(S,J)` recursion — reached once the corank layers have been driven down by
`corankStep` — is a single accumulated radial monomial times a unit bounded below by a positive
constant, NOT the isotropic `frobSq Δ + W` peel (that needs the dead anisotropy-removing atom). The
three ingredients and their general-width status:

* **Monomial factoring** — `frobSq ((u • M) · Q) = u² · frobSq (M · Q)` (`RouteMSJCorankStep.frobSq_smul_mul`,
  banked, ALREADY general widths) and its accumulated-prefactor form (`corankStep_prefactor`).
* **Unit lower bound** — `frobSq (M · Q) ≥ (entry)²`: since `frobSq X = ∑ᵢⱼ Xᵢⱼ²` is a sum of nonneg
  squares, ANY entry square bounds it below (`frobSq_ge_sq_entry`). On the terminal chart the
  dehomogenised leading/pivot ("Plücker") coordinate is pinned to a unit (`|·| ≥ c₀ > 0`), so
  `frobSq (M · Q) ≥ c₀² > 0` (`frobSq_ge_of_entry`). This is the general-width mechanism behind the
  `(2,2,2)` `step3_unit_ge_one`'s `+ 1` (there the pinned entry is the `(0,0)` entry `= 1` of
  `[[1,0],[q,1]] · [[1,a1],[a2,a3]]`).
* **Terminal finiteness** — `monomialIntegrand d k h c' · |unit|^{−c'}` is integrable on the unit box
  below the monomial threshold (`terminal_monomial_mul_unit_integrable`), composing the banked
  `integrableOn_monomial_mul_unit_iff` (unit-factor threshold-invariance) with
  `monomialIntegrand_integrable_of_lt` (below-threshold monomial finiteness). Both banked lemmas are
  `d`-generic, so this half lifts to general widths UNCHANGED.

**VERDICT (STEP-1): option (a) LIFTS.** The monomial factoring is banked general-width; the unit lower
bound generalises cleanly as `frobSq X ≥ (entry)²`; the finiteness endpoint is `d`-generic. What is NOT
here — and is the STEP-2 carrier (the multi-week mountain) — is DRIVING `corankStep` down the layers to
REACH a terminal chart on which an entry of the residual is pinned to a unit (resolving the
rank-deficient-`Q_b` charts, the standing `L ≥ 3` recursion). This module supplies the terminal these
recursion charts land on and its finiteness; it does not itself perform the recursion.

S2-FREE: `frobSq_ge_sq_entry`/`frobSq_ge_of_entry`/the factoring are pure algebra;
`terminal_monomial_mul_unit_integrable` rides only the banked measure-theoretic bricks (no
`monomial_rlct`). Axiom footprint: the clean three `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators

/-! ## The general-width unit lower bound (`frobSq ≥ (entry)²`) -/

/-- **`frobSq` bounded below by any entry square.** For a matrix `M`, any entry: `(M i j)² ≤ frobSq M`
(`frobSq M = ∑ᵢⱼ Mᵢⱼ²` is a sum of nonneg squares containing `(M i j)²`). The general-width mechanism
behind `Case222Resolution.step3_unit_ge_one`. -/
theorem frobSq_ge_sq_entry {a b : Type*} [Fintype a] [Fintype b] (M : a → b → ℝ) (i : a) (j : b) :
    (M i j) ^ 2 ≤ frobSq M := by
  have h1 : (M i j) ^ 2 ≤ ∑ j', (M i j') ^ 2 :=
    Finset.single_le_sum (f := fun j' => (M i j') ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ j', (M i j') ^ 2) ≤ ∑ i', ∑ j', (M i' j') ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', (M i' j') ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg _)) (Finset.mem_univ i)
  exact le_trans h1 (by unfold frobSq; exact h2)

/-- **`frobSq` unit lower bound from a pinned entry.** If an entry has `|M i j| ≥ c₀ ≥ 0`, then
`frobSq M ≥ c₀²`. The general-width `unit ≥ c₀ > 0` mechanism at the terminal chart (the pinned
dehomogenised leading/Plücker coordinate). -/
theorem frobSq_ge_of_entry {a b : Type*} [Fintype a] [Fintype b] (M : a → b → ℝ) (i : a) (j : b)
    (c₀ : ℝ) (h : c₀ ≤ |M i j|) (hc₀ : 0 ≤ c₀) : c₀ ^ 2 ≤ frobSq M := by
  have hsq : c₀ ^ 2 ≤ (M i j) ^ 2 := by
    have habs := abs_nonneg (M i j)
    have hsqabs := sq_abs (M i j)
    nlinarith [h, hc₀, habs, hsqabs]
  exact le_trans hsq (frobSq_ge_sq_entry M i j)

/-- **`frobSq ≥ 1` from an entry `= 1`.** The general-width form of `step3_unit_ge_one`'s `+ 1`: a
terminal residual with a coordinate pinned to `1` (the dehomogenised leading/pivot coordinate) has
`frobSq ≥ 1`. -/
theorem frobSq_ge_one_of_entry_eq_one {a b : Type*} [Fintype a] [Fintype b]
    (M : a → b → ℝ) (i : a) (j : b) (h : M i j = 1) : (1 : ℝ) ≤ frobSq M := by
  have := frobSq_ge_sq_entry M i j
  rw [h] at this; simpa using this

/-! ## The general-width `monomial × (unit ≥ c₀²)` terminal (the `blockForm_step3` lift) -/

/-- **The general-width `monomial × (unit ≥ c₀²)` terminal (option (a), the `(2,2,2)` `blockForm_step3`
lift).** For a corank block `M`, downstream `Q`, single radial `u`: the loss factors as `u²` times the
unit `frobSq (M · Q)`, and on the terminal chart — where an entry of `M · Q` is pinned to `|·| ≥ c₀ > 0`
(the dehomogenised leading/Plücker coordinate) — the unit is bounded below by `c₀²`:

    frobSq ((u • M) · Q) = u² · frobSq (M · Q),   c₀² ≤ frobSq (M · Q).

`frobSq_smul_mul` (banked) + `frobSq_ge_of_entry`. The exact general-width analogue of the `(2,2,2)`
`blockForm_step3` (`= u² · unit`) + `step3_unit_ge_one` (`unit ≥ 1`): there the pinned entry is the
`(0,0)` entry `= 1` of `[[1,0],[q,1]] · [[1,a1],[a2,a3]]`. -/
theorem frobSq_terminal_radial {a m b : Type*} [Fintype a] [Fintype m] [Fintype b]
    (u : ℝ) (M : Matrix a m ℝ) (Q : Matrix m b ℝ) (i : a) (j : b) (c₀ : ℝ)
    (hpin : c₀ ≤ |(M * Q) i j|) (hc₀ : 0 ≤ c₀) :
    frobSq ((u • M) * Q) = u ^ 2 * frobSq (M * Q) ∧ c₀ ^ 2 ≤ frobSq (M * Q) :=
  ⟨frobSq_smul_mul u M Q, frobSq_ge_of_entry (M * Q) i j c₀ hpin hc₀⟩

/-- **The accumulated-prefactor terminal.** With the accumulated radial monomial `pref` (Aoyagi's
`∏ bᵢ²` from the earlier resolved layers), the terminal loss is `(pref · u²) · unit`, `unit =
frobSq (M · Q) ≥ c₀²`. This is the monomial × (unit ≥ c₀²) form the finiteness endpoint consumes; the
`pref` is carried through unchanged (the sequential-independence of `corankStep_prefactor`). -/
theorem frobSq_terminal_radial_prefactor {a m b : Type*} [Fintype a] [Fintype m] [Fintype b]
    (pref u : ℝ) (M : Matrix a m ℝ) (Q : Matrix m b ℝ) (i : a) (j : b) (c₀ : ℝ)
    (hpin : c₀ ≤ |(M * Q) i j|) (hc₀ : 0 ≤ c₀) :
    pref * frobSq ((u • M) * Q) = (pref * u ^ 2) * frobSq (M * Q) ∧ c₀ ^ 2 ≤ frobSq (M * Q) :=
  ⟨by rw [frobSq_smul_mul, ← mul_assoc], frobSq_ge_of_entry (M * Q) i j c₀ hpin hc₀⟩

/-! ## The terminal finiteness endpoint (the `d`-generic finiteness half) -/

/-- **The terminal chart integrand is integrable below the monomial threshold (general `d`).** The
resolved terminal integrand `monomialIntegrand d k h c' · |unit|^{−c'}` (Jacobian monomial × loss-base
`(−c')`-power × the bounded unit `|unit| ∈ [a,b]`, `a > 0`) is integrable on the unit box whenever
`c' < monomialThreshold d k h`. Composes the banked `integrableOn_monomial_mul_unit_iff` (unit-factor
threshold-invariance) with `monomialIntegrand_integrable_of_lt` (below-threshold monomial finiteness).
This is the finiteness endpoint of option (a); both banked lemmas are `d`-generic, so it lifts to
general widths unchanged. -/
theorem terminal_monomial_mul_unit_integrable (d : ℕ) (k h : Fin d → ℕ)
    (unit : (Fin d → ℝ) → ℝ) (c' : NNReal) (a b : ℝ) (ha : 0 < a) (hc'0 : 0 < c')
    (hmeas : Measurable unit)
    (hunit : ∀ᵐ u ∂(volume.restrict (unitBox d)), a ≤ |unit u| ∧ |unit u| ≤ b)
    (hthr : (c' : ℝ≥0∞) < monomialThreshold d k h) :
    IntegrableOn (fun u => monomialIntegrand d k h (c' : ℝ) u * |unit u| ^ (-(c' : ℝ)))
      (unitBox d) volume :=
  (integrableOn_monomial_mul_unit_iff d k h unit (unitBox d) (c' : ℝ) a b ha hmeas hunit).mpr
    (monomialIntegrand_integrable_of_lt d k h c' hc'0 hthr)

/-! ## Non-vacuity witnesses (the terminal mechanism is inhabited at general widths) -/

/-- **Non-vacuity of the packaged `frobSq_terminal_radial`** at the smallest genuine width (`Fin 2`),
`M̂ = [[1,a1],[a2,a3]]` the dehomogenised chart block, `Q = [[1,0],[0,1]]` the identity downstream: the
loss factors `= u² · frobSq (M̂ · Q)` and the unit `≥ 1²` (pinned `(0,0)` entry of `M̂ · Q` `= 1`). -/
example (u a1 a2 a3 : ℝ) :
    frobSq ((u • (!![(1 : ℝ), a1; a2, a3] : Matrix (Fin 2) (Fin 2) ℝ)) * !![(1 : ℝ), 0; 0, 1])
        = u ^ 2 * frobSq ((!![(1 : ℝ), a1; a2, a3] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, 1])
      ∧ (1 : ℝ) ^ 2
        ≤ frobSq ((!![(1 : ℝ), a1; a2, a3] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), 0; 0, 1]) :=
  frobSq_terminal_radial u _ _ 0 0 1
    (by rw [Matrix.mul_apply, Fin.sum_univ_two]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons])
    (by norm_num)

/-- **Non-vacuity: the `(2,2,2)` `step3_unit_ge_one` residual is a pinned-entry unit.** The step-3
block residual `(q·a1+a3)² + (q+a2)² + a1² + 1` is `frobSq` of the sheared chart block
`[[1, a1], [q+a2, q·a1+a3]]` (`= [[1,0],[q,1]] · [[1,a1],[a2,a3]]`), whose `(0,0)` entry is pinned to
`1` — so `frobSq_ge_one_of_entry_eq_one` recovers the `≥ 1` bound the `(2,2,2)` proof establishes by
`nlinarith`. Confirms the general-width `frobSq_ge_sq_entry` mechanism subsumes the `(2,2,2)` case. -/
example (q a1 a2 a3 : ℝ) :
    (1 : ℝ) ≤ frobSq (fun i j : Fin 2 => ![![(1 : ℝ), a1], ![q + a2, q * a1 + a3]] i j) :=
  frobSq_ge_one_of_entry_eq_one _ 0 0 (by simp)

end DLNFibre.DLN.RLCT
