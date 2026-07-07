import DLNFibre.DLN.RLCT.Validate.RouteMSJTerminal

/-!
# `RouteMSJLedger` — the SJState shared-divisor support map (STEP-2 carrier)

**STEP-2 of the `SJState` recursion carrier** (thread `genm-sjcarrier3`; the R1-UPPER final gate →
`sjJointResolution`). Defines the carrier's **shared-divisor SUPPORT MAP** — the ledger the
adjudication (`pure-vs-atom-adj.md` / `chart-lemma-probe.md`, verdict A: the pure R-BLOWUP avoids
the atom's Gram wall) identified as the load-bearing datum — and proves it lands EXACTLY on the
banked terminal `monomialIntegrand`/`monomialThreshold` finiteness endpoint.

## The carrier

On the fully-resolved terminal normal-crossing chart of Aoyagi's `(S,J)` resolution, the loss is
`∑ᵢ bᵢ(u)²` where each generator `bᵢ` is a MONOMIAL in the exceptional divisors `u₁,…,u_d`:
`bᵢ(u) = ∏_ℓ |u_ℓ|^{e(i,ℓ)}`. The **support map** `e : ι → Fin d → ℕ` records to what order each
exceptional divisor `u_ℓ` divides each generator `bᵢ` — i.e. *which generators SHARE a divisor*.

**Why the support map is NECESSARY (the adjudication's key correction, DATA-A).** Two generators
sharing a divisor give a different RLCT than fresh-per-generator divisors: `⟨δx,δy⟩` (shared `δ`,
`e = [[1,1,0],[1,0,1]]` over `[δ,x,y]`) has common-divisor exponent `k_δ = min(1,1) = 1`, so
`∑bᵢ² = δ²(x²+y²)` (value ½); the fresh `⟨δ₁x,δ₂y⟩` has every `k_ℓ = 0`, so `∑bᵢ² = δ₁²x²+δ₂²y²`
(value 1). The `min_i` over the support matrix is exactly what separates them (`sharedDivisorExp`).
A threshold-only invariant that forgot the shared support undercounts (fresh-per-block gives ½→1).

## What lands here (this module)

The **common-divisor extraction** and its bridge to the banked terminal:

* `sharedDivisorExp e ℓ = ⨅ᵢ e(i,ℓ)` (the exponent of `u_ℓ` in the common monomial divisor `g`);
* `sjLoss e u = ∑ᵢ (genMonomial e i u)²`, the terminal loss;
* `sjLoss_factor` : `sjLoss e u = (commonDivisor e u)² · sjLoss (residualSupport e) u` (the common
  monomial factors out exactly — pure Nat-power algebra, `pow_add` + product distributivity);
* `sjLoss_terminal_integrand` : the terminal integrand `(sjLoss e u)^{−c'}·(∏_ℓ |u_ℓ|^{h_ℓ})` EQUALS
  the banked `monomialIntegrand d (sharedDivisorExp e) h c' u · |unit u|^{−c'}`, `unit = sjLoss
  (residualSupport e)` — the ledger's terminal loss lands on the banked terminal with the
  monomial exponent `k = sharedDivisorExp e` (the shared-divisor exponent): the support map's output
  IS the `k` of the finiteness endpoint;
* `sjLoss_terminal_lintegral_lt_top` : consequently, below the monomial threshold and given a
  dehomogenised chart generator (`∃ i₀, residual = 0`), the terminal loss integrand is `< ⊤`.

## The Case-2 ledger step (grounded Phase-2 slice, `prependColumn`)

The single-radial factor of the `(S,J)` step, lifted to the GENERATOR level (`prependColumn`,
`genMonomial_prependColumn`, `sjLoss_prependColumn_one`): a fresh divisor `u₀` enters each generator
to order `a i` (Case-2 full block `a ≡ 1`: every generator shares `u₀`), so the loss factors
`sjLoss = u₀²·(reduced)` — the generator-level form of `corankStep`'s `frobSq((u•Δ)·Q) = u²·frobSq`,
now with the sharing RECORDED (`sharedDivisorExp_prependColumn_one_zero`: fresh exponent `= 1`) and
old divisors PRESERVED (`sharedDivisorExp_prependColumn_succ`: the passive-prefactor invariant) —
answering Codex's "frobSq too coarse" for the radial-factor sub-step (the shared divisor IS visible
at the generator level).

## What is NOT here (Phase 2/3, deferred — reported precisely)

This module supplies the carrier, its terminal endpoint, and the Case-2 radial ledger step. It does
NOT build the block-elimination half of the step (the `Z`-independent unit reduction
`Case111`/`Case222` at opaque widths, at the generator level — the corank DECREMENT that transforms
the generators, not merely factors the radial), the Case-1 partial-block merge, the RECURSION down
the `(S,J)` profile to the terminal, nor the measure assembly into `gammaPeelIntegral < ⊤`.
Decorrelated Codex (this thread) flagged the sharp risk on those: the banked frobSq-level bricks
(`corankStep_prefactor`: `pref·frobSq = pref·u²·residual`) are TOO COARSE to recover the support
matrix through the block elimination — shared-divisor faithfulness there must be tracked
**generator-by-generator**. That block-elimination step, the recursion, and the assembly are the
remaining mountain.

S2-FREE: pure monomial algebra + the banked terminal measure bricks (no `monomial_rlct`). Axiom
footprint: the clean three `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The shared-divisor support map and its derived monomials -/

/-- **The shared-divisor support map.** `e i ℓ` = the exponent to which the exceptional divisor
`u_ℓ` divides the generator `bᵢ` on the terminal normal-crossing chart. Generators are indexed by a
nonempty `ι`; exceptional divisors by `Fin d`. The load-bearing ledger of the `(S,J)` carrier. -/
abbrev SJSupport (ι : Type*) (d : ℕ) : Type _ := ι → Fin d → ℕ

variable {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ}

/-- **The common-divisor exponent** `k_ℓ = min_i e(i,ℓ)`: the exponent of `u_ℓ` in the common
monomial divisor `g = ∏_ℓ |u_ℓ|^{k_ℓ}`. The `k` argument fed to the banked `monomialIntegrand`; the
`min_i` is exactly what distinguishes shared from fresh divisors (DATA-A). -/
def sharedDivisorExp (e : SJSupport ι d) (ℓ : Fin d) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => e i ℓ)

/-- **The generator monomial** `bᵢ(u) = ∏_ℓ |u_ℓ|^{e(i,ℓ)}`. -/
def genMonomial (e : SJSupport ι d) (i : ι) (u : Fin d → ℝ) : ℝ := ∏ ℓ, |u ℓ| ^ (e i ℓ)

/-- **The common monomial divisor** `g(u) = ∏_ℓ |u_ℓ|^{k_ℓ}`, `k_ℓ = sharedDivisorExp`. -/
def commonDivisor (e : SJSupport ι d) (u : Fin d → ℝ) : ℝ := ∏ ℓ, |u ℓ| ^ (sharedDivisorExp e ℓ)

/-- **The residual support** after factoring the common divisor: `e'(i,ℓ) = e(i,ℓ) − k_ℓ` (nonneg,
since `k_ℓ ≤ e(i,ℓ)`). The reduced ledger whose common divisor is trivial. -/
def residualSupport (e : SJSupport ι d) : SJSupport ι d := fun i ℓ => e i ℓ - sharedDivisorExp e ℓ

/-- **The terminal loss** `sjLoss e u = ∑ᵢ bᵢ(u)²` — the normal-crossing shape the pure `(S,J)`
recursion lands on. -/
def sjLoss (e : SJSupport ι d) (u : Fin d → ℝ) : ℝ := ∑ i, (genMonomial e i u) ^ 2

/-! ## The common-divisor extraction (pure Nat-power algebra) -/

/-- **The common-divisor exponent is a lower bound.** `sharedDivisorExp e ℓ ≤ e i ℓ` for every
generator `i` — it is the minimum over generators. -/
theorem sharedDivisorExp_le (e : SJSupport ι d) (i : ι) (ℓ : Fin d) :
    sharedDivisorExp e ℓ ≤ e i ℓ := by
  unfold sharedDivisorExp
  exact Finset.inf'_le (f := fun i => e i ℓ) (Finset.mem_univ i)

/-- **`sharedDivisorExp` over two generators is the `min`.** The `Fin 2` evaluation used by the
non-vacuity witnesses (DATA-A shared vs fresh). -/
theorem sharedDivisorExp_fin_two {d : ℕ} (e : SJSupport (Fin 2) d) (ℓ : Fin d) :
    sharedDivisorExp e ℓ = min (e 0 ℓ) (e 1 ℓ) := by
  unfold sharedDivisorExp
  apply le_antisymm
  · exact le_min (Finset.inf'_le (f := fun i => e i ℓ) (Finset.mem_univ 0))
      (Finset.inf'_le (f := fun i => e i ℓ) (Finset.mem_univ 1))
  · refine Finset.le_inf' _ _ (fun i _ => ?_)
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _

/-- **The generator monomial factors through the common divisor.**
`bᵢ(u) = g(u) · bᵢ'(u)`, `bᵢ' = genMonomial (residualSupport e)`. Exact Nat-power algebra: split
each `|u_ℓ|^{e(i,ℓ)} = |u_ℓ|^{k_ℓ}·|u_ℓ|^{e−k}` (`pow_add`, `k_ℓ ≤ e(i,ℓ)`) and distribute the
product. No division — valid even at `u_ℓ = 0`. -/
theorem genMonomial_factor (e : SJSupport ι d) (i : ι) (u : Fin d → ℝ) :
    genMonomial e i u = commonDivisor e u * genMonomial (residualSupport e) i u := by
  unfold genMonomial commonDivisor residualSupport
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  have hle := sharedDivisorExp_le e i ℓ
  rw [← pow_add,
    show sharedDivisorExp e ℓ + (e i ℓ - sharedDivisorExp e ℓ) = e i ℓ from by omega]

/-- **The terminal loss factors out the common-divisor square.**
`∑ᵢ bᵢ² = g² · ∑ᵢ (bᵢ')²`, the common monomial `g` pulled out of the sum of squares. -/
theorem sjLoss_factor (e : SJSupport ι d) (u : Fin d → ℝ) :
    sjLoss e u = (commonDivisor e u) ^ 2 * sjLoss (residualSupport e) u := by
  unfold sjLoss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [genMonomial_factor e i u, mul_pow]

/-- **The common-divisor square is the doubled-exponent monomial** `g² = ∏_ℓ |u_ℓ|^{2 k_ℓ}` —
matching the `(∏ |u_j|^{2 k_j})` factor of the banked `monomialIntegrand`. -/
theorem commonDivisor_sq (e : SJSupport ι d) (u : Fin d → ℝ) :
    (commonDivisor e u) ^ 2 = ∏ ℓ, |u ℓ| ^ (2 * sharedDivisorExp e ℓ) := by
  unfold commonDivisor
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun ℓ _ => ?_)
  rw [← pow_mul, Nat.mul_comm]

omit [Nonempty ι] in
/-- **The terminal loss is nonnegative** (a sum of squares). -/
theorem sjLoss_nonneg (e : SJSupport ι d) (u : Fin d → ℝ) : 0 ≤ sjLoss e u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-! ## The terminal bridge to the banked `monomialIntegrand` endpoint -/

/-- **The terminal bridge (EXACT).** The ledger's terminal loss integrand — the loss
`(sjLoss e u)^{−c'}` weighted by the resolution Jacobian monomial `∏_ℓ |u_ℓ|^{h_ℓ}` — is EXACTLY the
banked terminal integrand `monomialIntegrand d (sharedDivisorExp e) h c' u · |unit u|^{−c'}` with
`unit = sjLoss (residualSupport e)` the residual (`≥ 0`) unit factor and the monomial exponent
`k = sharedDivisorExp e` (the shared-divisor exponent). This is the load-bearing connection: the
support map's `min_i` output IS the `k` of the finiteness endpoint. `sjLoss_factor` +
`commonDivisor_sq` + `Real.mul_rpow` (`g² ≥ 0`, `unit ≥ 0`). -/
theorem sjLoss_terminal_integrand (e : SJSupport ι d) (h : Fin d → ℕ) (c' : ℝ) (u : Fin d → ℝ) :
    (sjLoss e u) ^ (-c') * (∏ ℓ, |u ℓ| ^ (h ℓ))
      = monomialIntegrand d (sharedDivisorExp e) h c' u
          * |sjLoss (residualSupport e) u| ^ (-c') := by
  have hU : 0 ≤ sjLoss (residualSupport e) u := sjLoss_nonneg _ _
  have hG2 : 0 ≤ ∏ ℓ, |u ℓ| ^ (2 * sharedDivisorExp e ℓ) :=
    Finset.prod_nonneg (fun ℓ _ => pow_nonneg (abs_nonneg _) _)
  have hfac : sjLoss e u
      = (∏ ℓ, |u ℓ| ^ (2 * sharedDivisorExp e ℓ)) * sjLoss (residualSupport e) u := by
    rw [sjLoss_factor, commonDivisor_sq]
  rw [hfac, Real.mul_rpow hG2 hU, abs_of_nonneg hU]
  unfold monomialIntegrand
  ring

/-- **The residual unit `≥ 1` at a dehomogenised generator.** If a generator `i₀` is the chart's
dehomogenised coordinate — its residual support is identically `0` (`e i₀ ℓ = k_ℓ`) — then
`bᵢ₀'(u) = 1`, so the residual unit `sjLoss (residualSupport e) u ≥ 1`. The general-width analogue
of `step3_unit_ge_one`'s pinned-`1` coordinate (`frobSq_ge_one_of_entry_eq_one`). -/
theorem sjLoss_residual_ge_one (e : SJSupport ι d) (i₀ : ι)
    (h0 : ∀ ℓ, e i₀ ℓ = sharedDivisorExp e ℓ) (u : Fin d → ℝ) :
    1 ≤ sjLoss (residualSupport e) u := by
  have hi0 : genMonomial (residualSupport e) i₀ u = 1 := by
    unfold genMonomial residualSupport
    refine Finset.prod_eq_one (fun ℓ _ => ?_)
    rw [h0 ℓ, Nat.sub_self, pow_zero]
  calc (1 : ℝ) = (genMonomial (residualSupport e) i₀ u) ^ 2 := by rw [hi0]; ring
    _ ≤ sjLoss (residualSupport e) u :=
        Finset.single_le_sum (f := fun i => (genMonomial (residualSupport e) i u) ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)

/-- **The residual unit `≤ #generators` on the unit box.** When `|u_ℓ| ≤ 1` for all `ℓ`, each
residual generator monomial is `≤ 1`, so `sjLoss (residualSupport e) u ≤ Fintype.card ι` — the
residual unit is bounded on the chart neighbourhood (the `b` bound the finiteness needs). -/
theorem sjLoss_residual_le_card (e : SJSupport ι d) (u : Fin d → ℝ) (hu : ∀ ℓ, |u ℓ| ≤ 1) :
    sjLoss (residualSupport e) u ≤ (Fintype.card ι : ℝ) := by
  have hterm : ∀ i : ι, (genMonomial (residualSupport e) i u) ^ 2 ≤ 1 := by
    intro i
    have hgm_nonneg : 0 ≤ genMonomial (residualSupport e) i u :=
      Finset.prod_nonneg (fun ℓ _ => pow_nonneg (abs_nonneg _) _)
    have hgm_le : genMonomial (residualSupport e) i u ≤ 1 := by
      unfold genMonomial
      exact Finset.prod_le_one (fun ℓ _ => pow_nonneg (abs_nonneg _) _)
        (fun ℓ _ => pow_le_one₀ (abs_nonneg _) (hu ℓ))
    exact pow_le_one₀ hgm_nonneg hgm_le
  calc sjLoss (residualSupport e) u
      = ∑ i, (genMonomial (residualSupport e) i u) ^ 2 := rfl
    _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card ι : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **The residual unit is continuous** (a finite sum of squares of products of `|u_ℓ|^n`). -/
theorem continuous_sjLoss_residual (e : SJSupport ι d) :
    Continuous (fun u : Fin d → ℝ => sjLoss (residualSupport e) u) := by
  unfold sjLoss genMonomial
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine Continuous.pow ?_ 2
  exact continuous_finset_prod _ (fun ℓ _ => ((continuous_apply ℓ).abs).pow _)

/-- **The ledger terminal loss integrand is finite below the monomial threshold.** Below the banked
`monomialThreshold d (sharedDivisorExp e) h`, and given a dehomogenised chart generator
(`∃ i₀, residual = 0` ⟹ residual unit `∈ [1, #ι]`), the fully-resolved terminal loss integrand
`(sjLoss e u)^{−c'}·(∏_ℓ |u_ℓ|^{h_ℓ})` has finite `∫⁻` over the unit box. Rewrites the integrand to
the banked terminal form (`sjLoss_terminal_integrand`) and applies
`terminal_monomial_mul_unit_lintegral_lt_top` with `k = sharedDivisorExp e`, `a = 1`, `b = #ι`. -/
theorem sjLoss_terminal_lintegral_lt_top (e : SJSupport ι d) (h : Fin d → ℕ) (c' : NNReal)
    (hc'0 : 0 < c') (i₀ : ι) (h0 : ∀ ℓ, e i₀ ℓ = sharedDivisorExp e ℓ)
    (hthr : (c' : ℝ≥0∞) < monomialThreshold d (sharedDivisorExp e) h) :
    ∫⁻ u in unitBox d,
        ENNReal.ofReal ((sjLoss e u) ^ (-(c' : ℝ)) * (∏ ℓ, |u ℓ| ^ (h ℓ))) < ⊤ := by
  have hcard : (0 : ℝ) < 1 := one_pos
  have hmeas : Measurable (fun u : Fin d → ℝ => sjLoss (residualSupport e) u) :=
    (continuous_sjLoss_residual e).measurable
  -- a.e. bounds on the residual unit over the box: `1 ≤ unit ≤ #ι`.
  have hunit : ∀ᵐ u ∂(volume.restrict (unitBox d)),
      (1 : ℝ) ≤ |sjLoss (residualSupport e) u| ∧
        |sjLoss (residualSupport e) u| ≤ (Fintype.card ι : ℝ) := by
    refine (ae_restrict_iff' (by exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))).mpr
      (ae_of_all _ (fun u hu => ?_))
    have hbox : ∀ ℓ, |u ℓ| ≤ 1 := by
      intro ℓ
      have := (Set.mem_univ_pi.mp hu) ℓ
      rw [abs_of_nonneg this.1]; exact this.2
    have hge := sjLoss_residual_ge_one e i₀ h0 u
    have hle := sjLoss_residual_le_card e u hbox
    rw [abs_of_nonneg (le_trans zero_le_one hge)]
    exact ⟨hge, hle⟩
  -- rewrite the integrand to the banked terminal form and apply the banked finiteness.
  have hbanked := terminal_monomial_mul_unit_lintegral_lt_top d (sharedDivisorExp e) h
    (fun u => sjLoss (residualSupport e) u) c' 1 (Fintype.card ι) hcard hc'0 hmeas hunit hthr
  rw [show (∫⁻ u in unitBox d,
        ENNReal.ofReal ((sjLoss e u) ^ (-(c' : ℝ)) * (∏ ℓ, |u ℓ| ^ (h ℓ))))
      = ∫⁻ u in unitBox d,
        ENNReal.ofReal (monomialIntegrand d (sharedDivisorExp e) h (c' : ℝ) u
          * |sjLoss (residualSupport e) u| ^ (-(c' : ℝ))) from ?_]
  · exact hbanked
  · refine setLIntegral_congr_fun (by exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (fun u _ => ?_)
    rw [sjLoss_terminal_integrand e h (c' : ℝ) u]

/-! ## The generator-level radial step (Aoyagi Case-2 ledger update — grounded Phase-2 slice)

The single-radial factor of the pure `(S,J)` step, LIFTED to the generator level (where the banked
frobSq bricks are too coarse — decorrelated Codex, this thread). A fresh exceptional divisor `u₀`
enters each generator `bᵢ` to order `a i` (Case-2 full block: `a ≡ 1`, every generator SHARES `u₀`;
Case-1 partial block: `a i ∈ {0,1}`). The ledger update `prependColumn` records exactly which
generators share the fresh divisor — the datum the `frobSq`-level `corankStep` loses. -/

/-- **Prepend a fresh exceptional column with active-set pattern `a`.** The ledger update of a
single radial blow-up: the fresh divisor `u₀` (new index `0`) divides `bᵢ` to order `a i`; old
divisors shift to `Fin.succ` and are PRESERVED (the passive-prefactor invariant). -/
def prependColumn (a : ι → ℕ) (e : SJSupport ι d) : SJSupport ι (d + 1) :=
  fun i => Fin.cons (a i) (e i)

omit [Fintype ι] [Nonempty ι] in
/-- **The fresh divisor factors out of each generator.**
`genMonomial (prependColumn a e) i (u₀ ::: u) = |u₀|^{a i} · genMonomial e i u`. -/
theorem genMonomial_prependColumn (a : ι → ℕ) (e : SJSupport ι d) (i : ι)
    (u₀ : ℝ) (u : Fin d → ℝ) :
    genMonomial (prependColumn a e) i (Fin.cons u₀ u) = |u₀| ^ (a i) * genMonomial e i u := by
  unfold genMonomial prependColumn
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- **The fresh divisor's shared exponent = the active-set minimum** `⨅ᵢ a i`. In Case-2 (`a ≡ 1`)
this is `1` (fully shared); the ledger records the sharing that `frobSq` cannot see. -/
theorem sharedDivisorExp_prependColumn_zero (a : ι → ℕ) (e : SJSupport ι d) :
    sharedDivisorExp (prependColumn a e) 0 = Finset.univ.inf' Finset.univ_nonempty a := by
  have hfun : (fun i : ι => prependColumn a e i 0) = a := by
    funext i; simp only [prependColumn, Fin.cons_zero]
  unfold sharedDivisorExp
  rw [hfun]

/-- **Old divisors are preserved (the passive-prefactor invariant).** The shared exponent of an old
divisor `u_ℓ` is unchanged by the fresh blow-up: `sharedDivisorExp (prependColumn a e) ℓ.succ =
sharedDivisorExp e ℓ`. The earlier exceptional coordinates are passive — never divided. -/
theorem sharedDivisorExp_prependColumn_succ (a : ι → ℕ) (e : SJSupport ι d) (ℓ : Fin d) :
    sharedDivisorExp (prependColumn a e) ℓ.succ = sharedDivisorExp e ℓ := by
  have hfun : (fun i : ι => prependColumn a e i ℓ.succ) = (fun i => e i ℓ) := by
    funext i; simp only [prependColumn, Fin.cons_succ]
  unfold sharedDivisorExp
  rw [hfun]

/-- **The Case-2 fresh divisor is fully shared** (`a ≡ 1`): its common-divisor exponent is `1`, so
it enters the terminal common monomial `g` to order exactly `1` — shared by all generators. The
shared-divisor datum, recorded at the generator level (the provenance of `corankStep`'s `u²`). -/
theorem sharedDivisorExp_prependColumn_one_zero (e : SJSupport ι d) :
    sharedDivisorExp (prependColumn (fun _ => 1) e) 0 = 1 := by
  rw [sharedDivisorExp_prependColumn_zero]; simp only [Finset.inf'_const]

omit [Nonempty ι] in
/-- **The Case-2 radial factor at the generator level** (`a ≡ 1`, the full block). The fresh radial
`u₀`, shared by EVERY generator, factors the terminal loss as `u₀² · (reduced loss)` — the
generator-level form of `corankStep`'s `frobSq((u•Δ)·Q) = u²·frobSq(Δ·Q)`, now with the sharing
recorded (`sharedDivisorExp_prependColumn_one_zero`). -/
theorem sjLoss_prependColumn_one (e : SJSupport ι d) (u₀ : ℝ) (u : Fin d → ℝ) :
    sjLoss (prependColumn (fun _ => 1) e) (Fin.cons u₀ u) = u₀ ^ 2 * sjLoss e u := by
  unfold sjLoss
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [genMonomial_prependColumn]
  simp only [pow_one, mul_pow, sq_abs]

/-! ## Non-vacuity — the load-bearing shared-vs-fresh distinction (DATA-A) -/

/-- The **shared-divisor** witness `⟨δx, δy⟩`: two generators over exceptional vars
`[δ, x, y] = Fin 3`, both divisible by `δ` (index `0`). Support matrix `[[1,1,0],[1,0,1]]`. -/
def suppShared : SJSupport (Fin 2) 3 := fun i => ![![1, 1, 0], ![1, 0, 1]] i

/-- The **fresh-per-generator** witness `⟨δ₁x, δ₂y⟩`: two generators over vars
`[δ₁, δ₂, x, y] = Fin 4`, each divisible by its OWN exceptional (`δ₁` index `0`, `δ₂` index `1`).
Support matrix `[[1,0,1,0],[0,1,0,1]]`. -/
def suppFresh : SJSupport (Fin 2) 4 := fun i => ![![1, 0, 1, 0], ![0, 1, 0, 1]] i

/-- **DATA-A (the load-bearing datum).** The SHARED-divisor witness has common-divisor exponent
`k_δ = 1` on the shared divisor `δ` (index `0`) — so the common monomial `g = |δ|` factors out
(`∑bᵢ² = δ²(x²+y²)`); the FRESH witness has `k_ℓ = 0` on every divisor — no common monomial factors
(`∑bᵢ² = δ₁²x²+δ₂²y²`). The `min_i` over the support matrix is exactly what distinguishes them, and
it is why fresh-per-block undercounts. Proved directly from `sharedDivisorExp_fin_two`. -/
theorem dataA_shared_vs_fresh :
    (sharedDivisorExp suppShared 0 = 1 ∧ sharedDivisorExp suppShared 1 = 0
      ∧ sharedDivisorExp suppShared 2 = 0)
    ∧ (∀ ℓ : Fin 4, sharedDivisorExp suppFresh ℓ = 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [sharedDivisorExp_fin_two]; rfl
  · rw [sharedDivisorExp_fin_two]; rfl
  · rw [sharedDivisorExp_fin_two]; rfl
  · intro ℓ; rw [sharedDivisorExp_fin_two]; fin_cases ℓ <;> rfl

/-- **Non-vacuity of the terminal factorisation.** On the shared witness the terminal loss factors
as `∑bᵢ² = |δ|²·(unit)` with common divisor `g = |δ|` (`sharedDivisorExp = [1,0,0]`) — the
`sjLoss_factor` mechanism at a concrete genuinely-shared support. -/
example (u : Fin 3 → ℝ) :
    sjLoss suppShared u
      = (commonDivisor suppShared u) ^ 2 * sjLoss (residualSupport suppShared) u :=
  sjLoss_factor suppShared u

/-- A support with a **dehomogenised generator** (`bᵢ₀ = g`): `e = [[1,0],[1,1]]`. -/
def suppDehom : SJSupport (Fin 2) 2 := fun i => ![![1, 0], ![1, 1]] i

/-- **Non-vacuity of the terminal-finiteness hypothesis H1** (`sjLoss_terminal_lintegral_lt_top`'s
`∃ i₀, ∀ℓ, e i₀ ℓ = sharedDivisorExp e ℓ`). On `suppDehom` generator `0` is the dehomogenised
coordinate — `suppDehom 0 = [1,0]` equals `sharedDivisorExp suppDehom = [min 1 1, min 0 1] = [1,0]`
at every `ℓ` — so its residual monomial is `1` (`sjLoss_residual_ge_one` fires) and the H1 path is
inhabited (`b₀ = g`): the finiteness endpoint's hypothesis is genuinely satisfiable. -/
example : ∃ i₀ : Fin 2, ∀ ℓ : Fin 2, suppDehom i₀ ℓ = sharedDivisorExp suppDehom ℓ := by
  refine ⟨0, fun ℓ => ?_⟩
  rw [sharedDivisorExp_fin_two]
  fin_cases ℓ <;> rfl

end DLNFibre.DLN.RLCT
