import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurGeneral` — the ∀-corank recursion SCAFFOLD

The arbitrary-corank generalisation of the rank-stratified radial-Schur recursion: a
WellFounded-on-corank strong-induction skeleton that, GIVEN the per-corank analytic `recStep`,
produces the finiteness conclusion `core_schurGen_lt_top` for every corank `r`. The two concrete
banked instances are literal instantiations:

* `RouteMSchurDepth2.core_schur2_lt_top` — corank `2`, threshold `λ_{2,4} = 2` (CLOSED, reviewed);
* `RouteMSchurCorank3.core_schur3_lt_top` — corank `3`, threshold `λ_{3,4} = 4` (in flight).

## What is in this file (and what is DEFERRED)

The SCAFFOLD — the *determined, friction-free* parts — is proved here, sorry-free:

* `SchurCore p r c' T` — the corank-`r` finiteness predicate
  `∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'} < ⊤`, the literal common shape of
  the corank-2/3 conclusions (`p` = the column count, `4` in this validation; `r` = the corank).
* `SchurThreshold p lam` — the abstract threshold contract: `lam : ℕ → ℝ` with the corank-recursion
  inequalities `lam 0 = 0`, `lam r ≤ r²/2`, and the additive peel bound
  `lam r ≤ jp/2 + lam (r−j)`. Keeping `lam` ABSTRACT (rather than a `ℝ`-valued strong-recursion
  `def`) is the de-risking choice: the wrapper is threshold-agnostic, and the concrete values
  `lam 2 = 2`, `lam 3 = 4` are discharged only at instantiation.
* `SchurLowerIH p lam r` — the inductive hypothesis in the EXACT form the Schur peel consumes: the
  JOINT lower core `SchurCore p (r−j) ·` over a FREE `Δ`/`S` box (the cert's `(W, V, Sc)` carrier),
  NOT an `Sc`-only statement (O2 cert: the Schur complement `Sc` plays the role of the free residual
  `Δ` — `n4-o2-pushforward-adjudication.md §3,§4`).
* `core_schurGen_lt_top` — the strong-induction WRAPPER: takes an abstract `SchurRecStep` and yields
  `SchurCore p r c' T` for all `r`. **Sorry-free, axiom-clean** — the deferred analytic content
  lives in the `SchurRecStep` HYPOTHESIS, so the wrapper itself imports no `sorry`.

DEFERRED (the genuine wall, NOT in this file): the analytic per-corank `recStep`
PROOF (`schurRecStep_deferred`), which peels the top `jp`-dim Morse block at threshold `jp/2`,
translation-dominates `M22 ↦ Sc` into the free lower core, and recurses. It stands on the
validated corank-3 cover (`core_schur3_lt_top`), which is in flight; once that lands, the recStep
proof generalises the corank-3 firing. The contract is pinned below as `SchurRecStep`; a concrete
STUB at `p = 4` is given as a clearly-marked `sorry` (`schurRecStep4_stub`), kept OUT of the
wrapper's dependency graph so `#print axioms core_schurGen_lt_top` stays clean.

## S2-hygiene
The scaffold introduces NO measure-theoretic content of its own and NO new axiom — it is pure
finiteness bookkeeping (strong induction on `ℕ`). The S2-discipline binds the deferred recStep
proof (Morse leaves / a-divisor / Tonelli / Schur splits), not this skeleton.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The corank-`r` finiteness predicate (the common shape) -/

/-- **The corank-`r` Schur core finiteness predicate.** `SchurCore p r c' T` asserts the free-box
core integral `∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'}` is finite. With `p = 4`,
`SchurCore 4 2 c' T` is the conclusion of `core_schur2_lt_top`, and `SchurCore 4 3 c' T` that of
`core_schur3_lt_top` — the literal common generalisation. -/
def SchurCore (p r : ℕ) (c' T : ℝ) : Prop :=
  (∫⁻ Δ in matBox r r T, ∫⁻ S in matBox r p T,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))) < ⊤

/-! ## The abstract threshold contract -/

/-- **The corank-recursion threshold contract.** A function `lam : ℕ → ℝ` is a `SchurThreshold p`
when it satisfies the corank-recursion inequalities that the WellFounded wrapper consumes:
* `lambda0` — the corank-0 leaf carries no binding threshold (`lam 0 = 0`, a pure-Morse leaf is
  finite for any `c' > 0`);
* `radial_le` — the a-axis (radial-divisor) cap `lam r ≤ r²/2` (the `r²` blow-up Jacobian);
* `peel_le` — the additive peel bound `lam r ≤ jp/2 + lam (r−j)` for `1 ≤ j ≤ r` (the top `jp`-dim
  Morse block contributes `jp/2`, the lower core `lam (r−j)`).

The closed corank-recursion threshold `λ_{r,p} = min(r²/2, min_j(jp/2 + λ_{r−j,p}))` is the
*greatest* such `lam`; the wrapper needs only these inequalities, so the actual value never has to
be computed here (`lam 2 = 2`, `lam 3 = 4` are discharged at instantiation). -/
structure SchurThreshold (p : ℕ) (lam : ℕ → ℝ) : Prop where
  lambda0 : lam 0 = 0
  radial_le : ∀ {r : ℕ}, 1 ≤ r → lam r ≤ (r ^ 2 : ℝ) / 2
  peel_le : ∀ {r j : ℕ}, 1 ≤ j → j ≤ r → lam r ≤ ((j : ℝ) * (p : ℝ)) / 2 + lam (r - j)

/-! ## The inductive hypothesis and the deferred per-corank step -/

/-- **The inductive hypothesis the Schur peel consumes.** At corank `r`, after the `j`-block peel,
the residual is the JOINT free-box corank-`(r−j)` core integrated at the SHIFTED exponent
`c'' = c' − jp/2`. `SchurLowerIH p lam r` packages exactly the finiteness of every such lower core
`SchurCore p (r−j) c'' T''` for `c'' < lam (r−j)`. This is the cert's `(W, V, Sc)` carrier — the
free lower core, NOT an `Sc`-only statement (O2 cert `n4-o2-pushforward-adjudication.md §3,§4`:
`Sc` is structurally the free residual `Δ` one corank lower). -/
def SchurLowerIH (p : ℕ) (lam : ℕ → ℝ) (r : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ r →
    ∀ c'' : ℝ, 0 < c'' → c'' < lam (r - j) →
      ∀ T'' : ℝ, 0 < T'' → SchurCore p (r - j) c'' T''

/-- **The deferred per-corank analytic step (the contract, NOT proved here).** Given the threshold
contract and the lower-corank IH, the corank-`r` core is finite below `lam r`. This is the genuine
wall: its PROOF is the radial-Δ cover + N2b minor-pivot split + shifted-exponent Morse peel +
`M22 ↦ Sc` translation-domination + recursion (the corank-3 firing
`RouteMSchurCorank3.core_schur3_lt_top`, generalised). The wrapper takes it as a HYPOTHESIS, so the
scaffold is sorry-free and the deferred content is named, not hidden. -/
def SchurRecStep (p : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, SchurThreshold p lam → SchurLowerIH p lam r →
    ∀ c' : ℝ, 0 < c' → c' < lam r →
      ∀ T : ℝ, 0 < T → SchurCore p r c' T

/-! ## The WellFounded-on-corank wrapper (the determined, friction-free part — sorry-free) -/

/-- **The ∀-corank finiteness, GIVEN the per-corank `recStep`.** Strong induction on the corank `r`
(the WellFounded measure: the peel drops `r → r − j` with `j ≥ 1`, so `r − j < r`). No analytic
content lives here — the per-corank work is the `hstep` hypothesis, deferred. The conclusion is the
literal `∀r` generalisation of `core_schur2_lt_top` / `core_schur3_lt_top`.

**Axiom-clean:** because `hstep` is a hypothesis, `#print axioms core_schurGen_lt_top` reports only
`[propext, Classical.choice, Quot.sound]` — the deferred `sorry` is confined to the concrete STUB
that supplies `hstep`, never to this wrapper. -/
theorem core_schurGen_lt_top
    (p : ℕ) (lam : ℕ → ℝ)
    (hlam : SchurThreshold p lam)
    (hstep : SchurRecStep p lam) :
    ∀ r : ℕ, ∀ c' : ℝ, 0 < c' → c' < lam r →
      ∀ T : ℝ, 0 < T → SchurCore p r c' T := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
      refine hstep r hlam ?_
      intro j hj0 hjr c'' hc0 hclam T'' hT''
      exact ih (r - j) (by omega) c'' hc0 hclam T'' hT''

/-! ## The corank-2 base rung (a literal instantiation of `SchurCore 4 2`) -/

/-- The closed corank-2 weld `core_schur2_lt_top` repackaged as `SchurCore 4 2` — confirming the
general predicate's shape matches the banked instance literally (the load-bearing shape-pin). -/
theorem schurCore4_two (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    SchurCore 4 2 c' T := by
  simpa only [SchurCore] using core_schur2_lt_top c' hc0 hc' T hT

/-! ## The concrete deferred STUB at `p = 4` (clearly marked; OUTSIDE the wrapper's axiom graph) -/

/-- **STUB — the deferred per-corank analytic step at `p = 4`.** This is the genuine wall: the
radial-Δ cover + N2b split + shifted-exponent peel + `M22 ↦ Sc` translation-domination + recursion,
generalising the corank-3 firing once `core_schur3_lt_top` is validated. Marked `sorry` ON PURPOSE;
kept SEPARATE from `core_schurGen_lt_top` so the wrapper stays axiom-clean. Replacing this `sorry`
with the real proof (and `schurThreshold4` below) closes the ∀M N4 finiteness for `p = 4`. -/
theorem schurRecStep4_stub (lam : ℕ → ℝ) : SchurRecStep 4 lam := by
  sorry

/-! ## The concrete threshold WITNESS (the contract is inhabited in-Lean, `p = 4`)

The wrapper above is threshold-AGNOSTIC (abstract `lam`); this section exhibits the concrete closed
corank-recursion threshold `λ_{r,4}` and PROVES it satisfies `SchurThreshold 4` — upgrading the
numeric non-vacuity (Python) to a Lean witness (bedrock: the witness is shown in-file). Kept SEPARATE
from `core_schurGen_lt_top`, which stays abstract-`lam` and axiom-clean. -/

/-- **The closed corank-recursion threshold `λ_{r,4}`** = `{0; ½; 2r−2 (r ≥ 2)}` — the explicit
solution of `λ_r = min(r²/2, min_{1≤j≤r}(2j + λ_{r−j}))` at `p = 4` (`λ_{r,4} = [0,½,2,4,6,8,…]`,
numerically `Vzero_lambda_recursion.py` and the closed-form check here). The genuine threshold, so
`schurLambda 2 = 2`, `schurLambda 3 = 4` are the corank-2/3 instance thresholds. -/
noncomputable def schurLambda : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 2
  | (n + 2) => 2 * ((n : ℝ) + 2) - 2

@[simp] theorem schurLambda_zero : schurLambda 0 = 0 := rfl
@[simp] theorem schurLambda_one : schurLambda 1 = 1 / 2 := rfl

/-- `schurLambda (n+2) = 2n + 2` (the `r ≥ 2` branch, simplified). -/
theorem schurLambda_add_two (n : ℕ) : schurLambda (n + 2) = 2 * (n : ℝ) + 2 := by
  have : schurLambda (n + 2) = 2 * ((n : ℝ) + 2) - 2 := rfl
  rw [this]; ring

/-- `schurLambda r = 2r − 2` for `r ≥ 2` (the `r ≥ 2` branch in closed `r` form). -/
theorem schurLambda_eq_of_ge_two {r : ℕ} (hr : 2 ≤ r) : schurLambda r = 2 * (r : ℝ) - 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 2 := ⟨r - 2, by omega⟩
  rw [schurLambda_add_two]; push_cast; ring

theorem schurLambda_two : schurLambda 2 = 2 := by
  have := schurLambda_add_two 0; simpa using this

theorem schurLambda_three : schurLambda 3 = 4 := by
  have := schurLambda_add_two 1; norm_num at this ⊢; linarith [this]

/-- The universal lower bound `2r − 2 ≤ schurLambda r` (`r = 0`: `−2 ≤ 0`; `r = 1`: `0 ≤ ½`;
`r ≥ 2`: equality). The load-bearing fact for the additive peel bound. -/
theorem schurLambda_ge (r : ℕ) : 2 * (r : ℝ) - 2 ≤ schurLambda r := by
  match r with
  | 0 => norm_num [schurLambda_zero]
  | 1 => norm_num [schurLambda_one]
  | (n + 2) => rw [schurLambda_add_two]; push_cast; linarith

/-- The universal cap `schurLambda r ≤ r²/2` (the radial-divisor a-axis bound). -/
theorem schurLambda_le_sq (r : ℕ) : schurLambda r ≤ (r ^ 2 : ℝ) / 2 := by
  match r with
  | 0 => norm_num [schurLambda_zero]
  | 1 => norm_num [schurLambda_one]
  | (n + 2) =>
      rw [schurLambda_add_two]; push_cast
      nlinarith [sq_nonneg ((n : ℝ)), (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- **The concrete threshold satisfies the contract.** `schurLambda` is a `SchurThreshold 4` — the
abstract threshold contract is INHABITED in-Lean, so `core_schurGen_lt_top` (and the deferred
`SchurRecStep`) are non-vacuous. -/
theorem schurLambda_satisfies_threshold : SchurThreshold 4 schurLambda where
  lambda0 := schurLambda_zero
  radial_le := fun {r} _ => schurLambda_le_sq r
  peel_le := fun {r j} hj hjr => by
    -- `schurLambda r ≤ jp/2 + schurLambda (r−j)` with `p = 4`, i.e. `≤ 2j + schurLambda (r−j)`.
    have hcast : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [hcast]
    have hsub : (↑(r - j) : ℝ) = (r : ℝ) - (j : ℝ) := Nat.cast_sub hjr
    -- The residual threshold's universal lower bound, in the shifted variable:
    have hres : 2 * ((r : ℝ) - (j : ℝ)) - 2 ≤ schurLambda (r - j) := by
      have := schurLambda_ge (r - j); rwa [hsub] at this
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjr1 : (j : ℝ) ≤ (r : ℝ) := by exact_mod_cast hjr
    have h2j : (j : ℝ) * 4 / 2 = 2 * (j : ℝ) := by ring
    rw [h2j]
    -- `r = 1` (then `j = 1`, residual `schurLambda 0 = 0`) needs the direct value; `r ≥ 2` uses
    -- `schurLambda r = 2r − 2 ≤ 2j + (2(r−j) − 2)`. (`r = 0` is vacuous: `1 ≤ j ≤ 0`.)
    rcases Nat.lt_or_ge r 2 with hr | hr
    · -- `r < 2`, with `1 ≤ j ≤ r`, forces `r = 1` and `j = 1`.
      have hr1 : r = 1 := by omega
      have hj_eq : j = 1 := by omega
      subst hr1; subst hj_eq
      norm_num [schurLambda_one, schurLambda_zero]
    · -- `r ≥ 2`: `schurLambda r = 2r − 2 ≤ 2j + (2(r−j) − 2)` by `hres`.
      rw [schurLambda_eq_of_ge_two hr]
      linarith

/-! ## What closes once the recStep lands (the honest remaining-input statement) -/

/-- **The ∀-corank `p = 4` finiteness at the concrete threshold, modulo ONLY the recStep.** Feeding
the proven threshold witness into the wrapper: GIVEN the deferred per-corank `SchurRecStep 4
schurLambda`, the corank-`r` Schur core is finite below the genuine threshold `schurLambda r` for ALL
`r` — so `λ_{r,4}` (with `schurLambda 2 = 2`, `schurLambda 3 = 4`) is exactly the closure threshold.
The ONLY remaining input is `hstep` (the genuine wall); the threshold-contract side is discharged
here. Takes `hstep` as a hypothesis, so axiom-clean. -/
theorem schurGen_lt_top_modulo_recStep (hstep : SchurRecStep 4 schurLambda) :
    ∀ r : ℕ, ∀ c' : ℝ, 0 < c' → c' < schurLambda r →
      ∀ T : ℝ, 0 < T → SchurCore 4 r c' T :=
  core_schurGen_lt_top 4 schurLambda schurLambda_satisfies_threshold hstep

end DLNFibre.DLN.RLCT
