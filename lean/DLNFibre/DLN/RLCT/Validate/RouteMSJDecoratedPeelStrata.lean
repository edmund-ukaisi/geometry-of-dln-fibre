import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelCoV
import DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex
import Mathlib.Topology.Instances.Matrix
import DLNFibre.DLN.RLCT.Foundations.LossContinuity

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelStrata` — the corner-cover split (piece 8)

**Thread `genm-decbuild`, piece 8 (the stratification keystone).** Any measurable predicate `S` on
the tail params splits the per-chart peeled integral `gammaPeelIntegral`, and finiteness of both
strata gives finiteness of the chart. Instantiated at the corank-rank stratum
`S = {A' | 0 < det(Q_b Q_bᵀ)}` (`= {rank Q_b = b}`), this routes `{det>0}` → good-strata Regime-A
closure (via `posDef_gram_of_rank_full`) and `{det=0}` → the deeper corner leaf (the operator-gated
determinantal atom, carried as an INTERFACE hypothesis, NOT a sorry — reduction stays clean-three).

## What lands here (sorry-free, generic)

* **`gammaPeelInner`** — the inner `A₀`-fibre integrand (a function of the tail params `A'`), so
  `gammaPeelIntegral = ∫⁻ A' in box, gammaPeelInner A'`.
* **`gammaPeelIntegral_stratify`** — for measurable `S`, `gammaPeelIntegral = ∫_{box∩S} + ∫_{box\S}`
  (banked `lintegral_inter_add_diff`).
* **`gammaPeelIntegral_lt_top_of_strata`** — finiteness of the chart from finiteness of both strata.
  The `{box \ S}` (deeper) stratum is the carried interface fencing the operator-gated atom; the
  `{box ∩ S}` (good) stratum is the buildable Regime-A obligation.

## What is NOT here (next steps)

The instantiation `S = {0 < det(Q_b Q_bᵀ)}` (measurability — `det ∘ product` continuous in `A'`),
the good-strata Regime-A wiring (absorption CoV + shift + reduced-chain IH), and the deeper atom
interface. This module is the generic split those instantiate.

S2-FREE: pure `lintegral` set-additivity. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The inner `A₀`-fibre integrand of `gammaPeelIntegral`** at tail params `A'`:
`∫⁻ A₀ in matBox ∩ pivotChart, frobSq(A₀ · prod(tailChain) A')^{−c'}`. -/
noncomputable def gammaPeelInner (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) (A' : Params (tailChain M)) : ℝ≥0∞ :=
  ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
    ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))

/-- `gammaPeelIntegral` is the outer integral of `gammaPeelInner` over the tail box. -/
theorem gammaPeelIntegral_eq_inner (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ A' in paramsBoxM (tailChain M) 1, gammaPeelInner M t ρ κ c' A' := rfl

/-- **The measurable stratification split (generic).** For any measurable `S` on the tail params,
`gammaPeelIntegral = ∫_{box ∩ S} inner + ∫_{box \ S} inner`. Banked `lintegral_inter_add_diff`. -/
theorem gammaPeelIntegral_stratify (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ)
    (S : Set (Params (tailChain M))) (hS : MeasurableSet S) :
    gammaPeelIntegral M t ρ κ c'
      = (∫⁻ A' in paramsBoxM (tailChain M) 1 ∩ S, gammaPeelInner M t ρ κ c' A')
        + (∫⁻ A' in paramsBoxM (tailChain M) 1 \ S, gammaPeelInner M t ρ κ c' A') := by
  rw [gammaPeelIntegral_eq_inner]
  exact (lintegral_inter_add_diff (gammaPeelInner M t ρ κ c') (paramsBoxM (tailChain M) 1) hS).symm

/-- **The finiteness reduction from the two strata.** `gammaPeelIntegral < ⊤` when both strata are
finite. The `{box \ S}` (deeper) finiteness is the carried interface fencing the operator-gated atom
(a hypothesis, not a sorry — clean-three); the `{box ∩ S}` (good) finiteness is the Regime-A
obligation. -/
theorem gammaPeelIntegral_lt_top_of_strata (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ)
    (S : Set (Params (tailChain M))) (hS : MeasurableSet S)
    (hgood : (∫⁻ A' in paramsBoxM (tailChain M) 1 ∩ S, gammaPeelInner M t ρ κ c' A') < ⊤)
    (hdeep : (∫⁻ A' in paramsBoxM (tailChain M) 1 \ S, gammaPeelInner M t ρ κ c' A') < ⊤) :
    gammaPeelIntegral M t ρ κ c' < ⊤ := by
  rw [gammaPeelIntegral_stratify M t ρ κ c' S hS]
  exact ENNReal.add_lt_top.mpr ⟨hgood, hdeep⟩

/-! ## The three-way `(a,b,q)` category routing (wtint WALL verdict, 2026-07-10)

The emitted Γ-peel Gram weight `det(Q_b Q_bᵀ)^{−a/2}` is NOT absorbed by the reduced-chain IH
(`frobSq(B₀) = frobSq(B·A_{≥2})` is identically `Y`-independent, while the Gram singularity lives
entirely in `Y` via `Q_b = Y·A_{≥2}`; wtint adversarial + decorrelated Codex). So the closure MUST
route by the discrete category `(a,b,q)`, `a = M₀−t`, `b = M₁−t`, `q = M_last`:

* **Cat I** (`a+b ≤ q`): the whole-line Γ-peel (Regime A) is safe — `det^{−a/2}` is integrable
  (`⟺ a < q−b+1`, sharp), via the single-minor bound `det(Q_bQ_bᵀ) ≥ minor²` (commissioned
  `genm-cbmin`, Loewner route — CB absent) + order-1 vanishing on the rank-drop divisor + red. IH.
* **Cat II/III** (`q < a+b`): the weight genuinely DIVERGES over the good stratum — the whole-line
  Γ-peel MUST NOT be used; route to the corner / Regime-B bounded branch (cert §B=2 cover).

The deeper-strata `{rank ≤ b−2}` atom (weaker `a < q−b+r`, non-binding) is SEPARATE and stays the
operator-gated build-vs-cite — kept out of the weight-control here. -/

/-- **The three-way category routing scaffold.** The per-chart finiteness dispatches on the discrete
category `a+b ≤ q` (Cat I, whole-line Γ-peel safe) vs `q < a+b` (Cat II/III, diverges → corner):
`gammaPeelIntegral < ⊤` follows from the two category obligations. `a = M₀−t`, `b = M₁−t`,
`q = M (Fin.last (L+1+1))`. Trivial dispatch (`by_cases`); content is the two carried closures. -/
theorem gammaPeelIntegral_lt_top_of_categoryRouting (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ)
    (hCatI : (M 0 - t) + (M 1 - t) ≤ M (Fin.last (L + 1 + 1)) → gammaPeelIntegral M t ρ κ c' < ⊤)
    (hCatHi : M (Fin.last (L + 1 + 1)) < (M 0 - t) + (M 1 - t) → gammaPeelIntegral M t ρ κ c' < ⊤) :
    gammaPeelIntegral M t ρ κ c' < ⊤ := by
  by_cases h : (M 0 - t) + (M 1 - t) ≤ M (Fin.last (L + 1 + 1))
  · exact hCatI h
  · exact hCatHi (not_le.mp h)

/-! ## The corank-rank stratum `{0 < det(Q_b Q_bᵀ)}` — measurable instantiation of the split -/

/-- **The corank Gram** `Q_b(A') · Q_b(A')ᵀ` as a function of the tail params, `Q_b(A')` the corank
rows of the reindexed tail product `prod(tailChain) A'` (`Sum.inr` of `blockSplitEquiv κ`). Its det
is `> 0` exactly on the full-row-rank stratum `{rank Q_b = b}` (`b = M₁−t`). -/
noncomputable def corankGram (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1))
    (A' : Params (tailChain M)) : Matrix (Fin (M 1 - t)) (Fin (M 1 - t)) ℝ :=
  (((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id) *
    (((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id).transpose

/-- **The good corank stratum is measurable** (open): `{A' | 0 < det(Q_b(A') Q_b(A')ᵀ)}` is the
preimage of `(0, ∞)` under the continuous map `A' ↦ det(corankGram A')` — `prod(tailChain)` is
continuous (`continuous_prod`); submatrix/mul/transpose/det continuous (`Continuous.matrix_*`). -/
theorem measurableSet_corankGood (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1)) :
    MeasurableSet {A' : Params (tailChain M) | 0 < (corankGram M t κ A').det} := by
  have hp : Continuous (prod (tailChain M)) := continuous_prod (tailChain M)
  have hQb : Continuous (fun A' : Params (tailChain M) =>
      ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id) :=
    (hp.matrix_submatrix (blockSplitEquiv κ) id).matrix_submatrix Sum.inr id
  have hcont : Continuous (fun A' : Params (tailChain M) => (corankGram M t κ A').det) := by
    unfold corankGram
    exact (hQb.matrix_mul hQb.matrix_transpose).matrix_det
  exact (isOpen_lt continuous_const hcont).measurableSet

/-- **The corank-rank stratification split.** Instantiating `gammaPeelIntegral_stratify` at the good
corank stratum `S = {0 < det(Q_b Q_bᵀ)}` (`= {rank Q_b = b}`): the chart integral splits into the
good stratum (→ Regime A) plus its complement (→ corner / deeper atom). -/
theorem gammaPeelIntegral_stratify_corank (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = (∫⁻ A' in paramsBoxM (tailChain M) 1 ∩ {A' | 0 < (corankGram M t κ A').det},
          gammaPeelInner M t ρ κ c' A')
        + (∫⁻ A' in paramsBoxM (tailChain M) 1 \ {A' | 0 < (corankGram M t κ A').det},
          gammaPeelInner M t ρ κ c' A') :=
  gammaPeelIntegral_stratify M t ρ κ c' _ (measurableSet_corankGood M t κ)

/-- **Chart finiteness from the corank strata.** `gammaPeelIntegral < ⊤` from finiteness of the
full-rank good stratum (`{0 < det}` → Regime A + weight-control) and its complement (`{det = 0}` →
corner / deeper `{rank ≤ b−2}` atom). Instantiates `gammaPeelIntegral_lt_top_of_strata`. -/
theorem gammaPeelIntegral_lt_top_of_corankStrata (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ)
    (hgood : (∫⁻ A' in paramsBoxM (tailChain M) 1 ∩ {A' | 0 < (corankGram M t κ A').det},
        gammaPeelInner M t ρ κ c' A') < ⊤)
    (hdeep : (∫⁻ A' in paramsBoxM (tailChain M) 1 \ {A' | 0 < (corankGram M t κ A').det},
        gammaPeelInner M t ρ κ c' A') < ⊤) :
    gammaPeelIntegral M t ρ κ c' < ⊤ :=
  gammaPeelIntegral_lt_top_of_strata M t ρ κ c' _ (measurableSet_corankGood M t κ) hgood hdeep

end DLNFibre.DLN.RLCT
