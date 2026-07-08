import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartShear
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPeel

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel` — the peel on the freed Γ-integral (mission item 1)

**Piece toward `sjJointResolution`** (thread `genm-sjcarrier8`; the R1-UPPER final gate). The banked
chain — block-reindex (`chartInner_blockReindex_eq_of_emb`), Schur weld
(`chartInner_schurWeld_eq_of_emb`), MP shear freeing `Γ` (`chartInner_schurShearFree_eq`) — rewrote the
RAW front-factor chart integral to the cross-coupled Schur form with the corank block `Γ` an
INDEPENDENT integration variable. This module composes those onto `gammaPeelIntegral` itself and welds
the banked corank atom (`corankBlock_morsePeel_lt_top`, `RouteMSJCorankPeel`) onto the freed loss.

## What lands here

* **`gammaPeelIntegral_schurShearFree_eq`** — the EQUALITY (no finiteness, no hypotheses) rewriting
  `gammaPeelIntegral M t ρ κ c'` into the freed-`Γ` triple integral
  `∫_{A'} ∫_{x∈outerDom} ∫_{Γ∈shearbox} (freedSchurLoss x Γ Q̃)^{−c'}`, with tail
  `Q̃ = (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id` and `Γ` free. This is the exact form
  the `(S,J)` outer descent (the mountain, `sjJointResolution`) operates on: the weld over the inner
  `A₀`-fibre, then the shear per outer `x`, both measure-preserving, composed under `lintegral_congr`
  over the outer tail box `A'`. Sorry-free; carries no analytic strength beyond the changes of variables.

* **`freedSchurLoss_inner_peel_lt_top`** — the CONDITIONAL inner-`Γ` finiteness (mission item 1(b)).
  Given the three interface hypotheses the outer descent must supply — the pivot-energy core strictly
  positive (`0 < frobSq (P·Q̃ₚ)`, `P = of x.1.1`), the coupling `Q_b Q_bᵀ` positive definite, and `c'`
  above the block Morse threshold `a·b/2` (`a = M₀−t`, `b = M₁−t`) — the freed inner `Γ`-integral over
  ANY domain is finite. Welds `freedSchurLoss` onto the atom's `w + ‖Apiv‖² + ‖Ccross + Γ·Qb‖²` shape
  at `w := frobSq (P·Q̃ₚ)`, `Apiv := 0`, `Ccross := C·Q̃ₚ`, `Qb := Q_b` — so the held pivot energy plays
  the atom's strictly-positive core. Sorry-free; the hypotheses are EXPOSED as the interface.

* **`freedSchurLoss_inner_bounded_lt_top`** — the atom-inapplicable branch (item 1(c)). Over ANY
  FINITE-measure domain, core positivity `0 < frobSq (P·Q̃ₚ)` alone (no threshold, no `PosDef`) makes the
  freed inner `Γ`-integral finite for any `c' ≥ 0` (the pivot energy lower-bounds the loss, so the
  integrand is bounded). The branch the descent uses on the `≈94/480` charts where `c' ≤ a·b/2`.

## What is NOT here (the standing mountain — reported precisely)

The three interface hypotheses of `freedSchurLoss_inner_peel_lt_top` do NOT hold pointwise for a fixed
outer `(A', x)`: the pivot energy `frobSq (P·Q̃ₚ)` CAN vanish (its zero-locus is where the tail product
degenerates), `Q_b Q_bᵀ` is rank-deficient on the bottleneck charts (`M₁−t > min deeper widths`), and
`c' < ½·minAdm M` does not force `c' > a·b/2` (≈94/480 charts). Supplying them — as a MEASURE
statement, by integrating the outer tail parameters `A'` and descending through the `SJLinGenState`
carrier (`gen_rowMix_const` block-elim + `loss_radialStep` radial) to the monomial terminal
(`sjLoss_terminal_lintegral_lt_top`), wiring the reduced coupling to the strong IH (`redChain t M`) —
is the `(S,J)` monomial/normal-form DOUBLE INDUCTION. Per the design certificate
(`.../genm-sjjoint-design/cert.md`, 3 decorrelated lines + Codex xhigh): at the binding cut
`minAdm M = a + minAdm (redChain t* M)` the residual exponent EXACTLY saturates the reduced-chain IH
threshold — Hölder-infeasible — so the strong IH is insufficient as a black box, and the
matrix-box→blow-up change of variables is ~65–75% genuinely-new resolution-of-singularities content.
`sjJointResolution` (`RouteMSJResolution`) stays the single named sorry, UNTOUCHED — this tide adds a
sorry-free module and precisely isolates the remaining gap to the outer descent.

S2-FREE: measure-preserving weld/shear (banked) + the banked corank atom
(`corankBlock_morsePeel_lt_top`, itself S2-free); no `monomial_rlct`. Axiom footprint: the clean three
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

variable {L : ℕ}

/-! ## The freed-`Γ` equality for `gammaPeelIntegral` (mission item 1 foundation) -/

/-- **`gammaPeelIntegral` in freed-`Γ` form (EQUALITY).** For an arbitrary `(t, ρ, κ)` pivot cut, the
per-chart peeled integral equals the freed-`Γ` triple integral: outer over the tail box `A'`, then over
the `(P, B₁₂, C)`-outer domain `x`, then over the freed corank block `Γ` (an INDEPENDENT variable over
the shear-image box), of the freed Schur loss `(freedSchurLoss x Γ Q̃)^{−c'}`, tail
`Q̃ = (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id`. Composes the banked Schur weld
(`chartInner_schurWeld_eq_of_emb`, over the inner `A₀`-fibre) with the banked MP shear
(`chartInner_schurShearFree_eq`, per outer `x`), under `lintegral_congr` over the outer `A'`. No
finiteness, no branch condition, no hypothesis — a pure change-of-variables identity. -/
theorem gammaPeelIntegral_schurShearFree_eq (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
              ENNReal.ofReal ((freedSchurLoss x Γ
                ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')) := by
  unfold gammaPeelIntegral
  refine lintegral_congr (fun A' => ?_)
  rw [chartInner_schurWeld_eq_of_emb ρ κ (prod (tailChain M) A') c' 1]
  exact chartInner_schurShearFree_eq
    ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id) c' 1

/-! ## The conditional inner-`Γ` finiteness (item 1(b) — the corank peel on the freed integral) -/

/-- **`frobSq` of an empty-row matrix is `0`.** The zero pivot slot `Apiv := 0` used to feed the freed
pivot energy into the atom's strictly-positive core `w`. -/
theorem frobSq_empty_rows {q : ℕ} : frobSq (0 : Matrix (Fin 0) (Fin q) ℝ) = 0 := by
  simp [frobSq]

/-- **The freed inner-`Γ` integral is finite, conditionally on the outer-descent interface (item
1(b)).** For a fixed outer triple `x` and tail `Q`, over ANY domain `s`, the freed corank integral
`∫_{Γ∈s} (freedSchurLoss x Γ Q)^{−c'}` is finite provided:

* `hc'` — `c'` is above the block Morse threshold `a·b/2` (`a = #corank rows`, `b = #corank cols`);
* `hG` — the coupling `Q_b Q_bᵀ` is positive definite (`Q_b = Q.submatrix Sum.inr id`, full row rank);
* `hpiv` — the pivot energy `frobSq (P·Q̃ₚ)` (`P = of x.1.1`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`) strictly
  positive (the held core `w`).

Welds `freedSchurLoss = frobSq (P·Q̃ₚ) + frobSq (C·Q̃ₚ + Γ·Q_b)` onto the banked atom's shape
`w + frobSq Apiv + frobSq (Ccross + Γ·Qb)` at `w := frobSq (P·Q̃ₚ)`, `Apiv := 0` (`frobSq 0 = 0`),
`Ccross := C·Q̃ₚ`, `Qb := Q_b`, then applies `corankBlock_morsePeel_lt_top`. The three hypotheses are
the EXACT interface the outer `(S,J)` descent must supply as a measure statement (they fail
pointwise) — this lemma isolates them, it does not assert them. -/
theorem freedSchurLoss_inner_peel_lt_top {t a b q : ℕ}
    (x : SJOuter t a b) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' : ℝ)
    (hc' : (a * b : ℝ) / 2 < c')
    (hG : ((Q.submatrix Sum.inr id) * (Q.submatrix Sum.inr id)ᵀ).PosDef)
    (hpiv : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (s : Set (Fin a → Fin b → ℝ)) :
    ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')) < ⊤ := by
  have hatom := corankBlock_morsePeel_lt_top
    (Apiv := (0 : Matrix (Fin 0) (Fin q) ℝ))
    (Ccross := Matrix.of x.2 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
    (Qb := Q.submatrix Sum.inr id) hG c' hc'
    (w := frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) hpiv s
  rw [show (∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')))
      = ∫⁻ Γ in s, ENNReal.ofReal
          ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
                + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
            + frobSq (0 : Matrix (Fin 0) (Fin q) ℝ)
            + frobSq (Matrix.of x.2 * (Q.submatrix Sum.inl id
                  + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
                + (Matrix.of Γ) * Q.submatrix Sum.inr id)) ^ (-c')) from ?_]
  · exact hatom
  · refine lintegral_congr (fun Γ => ?_)
    congr 2
    rw [frobSq_empty_rows]
    unfold freedSchurLoss
    ring

/-- **The freed inner-`Γ` integral is finite on a finite-measure domain from core positivity alone
(item 1(c), the atom-inapplicable branch).** For a fixed outer triple `x` and tail `Q`, over ANY
FINITE-measure domain `s`, the freed corank integral `∫_{Γ∈s} (freedSchurLoss x Γ Q)^{−c'}` is finite
for ANY exponent `c' ≥ 0` — no Morse threshold, no coupling `PosDef` — provided only the pivot energy
`frobSq (P·Q̃ₚ)` is strictly positive. This is the branch the `(S,J)` descent uses on the `≈94/480`
charts where `c' < ½·minAdm M` does not force `c' > a·b/2` (the atom is inapplicable): the pivot energy
lower-bounds `freedSchurLoss` for EVERY `Γ` (drop the nonneg corank term), so the integrand is bounded
by the constant `(frobSq (P·Q̃ₚ))^{−c'}` (`Real.rpow_le_rpow_of_nonpos`, `-c' ≤ 0`), whose integral over
the finite box is `(frobSq (P·Q̃ₚ))^{−c'} · volume s < ⊤`. The shear-image box
`{Γ | Γ + schurShift x ∈ genBox}` is a translate of a box, hence finite measure, so this applies to the
actual peel domain. As with `freedSchurLoss_inner_peel_lt_top`, the pivot-energy positivity is EXPOSED
as the interface the outer descent supplies (it fails pointwise), not asserted. -/
theorem freedSchurLoss_inner_bounded_lt_top {t a b q : ℕ}
    (x : SJOuter t a b) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' : ℝ) (hc0 : 0 ≤ c')
    (hpiv : 0 < frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)))
    (s : Set (Fin a → Fin b → ℝ)) (hs : volume s < ⊤) :
    ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')) < ⊤ := by
  have hle : ∀ Γ : Fin a → Fin b → ℝ,
      frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
        ≤ freedSchurLoss x Γ Q := by
    intro Γ
    unfold freedSchurLoss
    exact le_add_of_nonneg_right (frobSq_nonneg _)
  calc ∫⁻ Γ in s, ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c'))
      ≤ ∫⁻ _Γ in s, ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c')) := by
        refine lintegral_mono (fun Γ => ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_nonpos hpiv (hle Γ) (neg_nonpos.mpr hc0)
    _ = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c'))
          * volume s := setLIntegral_const s _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hs

end DLNFibre.DLN.RLCT
