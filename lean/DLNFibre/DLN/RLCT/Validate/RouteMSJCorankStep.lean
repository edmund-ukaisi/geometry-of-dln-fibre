import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep` — the relative corank-step invariant

The single hardest sub-brick of the general-`(L,S,J)` single-radial blow-up chart lemma (the R-BLOWUP
route; `expeditions/2026-06-20-aoyagi-full/threads/genm-sjjoint-design/chart-lemma-probe.md`), at
**general (opaque) widths**. It composes two exact identities into one corank-decrementing step and
proves the *sequential-independence* invariant the design (and decorrelated Codex) named as the crux:
the introduced radials/chart-vars factor out as an overall scalar prefix, and the deeper term is
radial-free — this is why the resolution is sequential, not simultaneous.

The step, for a corank block `Δ = fromBlocks A B C D` (`A` the invertible `t × t` pivot) coupled to any
downstream product `Q`, under Aoyagi's Case-2 single radial blow-up `Δ ↦ u • Δ`:

    frobSq ((u • fromBlocks A B C D) · Q) = u² · ( frobSq (A · Q̃) + frobSq (C · Q̃ + Γ · Q_b) ),

`Q̃ := Q_p + A⁻¹ B Q_b`, `Γ := schurCompl A B C D = D − C A⁻¹ B` (the corank-decremented block),
`Q_p, Q_b` the pivot / non-pivot column rows of `Q`. Two exact, S2-FREE ingredients:

* the **radial factor** (Z-agnostic, any downstream `Q`): `frobSq ((u • M) · Q) = u² · frobSq (M · Q)`
  (`frobSq_smul_mul`, this file), and
* the **Schur block-elimination** `frobSq_schur_block_split` (`RouteMSJChartAlgebra`) — the corank
  block `Γ` genuinely cross-coupled with `C · Q̃`.

The **prefactor-preserving** form (`corankStep_prefactor`) carries an accumulated monomial prefactor
`pref` (Aoyagi's `∏ bᵢ²`) through: `pref · frobSq((u • Δ)·Q) = (pref · u²) · residual`. The radial `u`
and `pref` factor out as the single scalar `pref · u²`; the residual is `u`-free and `pref`-free — so a
*later* downstream blow-up multiplies a fresh `u'²` in without ever dividing the earlier prefix
(`corankStep_sequential`, the two-step accumulation witness). This is the exact algebraic realisation of
steps 1 + 3 of the chart-lemma probe; the measure-theoretic Morse peel of the pivot energy
`frobSq (A · Q̃)` (step 2's integration) is the banked `radial_morse_residual_power_le`, NOT part of this
pointwise identity.

S2-FREE: pure matrix algebra (`frobSq`, `smul_mul`, the Schur split); axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-! ## The radial factor — `frobSq` degree-2 homogeneity, Z-agnostic, general widths -/

/-- `frobSq` scales with degree 2 under an entrywise scalar (raw-function form, no `Matrix` `SMul`):
`frobSq (fun i j ↦ u · Mᵢⱼ) = u²·frobSq M`. Pure `ring` on the sum of squares. -/
theorem frobSq_smul_fun {a b : Type*} [Fintype a] [Fintype b] (u : ℝ) (M : a → b → ℝ) :
    frobSq (fun i j => u * M i j) = u ^ 2 * frobSq M := by
  unfold frobSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- **`frobSq` degree-2 homogeneity** `frobSq (u • X) = u² · frobSq X` under the `Matrix` scalar action
(entrywise). The radial coordinate `u` of a blow-up leaves the loss with degree exactly 2. -/
theorem frobSq_smul {a b : Type*} [Fintype a] [Fintype b] (u : ℝ) (X : Matrix a b ℝ) :
    frobSq (u • X) = u ^ 2 * frobSq X := by
  have hsm : (u • X : Matrix a b ℝ) = (fun i j => u * X i j) := by
    funext i j; simp
  rw [hsm, frobSq_smul_fun]

/-- **The single-radial factor (Z-agnostic).** For any matrix `M`, downstream product `Q`, and radial
scalar `u`: `frobSq ((u • M) · Q) = u² · frobSq (M · Q)`. Holds for ANY `Q` (Z-agnostic) at general
widths — the single radial factors cleanly out of the coupled product. `Matrix.smul_mul` pulls `u`
through the product, then `frobSq_smul`. -/
theorem frobSq_smul_mul {a m b : Type*} [Fintype a] [Fintype m] [Fintype b]
    (u : ℝ) (M : Matrix a m ℝ) (Q : Matrix m b ℝ) :
    frobSq ((u • M) * Q) = u ^ 2 * frobSq (M * Q) := by
  rw [Matrix.smul_mul, frobSq_smul]

/-! ## The relative corank step — radial blow-up ∘ Schur block-elimination -/

variable {t a b n : Type*} [Fintype t] [Fintype a] [Fintype b] [Fintype n] [DecidableEq t]

/-- **The relative corank step (exact, general widths).** Aoyagi's Case-2 single radial blow-up
`Δ ↦ u • Δ` of a corank block `Δ = fromBlocks A B C D` (invertible `t × t` pivot `A`), coupled to any
downstream `Q`, factors the loss as `u²` times the Schur-decomposed residual:

    frobSq ((u • fromBlocks A B C D) · Q) = u² · ( frobSq (A · Q̃) + frobSq (C · Q̃ + Γ · Q_b) ),

`Q̃ := Q_p + A⁻¹ B Q_b`, `Γ := schurCompl A B C D`, `Q_p := Q.submatrix Sum.inl id`,
`Q_b := Q.submatrix Sum.inr id`. The residual is `u`-free: the pivot energy `frobSq (A · Q̃)` (a Morse
block) and the corank-decremented residual `frobSq (C · Q̃ + Γ · Q_b)` (Schur complement `Γ`
cross-coupled with `C · Q̃`) carry no radial. Composes `frobSq_smul_mul` with the banked
`frobSq_schur_block_split`. -/
theorem corankStep (u : ℝ) (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] (Q : Matrix (t ⊕ b) n ℝ) :
    frobSq ((u • fromBlocks A B C D) * Q)
      = u ^ 2 * (frobSq (A * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id))
          + frobSq (C * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id)
              + schurCompl A B C D * Q.submatrix Sum.inr id)) := by
  rw [frobSq_smul_mul, frobSq_schur_block_split]

/-- **The prefactor-preserving corank step (the sequential-independence invariant).** With an
accumulated monomial prefactor `pref` (Aoyagi's `∏ bᵢ²`), the radial `u` and `pref` factor out as the
single scalar `pref · u²`, and the residual is BOTH `u`-free and `pref`-free:

    pref · frobSq ((u • fromBlocks A B C D) · Q) = (pref · u²) · ( residual ).

This is the load-bearing "relative resolution invariant": the earlier exceptional coordinates are
passive scalar prefixes on the active residual, never divided by the downstream resolution — the reason
the `(S,J)` resolution is sequential, not simultaneous. -/
theorem corankStep_prefactor (pref u : ℝ) (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] (Q : Matrix (t ⊕ b) n ℝ) :
    pref * frobSq ((u • fromBlocks A B C D) * Q)
      = (pref * u ^ 2) * (frobSq (A * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id))
          + frobSq (C * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id)
              + schurCompl A B C D * Q.submatrix Sum.inr id)) := by
  rw [corankStep, ← mul_assoc]

/-- **The two-step accumulation witness (non-vacuity of the sequential invariant).** A second corank
step, applied where the earlier radial `u₁²` is the accumulated prefix, multiplies the fresh radial
`u₂²` in as the product `u₁² · u₂²` — the deepest residual is free of BOTH radials. This is
`corankStep_prefactor` at `pref := u₁²`; it exhibits, in-file, that the radials of successive steps
accumulate as a product monomial and never divide one another (Aoyagi's `∏ bᵢ²`). -/
theorem corankStep_sequential (u₁ u₂ : ℝ) (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] (Q : Matrix (t ⊕ b) n ℝ) :
    (u₁ ^ 2) * frobSq ((u₂ • fromBlocks A B C D) * Q)
      = (u₁ ^ 2 * u₂ ^ 2) * (frobSq (A * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id))
          + frobSq (C * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id)
              + schurCompl A B C D * Q.submatrix Sum.inr id)) :=
  corankStep_prefactor (u₁ ^ 2) u₂ A B C D Q

end DLNFibre.DLN.RLCT
