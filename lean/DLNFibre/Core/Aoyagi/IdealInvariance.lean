import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Analysis.RLCT.LocalMono
import DLNFibre.Core.Analysis.RLCT.Basic
import Meta.Cordon

/-!
# `Core.Aoyagi.IdealInvariance` — Object A: RLCT ideal-invariance (Aoyagi Lemma 1), two-sided

**BLUEPRINT (v3).** This module is a top-down *forecast*: every headline is `@[blueprint]`, and its
proof either composes lower forecasts or bottoms out at a `sorry` leaf that is **statement-locked and
honestly labelled** (strike-able proof-engineering vs. named analytic frontier). The gate is
elaboration + soundness of the *statements*, not a sorry-free build.

## The object (Aoyagi Lemma 1, corrected sign; worked.tex:153–165)

For analytic families `F : Fin m → (ℝⁿ → ℝ)` and `G : Fin p → (ℝⁿ → ℝ)`, if every `Gᵢ` lies in the
germ ideal `⟨F₁,…,F_m⟩` at `x` then
`rlctAt (∑ Gᵢ²) x ≤ rlctAt (∑ Fⱼ²) x`,
and if the two germ ideals are equal the RLCTs are equal. (The worked reproduction prints `≥` at
line 156; that is the paper's sign typo — the correct and Lean-checked direction is `≤`: a family
generating a *larger* vanishing set is *more* singular, so its threshold is *smaller*.)

`⟨F⟩ ⊇ ⟨G⟩` is encoded, at germ generality, by an **explicit continuous representation**
`Gᵢ = ∑ⱼ aᵢⱼ · Fⱼ` near `x` (`GermRepresents`). For polynomial/analytic `F, G` — the DLN case, where
the generators are matrix-product entries — this is *exactly* ideal membership in the local ring
(the coefficients are polynomials, hence continuous). Stating A over the representation keeps it TRUE
at full germ generality with no hidden analytic monument, and makes the pointwise domination
`∑ Gᵢ² ≤ C · ∑ Fⱼ²` a Cauchy–Schwarz + local-boundedness computation.

## The weighted carrier `wrlctAt` (the change-of-variables carrier for Object B)

`wrlctAt W K x` is the RLCT of `K` against a nonnegative analytic **weight** `W` in the measure:
`sSup { c ≥ 0 | w ↦ W w · K w ^(-c) integrable near x }`. This is the object the proper-map
change-of-variables of Object B produces (the Jacobian weight `W = |det Dg|`). Ideal-invariance is
inherited by the weighted form (multiply the pointwise comparison by the nonnegative `W`), which is
why A is stated in both forms and B rides the weighted one.

## The one genuine analytic leaf (named, not hidden)

`rlctAt_mono_of_ae_le` — germ-monotonicity of `rlctAt` under an a.e. domination `K ≤ K'` near `x`,
**without** a strict-positivity hypothesis. The banked `RLCT.localAdmissibleExponents_subset_of_le`
proves exactly this under `0 < K` near `x`; the singular RLCT setting has `K = ∑ Gᵢ²` vanishing on a
positive-dimensional germ, so the strict-positivity form does not apply and the zero-set (a
measure-zero real variety) must be handled a.e. This is standard-material proof-engineering
(measure-zero adjustment of the banked domination), NOT new mathematics — it is the module's single
strike-able frontier leaf and is decomposed to it explicitly.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {n : ℕ}

/-! ## Sum-of-squares germs and germ ideal membership -/

/-- The sum-of-squares germ `∑ᵢ (Fᵢ)²` of a finite family — the polynomial whose RLCT is Aoyagi's
`rlct⟨F⟩` (Def 1, `rlct_{w*}(J) = rlct(∑ Fᵢ²)`; worked.tex:143). -/
noncomputable def sumSqFam {m : ℕ} (F : Fin m → (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun w ↦ ∑ i, (F i w) ^ 2

/-- `∑ᵢ (Fᵢ w)² ≥ 0`. -/
lemma sumSqFam_nonneg {m : ℕ} (F : Fin m → (Fin n → ℝ) → ℝ) (w : Fin n → ℝ) :
    0 ≤ sumSqFam F w :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg _

/-- **Germ ideal membership by an explicit continuous representation.** `GermRepresents G F x`
holds when there are coefficient germs `aᵢⱼ`, continuous at `x`, with `Gᵢ = ∑ⱼ aᵢⱼ · Fⱼ` on a
neighbourhood of `x`. This is the honest germ-level encoding of `Gᵢ ∈ ⟨F₁,…,F_m⟩`: for
polynomial/analytic generators it is exactly local-ring membership (polynomial cofactors). -/
def GermRepresents {m p : ℕ} (G : Fin p → (Fin n → ℝ) → ℝ)
    (F : Fin m → (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ a : Fin p → Fin m → (Fin n → ℝ) → ℝ,
    (∀ i j, ContinuousAt (a i j) x) ∧
    (∀ᶠ w in 𝓝 x, ∀ i, G i w = ∑ j, a i j w * F j w)

/-! ## The strike-able analytic leaves (decomposed, statement-locked) -/

/-- **STRIKE-ABLE leaf — Cauchy–Schwarz + local boundedness.** From a continuous representation
`Gᵢ = ∑ⱼ aᵢⱼ Fⱼ` near `x`, the sum-of-squares germ of `G` is dominated by a constant multiple of
that of `F` near `x`: `∃ C ≥ 0, ∀ᶠ w in 𝓝 x, ∑ᵢ (Gᵢ w)² ≤ C · ∑ⱼ (Fⱼ w)²`. Pointwise
Cauchy–Schwarz gives `∑ᵢ (∑ⱼ aᵢⱼ Fⱼ)² ≤ (∑ᵢⱼ aᵢⱼ²)(∑ⱼ Fⱼ²)`; the coefficient sum `∑ᵢⱼ aᵢⱼ²` is
continuous at `x`, hence bounded on a neighbourhood. Proof engineering, no new mathematics. -/
@[blueprint]
theorem eventually_sumSqFam_le_of_germRepresents {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : GermRepresents G F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in 𝓝 x, sumSqFam G w ≤ C * sumSqFam F w := by
  -- map: A-domination (Cauchy–Schwarz + continuity boundedness of the coefficient sum)
  sorry

/-- **STRIKE-ABLE leaf — a.e. germ-monotonicity of `rlctAt` (no strict positivity).** If `0 ≤ K` and
`K ≤ K'` on a neighbourhood of `x` (with `K'` measurable), then `rlctAt K x ≤ rlctAt K' x`. The
banked `RLCT.localAdmissibleExponents_subset_of_le` is exactly this under the extra `0 < K` near `x`;
here `K = ∑ Gᵢ²` vanishes on a positive-dimensional germ, so the strict-positivity hypothesis fails
and the zero locus — a measure-zero real variety — is handled a.e. (`negPow` is `0` at a zero for
`c > 0`, so the domination `K'^(-c) ≤ K^(-c)` holds off the measure-zero zero set). Standard
measure-zero proof-engineering; decomposed from the banked lemma, not new mathematics. -/
@[blueprint]
theorem rlctAt_mono_of_ae_le {K K' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK'meas : Measurable K') (hbound : ∀ᶠ w in 𝓝 x, 0 ≤ K w ∧ K w ≤ K' w)
    (hbdd : BddAbove (localAdmissibleExponents K' x)) :
    rlctAt K x ≤ rlctAt K' x := by
  -- map: A-mono-ae (drop the 0<K hypothesis of localAdmissibleExponents_subset_of_le; measure-zero)
  sorry

/-- **STRIKE-ABLE leaf — positive scaling leaves `rlctAt` unchanged.** For `C > 0`,
`rlctAt (fun w ↦ C * K w) x = rlctAt K x`: `(C·K)^(-c) = C^(-c) · K^(-c)`, a positive constant
factor never affects local integrability. Proof engineering. -/
@[blueprint]
theorem rlctAt_const_mul {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {C : ℝ} (hC : 0 < C) :
    rlctAt (fun w ↦ C * K w) x = rlctAt K x := by
  -- map: A-scale (positive constant factor is integrability-neutral)
  sorry

/-! ## Object A — the two-sided ideal invariance (WIRED from the leaves) -/

/-- **Object A (≤), Aoyagi Lemma 1, corrected sign.** If every `Gᵢ` lies in `⟨F⟩` at `x`
(`GermRepresents G F x`), then `rlctAt (∑ Gᵢ²) x ≤ rlctAt (∑ Fⱼ²) x`. Wired: the representation
gives `∑ Gᵢ² ≤ C · ∑ Fⱼ²` near `x` (domination leaf); a.e. monotonicity gives
`rlctAt (∑ Gᵢ²) x ≤ rlctAt (C · ∑ Fⱼ²) x`; positive scaling collapses the constant. -/
@[blueprint]
theorem rlctAt_sumSqFam_le_of_germRepresents {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hFmeas : ∀ j, Measurable (F j)) (h : GermRepresents G F x)
    (hbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x)) :
    rlctAt (sumSqFam G) x ≤ rlctAt (sumSqFam F) x := by
  -- map: A-main (compose domination + a.e.-mono + scaling)
  sorry

/-- **Object A (=), two-sided ideal invariance.** If the germ ideals coincide (each family lies in
the other's ideal at `x`), the sum-of-squares RLCTs are equal: `le_antisymm` of the two `≤`
directions (`rlctAt_sumSqFam_le_of_germRepresents`). This is the foundational statement that
legalises every ideal-preserving step of Object B. -/
@[blueprint]
theorem rlctAt_sumSqFam_eq_of_germ_eq {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hGmeas : ∀ i, Measurable (G i)) (hFmeas : ∀ j, Measurable (F j))
    (hGbdd : BddAbove (localAdmissibleExponents (sumSqFam G) x))
    (hFbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x))
    (hGF : GermRepresents G F x) (hFG : GermRepresents F G x) :
    rlctAt (sumSqFam G) x = rlctAt (sumSqFam F) x :=
  -- map: A-two-sided (le_antisymm of both containments)
  le_antisymm (rlctAt_sumSqFam_le_of_germRepresents hFmeas hGF hFbdd)
    (rlctAt_sumSqFam_le_of_germRepresents hGmeas hFG hGbdd)

/-! ## The weighted RLCT `wrlctAt` and its ideal invariance (the CoV carrier for Object B) -/

/-- Exponents admissible for `K` **against a weight `W`** at `x`: `c ≥ 0` with
`w ↦ W w · K w ^(-c)` integrable near `x`. The weighted analogue of `localAdmissibleExponents`. -/
def wLocalAdmissibleExponents (W K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ IntegrableAtFilter (fun w ↦ W w * negPow K c w) (𝓝 x)}

/-- The **weighted local RLCT** `wrlctAt W K x`: `sSup` of the exponents admissible for `K` against
the nonnegative weight `W`. The object the proper-map change-of-variables of Object B produces (the
Jacobian weight `W = |det Dg|` enters the pulled-back integral). -/
noncomputable def wrlctAt (W K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (wLocalAdmissibleExponents W K x)

/-- The unweighted RLCT is the weight-`1` case (`W ≡ 1`): `wrlctAt 1 K x = rlctAt K x`. -/
@[blueprint]
theorem wrlctAt_one {K : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} :
    wrlctAt (fun _ ↦ (1 : ℝ)) K x = rlctAt K x := by
  -- map: A-weight-one (W ≡ 1 collapses to the unweighted admissible set)
  sorry

/-- **Object A (weighted ≤).** Weighted ideal-invariance: multiplying the pointwise comparison
`∑ Gᵢ² ≤ C · ∑ Fⱼ²` by the nonnegative weight `W` preserves it, so the weighted RLCTs compare the
same way. This is the form Object B's change-of-variables consumes. -/
@[blueprint]
theorem wrlctAt_sumSqFam_le_of_germRepresents {m p : ℕ} {W : (Fin n → ℝ) → ℝ}
    {G : Fin p → (Fin n → ℝ) → ℝ} {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w) (h : GermRepresents G F x) :
    wrlctAt W (sumSqFam G) x ≤ wrlctAt W (sumSqFam F) x := by
  -- map: A-weighted (nonneg-weight preserves the domination; a.e.-mono on the weighted integrand)
  sorry

end DLNFibre.Core.Aoyagi
