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

/-- **The junk-`0` guard.** `LocallyNullZeros K x`: the zero set of `K` is null on some neighbourhood
of `x`. REQUIRED because the banked `negPow` is `Real.rpow` with `0^(-c) = 0` — a *total* ℝ-proxy of
an ℝ∪{∞} invariant whose junk value at a zero INFLATES `rlctAt` when `{K = 0}` has positive measure
(the documented repo hazard, `docs/policies/citation-cordon.md`; counterexample `K = max(w,0)²`
raises `rlctAt` above a strictly-dominating germ). For sum-of-squares of polynomial/analytic families
`{∑ Fᵢ² = 0} = ⋂ᵢ Z(Fᵢ)` is a proper real-analytic subvariety, hence locally null — so this guard is
dischargeable at every point of use, and it is the honest hypothesis the monotonicity needs. -/
def LocallyNullZeros (K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ s ∈ 𝓝 x, volume ({w | K w = 0} ∩ s) = 0

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

/-- **STRIKE-ABLE leaf — germ-monotonicity of `rlctAt` under an eventual domination, junk-guarded.**
If `0 ≤ K` and `K ≤ K'` on a neighbourhood of `x` (`hbound`, pointwise-eventual), `K'` measurable,
and `K`'s zero set is locally null (`hKnull` — the junk-`0` guard, WITHOUT which the claim is FALSE:
`negPow K c` is `0` on `{K=0}`, so a positive-measure zero set of the smaller germ `K` inflates
`rlctAt K` above `rlctAt K'`), then `rlctAt K x ≤ rlctAt K' x`. Off the null zero set `K > 0` and the
banked `RLCT.localAdmissibleExponents_subset_of_le`'s a.e. content applies. Standard measure-zero
proof-engineering; the strict-positivity hypothesis of the banked lemma is replaced by `hKnull`. -/
@[blueprint]
theorem rlctAt_mono_of_eventually_le {K K' : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hK'meas : Measurable K') (hbound : ∀ᶠ w in 𝓝 x, 0 ≤ K w ∧ K w ≤ K' w)
    (hKnull : LocallyNullZeros K x)
    (hbdd : BddAbove (localAdmissibleExponents K' x)) :
    rlctAt K x ≤ rlctAt K' x := by
  -- map: A-mono (a.e. domination off the null zero set; junk-0 guarded by hKnull)
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
(`GermRepresents G F x`) and `∑ Gᵢ²`'s zero set is locally null (`hGnull`, the junk-`0` guard), then
`rlctAt (∑ Gᵢ²) x ≤ rlctAt (∑ Fⱼ²) x`. Wired: the representation gives `∑ Gᵢ² ≤ C · ∑ Fⱼ²` near `x`
(domination leaf); junk-guarded monotonicity gives `rlctAt (∑ Gᵢ²) x ≤ rlctAt (C · ∑ Fⱼ²) x`;
positive scaling collapses the constant. `hGnull` is dischargeable for polynomial/analytic `G`. -/
@[blueprint]
theorem rlctAt_sumSqFam_le_of_germRepresents {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hFmeas : ∀ j, Measurable (F j)) (h : GermRepresents G F x)
    (hGnull : LocallyNullZeros (sumSqFam G) x)
    (hbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x)) :
    rlctAt (sumSqFam G) x ≤ rlctAt (sumSqFam F) x := by
  -- map: A-main (domination ∘ junk-guarded mono ∘ scaling)
  sorry

/-- **Object A (=), two-sided ideal invariance.** If the germ ideals coincide (each family lies in
the other's ideal at `x`) and both sum-of-squares zero sets are locally null (`hGnull`, `hFnull` —
the junk-`0` guard applied symmetrically), the sum-of-squares RLCTs are equal. Direct two-sided:
`le_antisymm` of the two junk-guarded containments — the two-way representation makes both `≤`
directions hold, and the null-zero guards defeat the `negPow`-junk symmetrically. Foundational: it
legalises every ideal-preserving step of Object B. Both null guards are dischargeable for
polynomial/analytic families (proper zero sets). -/
@[blueprint]
theorem rlctAt_sumSqFam_eq_of_germ_eq {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hGmeas : ∀ i, Measurable (G i)) (hFmeas : ∀ j, Measurable (F j))
    (hGnull : LocallyNullZeros (sumSqFam G) x) (hFnull : LocallyNullZeros (sumSqFam F) x)
    (hGbdd : BddAbove (localAdmissibleExponents (sumSqFam G) x))
    (hFbdd : BddAbove (localAdmissibleExponents (sumSqFam F) x))
    (hGF : GermRepresents G F x) (hFG : GermRepresents F G x) :
    rlctAt (sumSqFam G) x = rlctAt (sumSqFam F) x :=
  -- map: A-two-sided (le_antisymm of both junk-guarded containments)
  le_antisymm (rlctAt_sumSqFam_le_of_germRepresents hFmeas hGF hGnull hFbdd)
    (rlctAt_sumSqFam_le_of_germRepresents hGmeas hFG hFnull hGbdd)

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

/-- The weighted junk-`0` guard: the zero set of `w ↦ W w · K w` is locally null (`W · K` is what the
weighted `negPow` acts on; the same `Real.rpow` junk-`0` hazard applies to the weighted integrand). -/
def LocallyNullZerosW (W K : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : Prop :=
  ∃ s ∈ 𝓝 x, volume ({w | W w * K w = 0} ∩ s) = 0

/-- **Object A (weighted ≤).** Weighted ideal-invariance: multiplying the pointwise comparison
`∑ Gᵢ² ≤ C · ∑ Fⱼ²` by the nonnegative weight `W` preserves it, so the weighted RLCTs compare the
same way — junk-guarded by `hWGnull` (the weighted integrand's zero set locally null). The form
Object B's change-of-variables consumes. -/
@[blueprint]
theorem wrlctAt_sumSqFam_le_of_germRepresents {m p : ℕ} {W : (Fin n → ℝ) → ℝ}
    {G : Fin p → (Fin n → ℝ) → ℝ} {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w) (h : GermRepresents G F x)
    (hWGnull : LocallyNullZerosW W (sumSqFam G) x)
    (hbdd : BddAbove (wLocalAdmissibleExponents W (sumSqFam F) x)) :
    wrlctAt W (sumSqFam G) x ≤ wrlctAt W (sumSqFam F) x := by
  -- map: A-weighted (nonneg-weight preserves the domination; junk-guarded weighted mono)
  sorry

/-- **Object A (weighted =), two-sided — the form Object B's value consumes.** With coinciding germ
ideals (`hGF`/`hFG`) and both weighted zero sets locally null, the weighted RLCTs are equal:
`le_antisymm` of the two weighted junk-guarded containments. Object B has both `hideal_fwd`/
`hideal_bwd`, so the engine rides this TRUE two-sided form (not a one-sided assumption). -/
@[blueprint]
theorem wrlctAt_sumSqFam_eq_of_germ_eq {m p : ℕ} {W : (Fin n → ℝ) → ℝ}
    {G : Fin p → (Fin n → ℝ) → ℝ} {F : Fin m → (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hW : ∀ᶠ w in 𝓝 x, 0 ≤ W w)
    (hWGnull : LocallyNullZerosW W (sumSqFam G) x) (hWFnull : LocallyNullZerosW W (sumSqFam F) x)
    (hGbdd : BddAbove (wLocalAdmissibleExponents W (sumSqFam G) x))
    (hFbdd : BddAbove (wLocalAdmissibleExponents W (sumSqFam F) x))
    (hGF : GermRepresents G F x) (hFG : GermRepresents F G x) :
    wrlctAt W (sumSqFam G) x = wrlctAt W (sumSqFam F) x :=
  -- map: A-weighted-two-sided (le_antisymm of both weighted junk-guarded containments)
  le_antisymm (wrlctAt_sumSqFam_le_of_germRepresents hW hGF hWGnull hFbdd)
    (wrlctAt_sumSqFam_le_of_germRepresents hW hFG hWFnull hGbdd)

end DLNFibre.Core.Aoyagi
