**Q1**

Use the `RadialMPChart` assembly, but make the source certificate **weighted**. The clean proof order is:

1. write the chart as `φ = ψ ∘ R`, where `ψ := Q ∘ shear` is the rational but measure-preserving/measurable-embedding part;
2. use `ψ` by `MeasurePreserving.setLIntegral_comp_preimage_emb`;
3. use the Jacobian c-o-v only for `R`;
4. finish from a preimage source set `S ⊆ (ψ ∘ R) ⁻¹' cubeBox N ε`.

So the reusable hypothesis should not be “`φ` is MP” and should not be a global `image_subset`. It should be:

```lean
ψ R : (Fin N → ℝ) → (Fin N → ℝ)
p : Fin N
h : ℕ                         -- h = minAdm M - 1
D : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)

hmp   : MeasurePreserving ψ volume volume
hemb  : MeasurableEmbedding ψ

hsrc :
  ∃ S : Set (Fin N → ℝ),
    MeasurableSet S ∧
    S ⊆ (fun u => ψ (R u)) ⁻¹' cubeBox N ε ∧
    (∀ u ∈ S, HasFDerivWithinAt R (D u) S u) ∧
    InjOn R S ∧
    (∀ u ∈ S, |(D u).det| = |u p| ^ h) ∧
    (∫⁻ u in S,
      ENNReal.ofReal (|u p| ^ h) *
        ENNReal.ofReal (|routeMCore M (ψ (R u))| ^ (-(c' : ℝ)))) = ⊤)
```

The key is that the rational `ψ` is never differentiated. The only Jacobian is carried by `R`.

**Q2**

Yes, the radial Jacobian is absorbed into the binding-axis divergence, but no, this does not let you reuse the unweighted MP lemma.

For non-MP `φ`, the lower bound must contain the Jacobian:

```text
g(φ u) · |det DR u|
```

With `h = minAdm - 1` and `loss ∘ φ = z² U`, the binding exponent is

```text
h - 2c' = minAdm - 1 - 2c' ≤ -1
```

from `c' ≥ minAdm / 2`. Thus the one-dimensional integral over `z ∈ (0, δ)` is still infinite. This is exactly the calibrated threshold. But you must prove the **weighted** divergence; unweighted divergence does not imply weighted divergence by monotonicity, since `|z|^h` shrinks near `0`.

**Q3**

For `φ = ψ ∘ R`, the calc skeleton is:

```lean
let B := cubeBox N ε
let g := fun x => ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ)))

obtain ⟨S, hSmeas, hSpre, hRderiv, hRinj, hRdet, hSdiv⟩ := hsrc

have hψ :
    ∫⁻ y in ψ ⁻¹' B, g (ψ y) = ∫⁻ x in B, g x :=
  hmp.setLIntegral_comp_preimage_emb hemb g B

have hRimage : R '' S ⊆ ψ ⁻¹' B := by
  rintro y ⟨u, hu, rfl⟩
  exact hSpre hu

have hcov :
    ∫⁻ y in R '' S, g (ψ y)
      = ∫⁻ u in S, ENNReal.ofReal |(D u).det| * g (ψ (R u)) := by
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul
    volume hSmeas hRderiv hRinj (fun y => g (ψ y))

have hcov' :
    ∫⁻ y in R '' S, g (ψ y)
      = ∫⁻ u in S, ENNReal.ofReal (|u p| ^ h) * g (ψ (R u)) := by
  rw [hcov]
  refine setLIntegral_congr_fun hSmeas ?_
  intro u hu
  rw [hRdet u hu]

apply top_le_iff.1
calc
  (⊤ : ℝ≥0∞)
      = ∫⁻ u in S, ENNReal.ofReal (|u p| ^ h) * g (ψ (R u)) := hSdiv.symm
  _ = ∫⁻ y in R '' S, g (ψ y) := hcov'.symm
  _ ≤ ∫⁻ y in ψ ⁻¹' B, g (ψ y) := lintegral_mono_set hRimage
  _ = ∫⁻ x in B, g x := hψ
```

If the actual Lean definition is still `φ = Q ∘ radial ∘ shear`, do not silently use `ψ := Q ∘ shear`. Either refactor to the mathematically intended `φ = (Q ∘ shear) ∘ radial`, or use the slightly heavier three-stage version: `Q` MP, then radial COV on `shear '' S`, then shear MP. The clean two-stage lemma requires the radial to be the source-side non-MP piece.

Mathlib name confidence: `MeasurePreserving.setLIntegral_comp_preimage_emb` and `lintegral_image_eq_lintegral_abs_det_fderiv_mul` match the banked local usage. For the 1D atom, `abs_rpow_lintegral_Ioo_eq_top` is the right shape if present locally; otherwise prove a wrapper for `∫⁻ z in Ioo 0 δ, ofReal (|z| ^ α) = ⊤` when `α ≤ -1`.

RECOMMEND: implement `routeMCore_box_diverges_of_RadialMPChart` with `φ = ψ ∘ radial`, `ψ` MP+embedding, radial COV on the certified preimage source `S`, and a weighted source-divergence hypothesis. It conceptually subsumes the minAdm=1 MP lemma by taking `radial = id` and `h = 0`, but keep the MP lemma as the lighter corollary/sibling for weight-one charts.