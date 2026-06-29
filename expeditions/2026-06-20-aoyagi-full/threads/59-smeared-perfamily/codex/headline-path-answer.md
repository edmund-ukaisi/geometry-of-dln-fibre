1. **Pick ROUTE-CONTRACT.**  
Fact from your prompt: you already have the L=2 rate, `measurePreserving_shearM`, and generic `pivotBlowupOn` determinant/injectivity/fderiv facts; ROUTE-NODECHART still requires the hard rational `cov` field. Inference: ROUTE-CONTRACT is less total work for opaque widths. Its remaining work is painful but local: containment A and z-axis divergence B. ROUTE-NODECHART risks rebuilding the hardest rational change-of-variables layer over opaque `Fin` widths, which is likely more work and more fragile than proving one chart factorization plus reusable axis-peel lemmas.

2. **Keep `phiL2`; prove `phiL2 = ψ ∘ R`.**  
Do not redefine the chart and rederive the rate unless equality is genuinely false. The banked rate is the expensive artifact; transport it across a factorization lemma. The key obstacle is the coordinate convention for `pivotBlowupOn`: it usually leaves the pivot coordinate as `z` and sends the other selected coordinates to `z * hᵢ`. Your `phiL2` formula looks like a full external scaling `z · H̄`. So the equality proof hinges on aligning the pivot/angular layout: either one angular coordinate is implicitly fixed to `1`, or your `H̄` block excludes the pivot, or you need a small adapter map. If `H̄` is literally a free full block including the pivot coordinate, then `phiL2 = ψ ∘ R` is not literally true for standard pivot blowup; verify this first.

3. **Yes, B should be abstracted once.**  
State the reusable theorem in terms of an axis box and a quadratic upper bound, not `M`.

Sketch:

```lean
theorem axisPeel_diverges_of_quadratic_rate
    {E : Type*} [MeasurableSpace E] [MeasureSpace E]
    (S : Set (ℝ × E)) (T : Set E)
    (δ C h c' : ℝ)
    (F U : ℝ × E → ℝ)
    (hS : S = {u | 0 < u.1 ∧ u.1 < δ ∧ u.2 ∈ T})
    (hδ : 0 < δ)
    (hTmeas : MeasurableSet T)
    (hTpos : 0 < volume T)
    (hC : 0 < C)
    (hc' : 0 < c')
    (hexp : h - 2 * c' ≤ -1)
    (hRate : ∀ u ∈ S, F u = u.1 ^ 2 * U u)
    (hUpos : ∀ u ∈ S, 0 < U u)
    (hUbdd : ∀ u ∈ S, U u ≤ C) :
    ∫⁻ u in volume.restrict S,
      ENNReal.ofReal ((|u.1| ^ h) * (|F u| ^ (-c'))) = ∞
```

For Lean, I would probably prove an even smaller core lemma from `0 < F u ∧ F u ≤ C * u.1^2`; then derive the `F = z²·U` version from `0 < U ≤ C`. Verify Mathlib’s exact `Real.rpow`/`ENNReal.ofReal` behavior at zero; keep `z ∈ (0, δ)` and `U > 0` to avoid relying on singular-point conventions.

4. **Cheapest honest ceiling: one contract-rate interface theorem.**  
Make a theorem that packages ROUTE-CONTRACT plus the reusable axis peel, leaving only chart geometry as named hypotheses.

```lean
theorem routeMCore_box_diverges_of_L2_contractRate
    (M : ...)
    (ψ R : ...)
    (D : ...)
    (p : ...)
    (h c' ε δ C : ℝ)
    (S : Set Source)
    (T : Set Rest)
    (U : Source → ℝ)
    (hmp : MeasurePreserving ψ)
    (hemb : MeasEmbedding ψ)
    (hSmeas : MeasurableSet S)
    (hSpre : S ⊆ (fun u => ψ (R u)) ⁻¹' cubeBox N ε)
    (hRderiv : ...)
    (hRinj : ...)
    (hRdet : ∀ u ∈ S, |det (D u)| = |u p| ^ h)
    (hAxis : S = {u | 0 < u p ∧ u p < δ ∧ rest u ∈ T})
    (hTmeas : MeasurableSet T)
    (hTpos : 0 < volume T)
    (hRate :
      ∀ u ∈ S,
        routeMCore M (ψ (R u)) = (u p)^2 * U u)
    (hUpos : ∀ u ∈ S, 0 < U u)
    (hUbdd : ∀ u ∈ S, U u ≤ C)
    (hexp : h - 2 * c' ≤ -1) :
    ∫⁻ x in volume.restrict (cubeBox N ε),
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ∞
```

Then the full opaque-width headline reduces to proving: factorization/rate transport, containment A, and `U` bounds on the chosen source box. That names the real gap without redoing measure theory or hiding a `sorry` inside the final divergence statement.