1. **ROUTE.** **(B) squeeze-suffices** for the downstream RLCT split: the listed RLCT lemmas need only same-domain germ comparability plus a measure-preserving product reindex, not a non-MP gauge chart with `Dchart`/`HasFDerivAt`/`jac_unit`.  
Caveat: if the theorem statement still returns `DeepestGaugeChart`, Lean requires those fields by type, but they are dead weight for the RLCT split.

2. **MINIMAL DATUM.** Replace `DeepestGaugeChart` by a squeeze certificate roughly carrying:

```lean
structure DeepestSqueezeCert where
  split : Flat H ≃ₜ Reg × Core × Spect
  split_mp : MeasurePreserving split
  split_zero : split 0 = (0, 0, 0)

  Phi : Flat H → ℝ
  Phi_eq :
    Phi = fun x =>
      (∑ i, ((split x).1 i)^2) +
      dlnLoss M 0 (coreParams ((split x).2.1))

  loss_meas : Measurable flatLoss
  Phi_meas : Measurable Phi
  Phi_nonneg : ∀ᶠ x in 𝓝 0, 0 ≤ Phi x

  squeeze :
    ∃ U ∈ 𝓝 0, ∃ c₁ c₂ : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧
      ∀ x ∈ U, c₁ * Phi x ≤ flatLoss x ∧ flatLoss x ≤ c₂ * Phi x
```

If the proof wants to expose the algebra, add internal fields `regFun`, `coreFun`, and an ideal-membership/squeeze lemma, but the downstream consumer should see only the final `Phi` squeeze.

The spectator direction is handled by spectator-peel **after** a measure-preserving product reindex. So you still need an MP `split`, but only a linear/permutation/product split, not the nonlinear gauge chart.

3. **THE SUBTLETY.** From the cert, the squeeze is clearly valid for the **normalized model**

```lean
Φ_norm x = ∑ i, E_i x ^ 2 + ‖T̃₁ x ··· T̃_L x‖²
```

but it is **not automatically** valid for a clean additive model whose core is independent of regular/spectator variables.

The likely trap is assuming

```lean
‖T · (I - VY)⁻¹ · S‖²
```

is uniformly comparable to

```lean
‖T · S‖²
```

just because `(I - VY)⁻¹` is a bounded invertible matrix near `I`. Internal invertible insertions can change cancellations and zero sets; scalar unit-invariance does not cover this.

Missing fact needed for the squeeze route: an explicit local ideal-equivalence / two-sided bound showing the normalized core term is comparable to `dlnLoss M 0` in core coordinates independent of the regular block, or else a product-coordinate certificate using the `T̃` variables themselves.

4. **IF LITERAL CHART IS FORCED.** Cheapest decomposition:

1. `deepestGauge_chart_homeomorph`  
   Build the self-homeomorphism from layer block-elimination maps and flattening.  
   Lean API: `Homeomorph.mk`, composed with product/pi homeomorphisms.

2. `deepestGauge_loss_form_germ`  
   Prove the germ equality for `loss ∘ chart`.  
   Lean API: `Filter.EventuallyEq`, `Matrix.ext`, `Finset.sum_congr`.

3. `deepestGauge_Dchart_hasFDerivAt`  
   Package the derivative of the chart.  
   Lean API: `HasFDerivAt.comp` plus the matrix-inverse derivative/`ContDiff` API.

4. `deepestGauge_jac_unit`  
   Bound `|(Dchart x).det|` above and below near `0`.  
   Lean API: continuity + `ContinuousAt.eventually`, using nonzero determinant at `0`.

5. `deepestGauge_split_mp`  
   Prove the regular/core/spectator reindex is MP.  
   Lean API: finite coordinate permutation / product measure-preserving equivalences.

The dangerous part is that the requested `chart : Flat ≃ₜ Flat` with `hasDeriv : ∀ x, ...` is global, while block elimination is naturally only local near invertible blocks.

5. **LIKELY SINK.** For the recommended squeeze route: proving the final squeeze against the **canonical additive product model**, not merely against the normalized `E/T̃` model. The internal gauge unit `(I - VY)⁻¹` is the place this can fail.