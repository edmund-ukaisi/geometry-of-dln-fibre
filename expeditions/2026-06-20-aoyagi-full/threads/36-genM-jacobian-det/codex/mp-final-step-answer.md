**Q1.** Use your candidate, but make it slightly sharper for Lean:

```lean
Pδ :=
  {u : Fin 4 → ℝ |
    u 0 ∈ Set.Icc (δ/2) δ ∧
    u 1 ∈ Set.Icc (-δ) δ ∧
    u 2 ∈ Set.Ioo 0 δ ∧
    u 3 ∈ Set.Icc (-δ) δ}
```

Use `Ioo 0 δ` for `z = u 2`; it avoids the pivot-zero boundary from the start. With `δ = ε/4`, containment is straightforward:

- `a = u 0 ≥ δ/2 > 0`, so the off-pole rate applies.
- `|b/a * sb| ≤ δ * δ / (δ/2) = 2δ`.
- `|z - (b/a) sb| ≤ δ + 2δ = 3δ < ε`.
- the other flat coordinates are bounded by `δ < ε`.

So `Pδ ⊆ phi121sm ⁻¹' cubeBox 4 ε`.

For divergence, the full-box lemma is **not enough directly**. It proves divergence on `[0,δ]^4`, but restricting `a` to `[δ/2,δ]` is passing to a smaller set; monotonicity goes the wrong way. In Lean, prove a restricted-box/z-axis divergence by Tonelli:

```lean
∫⁻ u in Pδ,
  ENNReal.ofReal (|((u 2)^2 * (u 0)^2)| ^ (-(c':ℝ))) = ⊤
```

Use `piFinSuccAbove` to peel coordinate `2`, then `setLIntegral_prod` or `lintegral_prod_mul`. The load-bearing analytic atom is the 1D lemma already present:

```lean
abs_rpow_lintegral_Ioo_eq_top
```

with exponent `-(2 * (c' : ℝ)) ≤ -1`, derived from `1/2 ≤ (c' : ℝ)`.

Certain Mathlib/local names in this checkout: `MeasurePreserving.setLIntegral_comp_preimage_emb`, `setLIntegral_prod`, `lintegral_prod`, `lintegral_prod_mul`, `lintegral_const_mul`, `lintegral_mul_const`, `Measure.volume_eq_prod`, `Measure.prod_restrict`.

**Q2.** The intersect route is mathematically valid but not actually slicker. You can show

```lean
[0,δ]^4 ∩ phi121sm ⁻¹' cubeBox 4 ε
```

still has infinite integral because it contains a positive-rest-measure strip such as

```lean
u0 ∈ [δ/2, δ], u1 ∈ [0, δ], u2 ∈ (0, δ), u3 ∈ [0, δ].
```

But proving that is exactly the sub-box argument. The existing full-box divergence does not automatically survive intersection with `phi ⁻¹' cubeBox`; in principle the intersection could remove the divergent region. Here it does not, but the proof is: exhibit the bounded-away-from-pole strip and run the z-Fubini divergence.

**Q3.** The clean reusable replacement for `image_subset` is not just containment. You need containment plus source divergence. Package it as a source certificate:

```lean
hsrc :
  ∀ ε : ℝ, 0 < ε →
    ∃ S : Set (Fin N → ℝ),
      MeasurableSet S ∧
      S ⊆ phi ⁻¹' cubeBox N ε ∧
      (∫⁻ u in S,
        ENNReal.ofReal (|routeMCore M (phi u)| ^ (-(c' : ℝ)))) = ⊤
```

Then the final calc is the whole MP step:

```lean
let g := fun x : Fin N → ℝ =>
  ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ)))

obtain ⟨S, hSmeas, hSsub, hSdiv⟩ := hsrc ε hε

have hpre :=
  hmp.setLIntegral_comp_preimage_emb hemb g (cubeBox N ε)

apply top_le_iff.1
calc
  (⊤ : ℝ≥0∞)
      = ∫⁻ u in S, g (phi u) := hSdiv.symm
  _ ≤ ∫⁻ u in phi ⁻¹' cubeBox N ε, g (phi u) :=
      lintegral_mono_set hSsub
  _ = ∫⁻ x in cubeBox N ε, g x := hpre
```

For M121, instantiate `S = Pδ` with `δ = ε/4`; prove `hSsub` by bounded-away-from-pole containment and `hSdiv` by the z-axis Tonelli lemma.

**RECOMMEND:** replace `image_subset` by a `preimage_source_diverges` hypothesis as above. For the rational MP chart, prove that hypothesis using `Pδ = {a∈[δ/2,δ], b∈[-δ,δ], z∈(0,δ), sb∈[-δ,δ]}` with `δ=ε/4`, then the final theorem is a three-line `setLIntegral_comp_preimage_emb` + `lintegral_mono_set` calc.