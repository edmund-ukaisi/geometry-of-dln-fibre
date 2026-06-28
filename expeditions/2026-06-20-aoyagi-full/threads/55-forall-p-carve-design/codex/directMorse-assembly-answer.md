1. **Pick B. [LOW]**  
Reason: the full split variable `X = topRow + frobSq(Sc·S_bot)` gives the zero-guard from N2b’s upper bound; A’s `X = topRow` zero-guard is false pointwise.

2. **Chosen snag resolution. [LOW/MED]**  
Cleanest path is **not** the flat `k` reshape. Use the repo wrapper:

```lean
radial_morse_dominates_absZ_lt_top
  (μ := volume)
  (Ω := Fin (r-1) → Fin p → ℝ)
  (Z := matBox (r-1) p T)
  (W := fun S_bot => frobSq (rmatMul Sc S_bot))
```

with `m := p-1`, so `m+1 = p`, and `hZ := matBox_volume_lt_top (r-1) p T`. This avoids `matBox → morseBox` and avoids proving `W` measurable. Known repo fact, not Mathlib-v4.29 core.

If forced to use `radial_morse_dominates_lt_top`, add/verify:

```lean
matBox_flat_preimage :
  matBox m p T = (matToFlatEquiv m p) ⁻¹' morseBox (m*p) T

measurePreserving_matToFlatEquiv :
  MeasurePreserving (matToFlatEquiv m p) volume volume

measurable_W_flat :
  Measurable fun z : Fin (m*p) → ℝ =>
    frobSq (rmatMul Sc ((matToFlatEquiv m p).symm z))
```

`matToFlatEquiv (r n)` exists in repo; generic preimage name: verify.

3. **`X=0 → F=0`. [LOW]**  
For B, `hupp : F ≤ c₁ * X`; if `X=0`, then `F ≤ 0`, and `frobSq_nonneg` gives `F=0`. This is exactly the existing `schurSplit_lintegral_le` / `ofReal_rpow_le_const_mul` pattern.

For A, `topRow=0 → F=0` is false: e.g. `R = I`, top row of `S` zero, lower rows nonzero. Upper N2b only gives `F ≤ c₁ * residual`, not zero. A would need a separate a.e.-null zero-set workaround, not the existing pointwise lemma.

4. **Highest-risk step. [MED]**  
Arithmetic/index casting: instantiate the radial lemma with `m := p-1`, prove `(p-1)+1 = p`, positivity of `r*T`, and rewrite the `morseBox p (r*T)` radius after `stepShearP_r`.