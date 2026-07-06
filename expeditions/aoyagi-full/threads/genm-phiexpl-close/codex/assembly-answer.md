Q1. **YES**, given your stated `recoverProduct` definition.  
The reduced factor is exactly `Q.1.₂₂ * Q.2.₂₂ = (W + C.1.₂₂)(V + C.2.₂₂)`, and `X,Y,U` are spectators. A shear would only be needed if the chart fed `recoverProduct` Schur-adjusted layer coordinates rather than these stored raw `₂₂` corners.

Q2. Cleanest: **choose a global `G` agreeing germwise with `Matrix.inv` near `Br.₁₁`**, then define `qₑ` with `G(S+Br.₁₁)`. This preserves global `ContDiff ℝ 1` while keeping the slice `p=0` polynomial after using `G Br.₁₁ = Br.₁₁⁻¹`.

Most likely Lean pitfall: not smoothness itself, but **coercion/reindex friction** between matrices, finite Pi spaces, and `EuclideanSpace ℝ (Fin n)`. Matrix multiplication is polynomial/continuous-differentiable in principle, but the flattening equivalence and block reads must be packaged so `ContDiff` composes without painful extensional rewrites. Mathlib lemma availability for your exact `Matrix.inv` globalisation route needs checking.

The Schur step is mathematically correct: if `Br.₁₁` is invertible and `rank Br ≤ r` with an `r × r` pivot block, then `Br.₂₂ = Br.₂₁ Br.₁₁⁻¹ Br.₁₂`.

Q3. **YES**, assuming your banked `rlctAtOn_comp_homeomorph` really accepts this homeomorphism/measurability package.  
You only need equality as a germ near `(0,t0)`, since `G = inv` there and `rlctAtOn_congr_germ` erases the replacement. The measure-preserving part is only a risk if `ρ` includes translations/permutations/scalings not already normalized to determinant absolute value `1`; a general linear equiv is not automatically MP.

Q4. Risk ranking:

1. **Measure-preserving `ρ`**: cheapest check is prove the actual coordinate map is only permutation plus translations, no scaling; otherwise MP may fail.
2. **Global `G` construction**: test a tiny standalone lemma `∃ G, ContDiff ℝ 1 G ∧ G =ᶠ[𝓝 Br₁₁] Matrix.inv`.
3. **Flattening `qₑ` smoothness**: prototype the `ContDiff` proof for one matrix product flattened to `Fin`.
4. **`hRne` a.e. nonvanishing**: verify the reduced product polynomial is nonzero under your positivity assumptions. This is the most theorem-library-sensitive part, not the main math.