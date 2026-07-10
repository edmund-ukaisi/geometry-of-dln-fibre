**1. Route Ranking**

1. **A: Pi-split, Fubini, row-split, pivot translation. Commit to this.**

Verified local/API pieces: `MeasurableEquiv.piFinSuccAbove`, `volume_preserving_piFinSuccAbove`, local `eFront`/`measurePreserving_eFront`/`eFront_preimage_box`, `Measure.volume_eq_prod`, `setLIntegral_prod`, `MeasurePreserving.setLIntegral_comp_preimage_emb`, `MeasurableEquiv.sumPiEquivProdPi`, `volume_measurePreserving_sumPiEquivProdPi`, `measurePreserving_add_right`, `measurableEmbedding_addRight`, `lintegral_mono_set`.

Sequence:
- Restate `gammaPeelIntegral_sjGoodMap_eq` with explicit `sjDeepFactor`.
- Split `A' : Params (tailChain M)` into `(A'0, Adeep)` using `piFinSuccAbove 0`; the box becomes `matBox (M 1) (M 2) 1 ×ˢ paramsBoxM deeper 1`.
- Row-reindex `A'0` by `blockSplitEquiv κ`, then split rows by `sumPiEquivProdPi` into `(U, W)`, where `U` are pivot rows and `W` corank rows.
- For fixed `(Adeep, W, x, Γ)`, translate
  `v = U + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W`
  using `measurePreserving_add_right`.
- Rewrite `Matrix.of (Sum.elim (v - shift) W)` as `assembleFront x v W`.

Likely thrash: not the Jacobian. It is the domain bookkeeping:
`matBox` under row reindex/split and the sign convention in the translated domain
`{v | v - P⁻¹B₁₂W ∈ matBox t h 1}`. A secondary nuisance is `AEMeasurable` for `setLIntegral_prod`; follow the existing `chartInner_schurShearFree_eq` pattern.

2. **B: one fiberwise shear on `A'0`.**

Sequence:
- Define `frontShear x A1` that sends top rows to `top + P⁻¹B₁₂ * bottom`, bottom rows fixed.
- Prove measure-preserving either by row-splitting then `measurePreserving_shearSub`/`measurePreserving_coreShear`, or by a direct determinant-one linear equivalence.
- Transport the `A'0` integral in one shot.

Likely thrash: if proved directly, the determinant/linear-equivalence route is more fragile and less aligned with local code. If proved by row-splitting, it collapses back into route A while hiding the shifted-box domain. I would not use B unless A’s row-split API unexpectedly fights you.

**2. The Classical.choose Fix**

Do not try to prove
`Classical.choose (sjTail_factor ...) = explicitFactor`; the factor is not unique unless you add extra rank hypotheses. Restate the equality with the explicit witness.

Shape:

```lean
noncomputable def sjDeepFactor (M : Fin (L + 1 + 1 + 1) → ℕ)
    (A' : Params (tailChain M)) :
    Matrix
      (Fin ((tailChain M) ((0 : Fin (L + 1)).succ)))
      (Fin ((tailChain M) (Fin.last (L + 1)))) ℝ :=
  Matrix.reindex
    (finCongr (show Mtail (tailChain M) (0 : Fin (L + 1))
      = (tailChain M) ((0 : Fin (L + 1)).succ) from rfl))
    (finCongr (show Mtail (tailChain M) (Fin.last L)
      = (tailChain M) (Fin.last (L + 1)) from rfl))
    (prod (Mtail (tailChain M)) (Atail (tailChain M) A'))

theorem sjTail_factor_explicit
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ) (κ : Fin t ↪ Fin (M 1))
    (A' : Params (tailChain M)) :
    (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id
      = ((A' 0).submatrix (blockSplitEquiv κ) id) * sjDeepFactor M A'
```

Then prove:

```lean
theorem gammaPeelIntegral_sjGoodMap_eq_explicit
    (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c'
      = ∫⁻ A' in paramsBoxM (tailChain M) 1,
          ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
            ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
                Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
              ENNReal.ofReal
                ((sjGoodChartLoss x Γ ((A' 0).submatrix (blockSplitEquiv κ) id)
                    (sjDeepFactor M A')) ^ (-c'))
```

For the split, also add a wrapper `sjDeepFactorCore M Adeep` and a simp lemma saying `sjDeepFactor M ((tail-front-split).symm (A0, Adeep)) = sjDeepFactorCore M Adeep`.

**3. Good/Env Structure**

Use a quantitative good set, not mere invertibility. For example: `|det P| ≥ δ`, some `b×b` column minor of `W` has absolute determinant `≥ δ`, and some `h×h` column minor of `A2` has absolute determinant `≥ δ`.

After transport, the good piece should have the shape:

```lean
∫⁻ env in EnvBox ∩ Good δ,
  ∫⁻ Γ in Gdom x,
    ∫⁻ v in Vdom x W,
      ENNReal.ofReal ((sjGoodChartLoss x Γ (assembleFront x v W) A2) ^ (-c'))
```

where
`Gdom x = {Γ | Γ + schurShift x ∈ genBox _ _ 1}` and
`Vdom x W = {v | v - P⁻¹ * B12 * W ∈ matBox t h 1}`.

Then prove, for `env ∈ Good δ`:

```lean
inner env ≤ BallBound δ
```

by bounding the shifted `(Γ, v)` domain inside one fixed closed ball and applying the explicit ball endpoint `corner_block_lintegral_le`-style bound. The unit cube endpoint is not enough unless you generalize it to arbitrary radius; the domains are shifted boxes. Ball domination is the cleaner route.

Finally:

```lean
∫⁻ env in EnvBox ∩ Good δ, inner env
  ≤ ∫⁻ env in EnvBox ∩ Good δ, BallBound δ
  = BallBound δ * volume (EnvBox ∩ Good δ)
  < ⊤
```

Use `setLIntegral_mono_ae'`, `setLIntegral_const`, `ENNReal.mul_lt_top`, and finite box volume lemmas such as local `matBox_volume_lt_top` and `paramsBoxM_volume_lt_top`.

**4. Smallest Next Lemma**

Formalize the pivot-row translation first:

```lean
theorem sjGoodChartLoss_pivotRows_translate_eq {t a b h o : ℕ}
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ)
    (W : Matrix (Fin b) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) (c' : ℝ) :
    (∫⁻ U in matBox t h 1,
        ENNReal.ofReal
          ((sjGoodChartLoss x Γ (Matrix.of (Sum.elim U W)) A2) ^ (-c')))
      =
    ∫⁻ v in {v : Matrix (Fin t) (Fin h) ℝ |
        v - (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W ∈ matBox t h 1},
        ENNReal.ofReal
          ((sjGoodChartLoss x Γ (assembleFront x v W) A2) ^ (-c'))
```

Proof route: set `S := (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * W`, apply `measurePreserving_add_right volume (-S)` with `setLIntegral_comp_preimage_emb`, then `rfl`/`simp [assembleFront]`.

**5. Wall Check**

No mathematical wall in the transport itself. I agree this is labour.

The real failure mode is using only pointwise “good = invertible” data. Pointwise finite inner integrals do not imply the environment integral is finite. The good branch needs quantitative `δ`-good data or a uniform compactness argument producing a uniform sphere lower bound. The non-good branch then belongs to the banked charge inequality plus rank-flag recursion.