1. **Q1: INSUFFICIENT**  
A single pivot chart is not enough for equality: its image misses the positive-measure stratum `{A₀₀ = 0, A ≠ 0}` accumulating at `0`, so it is not a neighborhood germ, even modulo null sets. It can certify behavior on one chart image, but not local integrability of `|F|^{-c}` on a full neighborhood of `(0,0)`.

2. **Q2: SOUND**  
Yes: the correct general principle is finite-cover locality of local integrability, hence threshold over a finite cover is the infimum/minimum of the chart thresholds. Minimal lemma shape:

```lean
IntegrableOn f (⋃ i ∈ Finset, U i) μ ↔ ∀ i, IntegrableOn f (U i) μ
```

up to measurable/open hypotheses and local-neighborhood packaging. Then:

```lean
weightedThreshold F ρ {w}
  = ⨅ i, weightedThreshold (chart_i pullback of F)
                         (pulled weight * |det D chart_i|)
                         (chart_i ⁻¹' {w})
```

for a finite family whose images cover a neighborhood of `w` modulo null sets. Since all `mk` pivot charts are equivalent by row/column permutation, the inf collapses to the common value.

3. **Q3: INSUFFICIENT**  
The one-sided transport route only gives a bound. A non-surjective chart can show

```lean
rlctAtOn F 0 ≤ chartThreshold
```

or the corresponding direction depending on your lemma convention, but the reverse inequality needs control on the missing directions. Restricting to the chart image cannot prove integrability on a full neighborhood, because integrability over a subset does not imply integrability over the ambient neighborhood.

4. **Q4: SOUND**  
Yes: the honest equality for the general MIN fact requires the argmax/pivot cover machinery, or an equivalent finite local cover argument. The missing Lean surface is not the analytic transport lemma itself, but the glue layer: finite-cover locality for `weightedThreshold`, plus measurable/null bookkeeping for chart images and tie sets. If `g5_flat_cover` already has the lintegral additivity/local-cover infrastructure, the remaining gap is packaging it into a reusable `weightedThreshold_cover_min` lemma.

**ROUTE**

Build the cover. The cheapest sound path is:

```lean
rlctAtOn F 0
= ⨅ pivot : Fin (m*k), chartThreshold pivot
= min (mk / 2) (rlctAtOn core 0)
```

using `mk` pivot charts covering `{A ≠ 0}` together with the zero fiber, ignoring only null tie/boundary sets if using argmax cells. This is not single-chart. The minimal new lemma is a finite-cover `weightedThreshold` locality lemma: local integrability near `w` is equivalent to local integrability on each member of a finite neighborhood cover, hence thresholds combine by finite infimum/minimum.