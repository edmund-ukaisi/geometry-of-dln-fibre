1. **HONEST** — Fact: `IsDeepLayers` mentions only fibre membership and layer ranks, not `rlctAt`; so D1/L2 are genuine claims. Unlike `argmin rlctAt`, D1 is not built into the definition.

2. **SOUND, conditional** — Fact: `Classical.choice` is arbitrary. Obligation: for every `w`, `IsDeepLayers H r B w → rlctAt H (dlnLoss H B) w = ofReal (aoyagiLambda H r)` and this value is the fibre inf, i.e. `∀ v ∈ optimalSet H B, rlctAt ... w ≤ rlctAt ... v`. Inference: plausible if all per-layer-rank-`r` fibre points are one regular gauge/analytic-equivalence class and Aoyagi monotonicity makes them minimizers; false if `IsDeepLayers` admits even one different-RLCT point.

3. **FLAG** — Fact: `Nonempty {w // IsDeepLayers ...}` is not vacuous or trivially inhabited; it requires an actual fibre point with all layer ranks `r`. But as stated `hB : B.rank = r` alone is under-hypothesized unless `r ≤ H s` for all layers / `B` is known realisable through the widths.

4. **SOUND, with packaging caveat** — Fact: D1 exactly states “the fibre-infimum is attained at `deepestPoint`,” not “all fibre points have that RLCT.” Inference: faithful to Aoyagi’s deepest-point reduction once the chosen point is genuinely deepest and the raw-loss-to-homogeneous-core/strata coverage reductions are proved; otherwise it packages more than the cited theorem alone.

**Bedrock?** Honest and non-circular, but not bedrock until the rank-feasibility hypothesis and the uniform “all `IsDeepLayers` choices are minimising with Aoyagi value” lemma are explicit/proved.