1. **Yes.** Fact: `monomialThreshold` unfolds to an `sSup` over `IntegrableOn`, not to `1/2`; inference: in this proof, `monomial_rlct` is the only bridge from that analytic supremum to the arithmetic `⨅ axisRatio = 1/2`, so the dependency is not cosmetic.

2. **Validates:** `monomialThreshold 2 ![1,1] ![0,0]` agrees with `ENNReal.ofReal (aoyagiLambda ![1,1,1] 0)`, using S2 plus sorry-free arithmetic/kernel evaluation.

   **Does-not-validate:** by itself it does not prove `rlctAt (dlnLoss ...) = aoyagiLambda`; that needs the separate `rlctAt = monomialThreshold` bridge.

3. No obvious soundness concern from that scoping. Fact: the axiom only makes the threshold equality unconditional; the pole-order equality is guarded by `∃ j, k j ≠ 0`. Mathematically, with the stated `ℝ≥0∞` convention, all-zero `k` gives every `axisRatio = ⊤`, matching an integrand independent of `c` and threshold `⊤`; the order claim is exactly the part that would be suspicious in the nonsingular/unit case, and it is not asserted there.