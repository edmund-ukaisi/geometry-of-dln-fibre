**1. ROUTE Verdict: HYBRID**

**INFERENCE:** Use Route B’s flat composite for `composeFold fs = phiFlatLDU…kLDU`, but prove the nonlinear determinant lemmas through reusable block-local facts rather than through a full per-role `ChartIdx ≃ Block ⊕ Rest` bridge layer. **DERIVED:** The fixed-width anchors succeeded with short flat composites, so equality-to-chart is cheaper flat than via a new dependency-ordered CLE reindex tower. **INFERENCE:** Route A is more bounded only if you need the conjugated-block API itself; otherwise the opaque-width reindex design is the largest unbanked cost.

**2. Q1 + Q2**

**DERIVED:** The determinant telescope itself only needs each factor’s abs-det evaluated at the correct intermediate point; it does not logically require a `paramsBlockSplitCLE ρ`. **INFERENCE:** What the block structure buys is not telescoping, but an easy way to prove and state that a factor touches exactly the intended coordinates and has determinant `|det K_s|^{r+c}` or `∏ |q_{s,i}|^...`.

**DERIVED:** Since `readK_kLDU_det` already gives `det (readK (kLDU x) s) = ∏_i q_{s,i}`, the frame determinant can be read as a flat-coordinate monomial after rewriting through that lemma. **INFERENCE:** You still need a flat lemma identifying the frame factor’s determinant with `|det (readK … s)|^{r+c}` at the right intermediate point, but you do not need a per-role coordinate equivalence merely to turn `det K_s` into `∏ q`.

**3. First Lemma + Probe**

First lemma to build:

```lean
-- schematic shape
lemma frameFactor_abs_det_flat_kLDU
  (x : Fin (routeMAmbient M) → ℝ) (s : Boundary M) :
  abs_det_of_frameFactor_at_intermediate M s x
    =
  ∏ i, |qCoord M s i x| ^ (r_s + c_s) := by
  -- determinant of flat frame factor
  -- rewrite det(readK(kLDU x) s) by readK_kLDU_det
```

**INFERENCE:** This is the load-bearing de-risking step because it tests whether Route B can expose the Schur/frame determinant as a flat monomial without constructing `ρ`.

Cheapest fixed-width probe: do a non-anchor asymmetric case with at least one genuine Schur block and nontrivial LDU pivots, e.g. `(3,3,4)`, proving the flat frame determinant rewrites through the kLDU `readK` determinant into the expected monomial before generalizing opaque widths.