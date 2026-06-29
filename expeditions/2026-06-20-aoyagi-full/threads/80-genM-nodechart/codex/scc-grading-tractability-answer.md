**1. Finer Grading**
From your summary: the raw finer grading is **M-dependent**. A uniform formula `b : Fin N → ℕ` may still exist as a function of positional index plus widths, but it would not be a fixed-shape grading. The number and size of blocks vary with the descent/K-core ranks `t_s`.

So: **not impossible in principle**, but not “bounded” in the simple Lean sense. The SCC/frameB structure is not just `(layer, local coordinate kind)` with fixed cases; the K-coupling block changes size and membership with `M`.

ASSUMPTION: the per-boundary `t_s` are computed from the width profile by descent ranks/minima, not fixed constants.

**2. Middle Grading**
A `(layer, role)` grading is the only plausible middle route, but your evidence suggests it is insufficient unless “role” includes an M-dependent K-core membership predicate.

Follows from your summary: the K-coupling block is not decomposable into singleton/radial/chain pieces; it must remain one square block to expose determinants like `(z1 z4 - z2 z3)^2`. If `(layer, role)` puts all K-core coordinates together, it may be block-triangular, but the diagonal block is still an M-sized K-core determinant, not a fixed role monomial.

So the middle grading is tractable only if the local K-block determinant theorem is stated uniformly in `t_s`. Otherwise it collapses back into M-dependent SCC bookkeeping.

**3. Det-Comp Route**
Yes: the `det_comp` / product-of-CLMs route looks more tractable than one global SCC grading.

It avoids needing a single global condensation grading. Each fused triangular piece can have a local determinant lemma, with local block sizes depending on `M`, and the global result follows by

```lean
|det (f₁ * f₂ * ... * fₙ)| = ∏ |det fᵢ|
```

The prior disjoint-factor route failed because the chain coupling was not representable by independent factors. That does not kill this route: these factors would be **non-disjoint triangular frame pieces**, so coupling can live inside a factor or across ordered factors. The cost is proving the concrete equality `DFrame_M = productOfPieces_M`.

**4. Verdict**
Route b, as “one fused global block-tri determinant using an SCC/frameB-style grading,” is a **wall over opaque widths** unless you can exhibit a uniform grading whose diagonal blocks are exactly the local K-core/radial/chain determinant blocks.

The cheapest concrete check: run the same dependency/SCC extraction for a second width profile with different K-core behavior, e.g. `(2,3,2)` or `(4,2,2)`. Look for:

- whether SCC block sizes follow a simple formula from `t_s`;
- whether frameB-style determinant blocks match SCC blocks or require hand splitting/merging;
- whether a `(layer, role)` grading gives the same determinant blocks without inspecting the full graph.

If the second case again needs hand-tuned clumping different from raw SCC, treat global grading as a wall and move to the roadmap/operator `det_comp` route.