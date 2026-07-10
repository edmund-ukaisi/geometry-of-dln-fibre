Verified in the current tree: `gammaPeelIntegral` is the raw per-chart integral, `sjBoundaryPeel` is closed, `sjJointResolution` is the named remaining sorry, and the exact Schur split is banked. I treat your newer `_of_injective` endpoint as given.

**Ranking**

1. **C5: C2-forward, with explicit right inverses, not an iff.** Highest value/reachability: it packages the good-chart cross-coupled loss as one injective linear map, exactly what the endpoint wants, while avoiding CoV and rank-iff friction.
2. **C1, weakened to “full row rank/right inverse implies injective”.** Very reachable and reusable; the full `↔ rank Q = M1` is less valuable than the forward direction and needs annoying edge cases like zero row count.
3. **C4.** Useful plumbing if `good`/`deeper` predicates are already fixed, but lower leverage; otherwise you risk banking a cover over provisional definitions.
4. **C2 as stated with full iff.** Mathematically close to the endpoint, but the `iff` is extra risk and may need nonempty/dimension side conditions; the forward/right-inverse form is the tide-sized core.
5. **C3.** Highest assembly value but not tide-sized: it hides the measure transport, shear-domain handling, flattening, comparison to the corner cube, and endpoint firing.

**Top Pick**

I would bank the abstract good-chart linear map:

```lean
noncomputable def sjGoodLin {r p q h o : ℕ}
    (a : ℝ) (C : Matrix (Fin p) (Fin r) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ)
    (A2 : Matrix (Fin h) (Fin o) ℝ) :
    (Matrix (Fin p) (Fin q) ℝ × Matrix (Fin r) (Fin h) ℝ) →ₗ[ℝ]
      (Matrix (Fin r) (Fin o) ℝ × Matrix (Fin p) (Fin o) ℝ)
```

with theorem:

```lean
theorem sjGoodLin_injective_of_rightInverse {r p q h o : ℕ}
    {a : ℝ} (ha : a ≠ 0)
    (C : Matrix (Fin p) (Fin r) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ)
    (A2 : Matrix (Fin h) (Fin o) ℝ)
    (RW : Matrix (Fin h) (Fin q) ℝ) (hW : W * RW = 1)
    (RA : Matrix (Fin o) (Fin h) ℝ) (hA2 : A2 * RA = 1) :
    Function.Injective (sjGoodLin (a := a) (C := C) (W := W) (A2 := A2))
```

where `sjGoodLin (Γ, v) = (a • (v * A2), (C * v + Γ * W) * A2)`.

Proof steps:

1. Define `sjGoodLin`; prove linearity using matrix distributivity and scalar-mul lemmas.
2. Prove kernel-zero. From first component, `a • (v*A2)=0`; since `a≠0`, get `v*A2=0`.
3. Multiply right by `RA`: `v = v*(A2*RA) = 0`.
4. Second component becomes `(Γ*W)*A2=0`; multiply by `RA`, then by `RW`, to get `Γ=0`.
5. Conclude injectivity via `LinearMap.ker_eq_bot`.

Main friction risk: Lean matrix associativity/simp around product-valued linear maps, plus module placement. The existing rank-to-right-inverse lemma is currently in `D1HChartRank`; avoid an import cycle by proving the right-inverse version first, then add a rank corollary only if imports are clean.

**Hidden CoV Mountain**

C3 is the main “whole CoV in disguise”. C2 becomes mountain-sized only if you require the actual chart coordinate extraction, full rank-flag recursion, and iff converse. C4 is not CoV if kept as pure predicates and set inclusion.

Yes: bank endpoint-admissibility plus this one injective-good-loss brick, then report the remaining explicit CoV/resolution map as the mountain. That is the right leaf-executor move.