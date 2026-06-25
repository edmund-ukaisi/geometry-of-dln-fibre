**Q1**

Rank: **(a) first, (b) only as a presentation layer.**

Use Lemma-2 as a measure-preserving homeomorphism between step 1 and step 2. Internally, prove the cover by chaining:

`step1 pivot` → `L2_p.symm reindex, det = ±1` → `step2 pivot` → optional `step3 pivot`.

Decisive reason: `g5_pivotNode` stays a pure pivot-node theorem. If you absorb L2 into step 1, you either stop using `g5_pivotNode` directly or you have to reprove composite chart image/injectivity/domain facts. With (a), the Jacobian ledger is literally:

`x^3 · 1 · s^2 · u^3`.

For the final leaf API, you can still define

`φ_leaf = φ₁_p ∘ L2_p.symm ∘ φ₂_q [∘ φ₃_r]`

so the theorem statement looks absorbed. But the proof should keep L2 as a separate deterministic reindex.

Use a state-style proof object: current map `Φ`, current Jacobian weight `J`, current domain/indicator `D`. A pivot node updates by composing with `pivotBlowupOn`; L2 updates by composing with `L2_p.symm` and multiplying Jacobian by `1`.

Confident local/Mathlib names: `g5_pivotNode`, `pivotBlowupOnDeriv_det`, and Mathlib’s `lintegral_image_eq_lintegral_abs_det_fderiv_mul` are real in this project/import path. Mathlib documents the latter as the lintegral change-of-variables theorem with the determinant weight. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/Jacobian.html))

**Q2**

Do **not** try to prove the leaf integrand equals bare `monomialIntegrand` if the residual unit is nonconstant. The true statement is:

`leafIntegrand c u = monomialIntegrand d k h c u * |unit u|^(-c)`.

Then prove the threshold is unchanged by the unit.

You have the concept already: `rlct_unit_invariant_aux` / `Skeleton.rlct_unit_invariant` is the correct S1.3 idea, with the required `Measurable u` and local bounds. But its current shape is `Params`/unweighted `rlctAt`. For this concrete leaf bridge, add a small new weighted/fixed-box corollary rather than forcing the existing theorem.

Recommended lemma shape:

```lean
theorem integrableOn_monomial_mul_unit_iff
    (d : ℕ) (k h : Fin d → ℕ) (unit : (Fin d → ℝ) → ℝ)
    (S : Set (Fin d → ℝ)) (c : NNReal)
    (hmeas : Measurable unit)
    (ha : 0 < a) (hb : 0 < b)
    (hunit : ∀ᵐ u ∂(volume.restrict S), a ≤ |unit u| ∧ |unit u| ≤ b) :
    IntegrableOn
      (fun u => monomialIntegrand d k h (c : ℝ) u * |unit u| ^ (-(c : ℝ)))
      S volume
    ↔
    IntegrableOn (monomialIntegrand d k h (c : ℝ)) S volume
```

Then derive:

```lean
theorem monomialThreshold_withUnit_eq
    ... :
    sSup {c | ∃ c' : NNReal, c = c' ∧
      IntegrableOn
        (fun u => monomialIntegrand d k h (c' : ℝ) u * |unit u| ^ (-(c' : ℝ)))
        (unitBox d) volume}
      = monomialThreshold d k h
```

This is the crux. Without this lemma, the claim “leaf threshold = `monomialThreshold`” is not justified. The equality-to-bare-monomial statement is false unless the unit is identically `1`.

Per leaf, prove only:

```lean
F ∘ φ_leaf = monomial * unit
|det Dφ_leaf| = ∏ j, |u j| ^ h j
unit measurable
unit bounded above and below on the chosen local box
```

For units like `1 + Σ z^2`, use explicit bounds. For a general analytic unit with `unit 0 ≠ 0`, use continuity to get e.g. `[1/2, 3/2]` after shrinking.

**Q3**

Yes: do a representative leaf first. If only one, choose a **block leaf**, because it exercises all three pivot levels plus L2. Practically, prove one unit leaf too before expanding to 24, because the E/F0 terminal algebra is a different branch.

Unit-invariance should be **abstract once**, not per-leaf. Per-leaf proofs should only discharge algebra and bounded-unit hypotheses. Then enumerate the leaves as:

```lean
inductive Leaf
| unit  : APivot → Fin 2 → Leaf   -- 4 * 2 = 8
| block : APivot → Fin 4 → Leaf   -- 4 * 4 = 16
```

Load-bearing risk: the unit lemma must be applied on the actual localized leaf domain/box used for the threshold comparison. Do not apply it on an unbounded chart domain unless you have a real upper bound for the unit there.