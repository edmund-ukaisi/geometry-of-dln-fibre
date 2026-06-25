**Verdict: (B) Separate Lemma**

Prereq-(a) is **not** the same object as `#111 / schur_chart_exists`.

**FACT:** `#111` is an origin/pivot-chart resolution statement for a reduced zero-product core:
`‖prod(C)‖² = monomial * ‖prod(C')‖²`.

**FACT:** prereq-(a) is a local analytic normal form at an arbitrary fibre point `v`, splitting
`F(v + W)` into:
`regular q-square block + homogeneous residual core`.

**INFERENCE:** Translating `#111` to `v` cannot supply this split. At arbitrary `v`, the generator has a nonzero Jacobian block of rank `q`, and that block must first be removed by a constant-rank/Morse-type normal form. `#111` resolves a core after one already has a zero-origin product-type core; it does not produce the regular block.

So D1>= is **not #111-gated**. It is gated on a separate local split hypothesis/theorem. Once that split is assumed, D1>= uses general analytic/RLCT facts and does not need the resolution of the core.

**Clean Lean Hypothesis Shape**

For the pointwise D1>= theorem, the clean hypothesis is:

```lean
LocalHomogeneousResidualSplitAt F generator v :=
  generator v = 0 ∧
  ∃ q Core OutCore,
  ∃ coord : AnalyticLocalEquiv (EuclideanSpace ℝ (Fin q) × Core) Param,
  ∃ core : Core → OutCore,
    coord 0 = v ∧
    q = rank (fderiv ℝ generator v) ∧
    AnalyticAt ℝ core 0 ∧
    core 0 = 0 ∧
    (∃ d : ℕ, 0 < d ∧ ∀ t z, core (t • z) = (t ^ d : ℝ) • core z) ∧
    (F ∘ coord =ᶠ[𝓝 0]
      fun xz => ‖xz.1‖^2 + ‖core xz.2‖^2)
```

Empty residual core should be allowed, e.g. `core = 0` on the residual/tangent variables, giving the pure regular case.

**Residual Core**

**FACT:** At generic smooth stratum points, the residual core is empty.  
**FACT:** At the deepest origin, the residual core is the whole zero-product chain `‖prod(C)‖²`.

**INFERENCE:** For D1>=, the residual core should be treated as an abstract homogeneous core, not as necessarily `‖prod(C')‖²`. If a separate local normal-slice theorem proves that this core is a smaller chain-product at its own origin, then `#111` can later apply to that core. But that is stronger than prereq-(a) and not needed for D1>=.

**All v vs Generic v**

D1>= is pointwise:

```lean
∀ v, generator v = 0 → rlctAt F deepestPoint ≤ rlctAt F v
```

So the split is needed for **all fibre points `v`**, or at least for every `v` not already handled by another pointwise argument. Generic stratum points are insufficient: they are exactly the easy residual-empty cases and do not cover singular fibre points, where the nonempty residual core appears.

**Clean Gating**

D1>= should be gated as:

```lean
∀ v ∈ fibre, LocalHomogeneousResidualSplitAt F generator v
```

plus the already established rank identity:

```lean
rank (Jac generator at v) = Mval(t_v)
```

and general analytic/RLCT lemmas: analytic-coordinate invariance, regular quadratic block contribution, homogeneity scaling, and monotonicity.

So: **separate (a)-split lemma; not #111; not purely general unless the homogeneous split itself is taken as a hypothesis.**