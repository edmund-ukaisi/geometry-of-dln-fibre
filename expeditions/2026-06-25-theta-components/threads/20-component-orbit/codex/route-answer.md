**Verdict:** do **not** try to prove the current exact target by transporting a component through the count chain. The clean route is to relax the consumer to accept a smooth polynomial/smooth factor, then prove an intrinsic fibre-component statement of the form

```lean
sweepFibreRing ⧸ I ≃ₐ[k] MvPolynomial η (orbitRing M)
```

or an abstract smooth fp domain, not necessarily a bare `orbitRing M`.

The dimension trap is real. The chart identity already records

```text
dim Σ^r = dim F + δ
δ = r * (d_last + d_0 - r)
```

see [ChartSweepWiring.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/ChartSweepWiring.lean:15) and the theorem at [ChartSweepWiring.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/ChartSweepWiring.lean:117). The persisted `(2,2,2), r=1` check is decisive: fibre top components have dimension `4`, while the residual zero-product orbit components for `d-r=(1,1,1)` have dimension `1`; the missing dimension is `δ=3`. So a bare shifted orbit closure is too small. It is orbit closure **times an affine factor**.

For labelled transport, the minimum prime-level route is:

1. `I` in `sweepFibreRing`.
2. `map C I` in `O(F)[Schur]` using the polynomial prime correspondence already built in [TopDimMinPrimesPoly.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/TopDimMinPrimesPoly.lean:107).
3. localize at `gF`, via `map`/`comap` survival in [TopDimMinPrimesLocalization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/theta-components/lean/DLNFibre/Core/TopDimMinPrimesLocalization.lean:194).
4. transport across `chartLocalizedAlgEquiv`.
5. descend from `dsig` localization to `O(Σ^r)`.
6. use W0 set equality to land in `topComponents`, then `exists_kostantPartition_partitionIdeal_eq_of`.

That labels the component. It does **not** give `O(F)/I ≃ orbitRing M`; polynomial extension and localization have changed the component coordinate ring.

Which rungs need quotient `AlgEquiv`s? Polynomial, localization, and chart do if you want ring geometry, but they give localized/polynomial component rings. W0 and sigma labelling are prime/set-level. The missing theorem is not a transport lemma; it is an intrinsic block-triangular fibre theorem identifying the reduced component with residual orbit closure plus affine variables.

Recommended target change:

```lean
(sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k]
  MvPolynomial η (orbitRing M)
```

Then prove smoothness of the RHS from `OrbitSmooth` plus polynomial smoothness. This is mathematically aligned with the chart notes and avoids a false cancellation of the affine factor.

Line-count tier: labelled prime bijection only, ~300-700 LoC. Intrinsic component-as-`orbitRing[M][η]`, ~800-1800 LoC. Current bare-`orbitRing` target is high-risk and likely false for the natural `M`; the hardest rung is the intrinsic vanishing-ideal/coordinate-isomorphism equality for each component.