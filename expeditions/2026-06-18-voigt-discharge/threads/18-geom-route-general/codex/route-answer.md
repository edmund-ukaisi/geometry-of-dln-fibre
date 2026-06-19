I checked the pinned Mathlib `v4.29.0` sources locally.

**1. ROUTE A General-Chart**
**SUB-LIBRARY.**

The general chart is not a bounded lemma for arbitrary barcode/rank pattern. The hard step is:

`localized graph ideal = localized orbit/closure ideal` for an arbitrary bar-list.

Why: pivot selection varies with the barcode incidence, and after choosing pivots you still must prove every residual rank/minor/normal-form equation lies in the graph ideal by explicit Laurent identities. That is matrix-Schubert-cell-like infrastructure: canonical pivots, denominator bookkeeping, Laurent cofactor identities, and ideal membership without Gröbner automation. The 2x2x2 certified case does not scale as a template unless you build this whole combinatorial cell API.

**2. ROUTE B Homogeneity**
(i) **Spec-detour generic smoothness:** **BOUNDED for nonempty smooth locus; false for direct generic-to-`m_M`.**

Known in Mathlib v4.29: scheme-side `Scheme.Hom.dense_smoothLocus_of_perfectField`, ring-side `Algebra.smoothLocus`, and the affine bridge `formallySmooth_stalkMap_iff` exist. So `Spec A → Spec k` plus reduced finite-presentation hypotheses is a bounded setup.

But `genericPoint ∈ smoothLocus` does **not** imply `m_M ∈ smoothLocus`. Openness gives stability under generalization, not specialization. To get a smooth closed `k`-point, use density + Jacobson/closed-points machinery; Mathlib has the relevant ingredients (`LocallyOfFiniteType.jacobsonSpace`, `pointEquivClosedPoint`, `nonempty_inter_closedPoints`). That part is bounded once `O_M` is actually modeled as a finite-type reduced scheme.

(ii) **G-stability via algebra automorphisms:** **BOUNDED, if kept ring-side.**

For each `P : G(k)`, build the induced `k`-algebra automorphism of the coordinate ring and prove it sends `m_A` to `m_{P • A}`. Preservation of `IsSmoothAt` then follows from existing formal-smoothness invariance under isomorphism/localization. I infer no absent Mathlib brick here. Scheme/group-object modeling would be much heavier and unnecessary.

(iii) **Transitivity step:** **BOUNDED after (i) and (ii).**

Once you have one smooth closed `k`-point of the orbit and an automorphism action preserving smoothness, your existing transitivity theorem moves it to `M`. The only modeling cost is exposing the closed point as an actual tuple in `O_M`.

(iv) **L2 differential = tangent:** **ABSENT-BRICK.**

Mathlib has `Ideal.Cotangent`, Kähler differentials, dual numbers/square-zero derivation API, and Jacobian pieces. I do **not** see a ready affine-variety theorem saying “the tangent space of the orbit/image equals the image of the differential of the orbit map.” You would need to assemble a local tangent/cotangent bridge, tangent-map functoriality, the coordinate identification for `Rep`, and the proof that the orbit-map differential is exactly `δ⁰` and has image the tangent space.

Single hardest Route B step: **(iv) L2 differential-image=tangent**.

**3. RECOMMENDATION**
Use **Route B for L3**, and a **hybrid local first-order computation for L2**.

Route B has fewer absent bricks for smoothness: generic smoothness + closed smooth point + ring-side action automorphisms + transitivity is much less Lean than a uniform explicit chart. Route A’s chart is a genuine general-purpose cell/ideal-membership sub-library.

For L2, do not try to get it “for free” from homogeneity unless you are willing to build a tangent-of-homogeneous-space API. Build only the narrow affine tangent/cotangent computation needed for this orbit map.

**4. Biggest Uncertainty**
What I would check first: the exact coordinate-ring model of `O_M`.

If `A` is really the affine coordinate ring of the orbit/open piece, Route B L3 is clean. If `A` is the closure coordinate ring, you must also prove the chosen smooth closed point lies in the open orbit before transitivity applies; that modeling lemma could become the main L3 nuisance.