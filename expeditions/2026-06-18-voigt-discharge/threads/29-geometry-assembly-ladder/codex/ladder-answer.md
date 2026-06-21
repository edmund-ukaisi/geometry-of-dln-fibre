## A. L2b Factoring
- **VERDICT:** a third framing: **dimension-bridge split**. Prove `finrank range δ⁰ = varietyDim Z_M` as the main orbit-dimension bridge; if desired, derive `finrank kerJac = finrank range δ⁰` later as a corollary by comparing both to `varietyDim Z_M`.

- **WHY:** A standalone `kerJac = range δ⁰` couples a generator-dependent Jacobian kernel to the coordinate-free orbit tangent, forcing either explicit determinantal tangent algebra or tangent-functor/open-immersion machinery. The final codimension theorem only needs dimensions, so direct subspace equality is extra surface area. Also: once `finrank range δ⁰ = varietyDim Z_M` is proved, L0 already finishes the codimension theorem; L3/L2a become logically optional for the final result, though useful for the Jacobian ladder.

- **dim `O_M = varietyDim Z_M`:** separate lemma. The rewrite `varietyDim orbitSet = varietyDim Z_M` can fall out from L6 ideal equality, but `finrank range δ⁰ = dim O_M` is not free; it is the real orbit-dimension bridge.

- **`range δ⁰ ⊆ ker Jac`:** red herring for the dimension-only route. It is needed only if you want actual tangent-space inclusion/equality, not for the codimension proof by comparing dimensions.

- **Per-option:**
  - **Option 1 direct iso:** consumes L2a, explicit generators, `dμ_e = δ⁰`, orbit-in-Z tangent functoriality, open orbit/local-ring comparison, and likely L3. Residual obligation: hard tangent-space equality.
  - **Option 1 dimension count:** consumes L0/L4d/M3/L3/L2a plus the orbit-dimension bridge; this is Option 2 hidden inside L2b.
  - **Option 2 / split:** L0 plus L1+L6 gives `codim = card - varietyDim Z_M`; the residual obligation is exactly `finrank range δ⁰ = varietyDim Z_M`.

## B. L3 Sizing
- **REUSE precedent:** no, not directly. `smooth_of_grpObj_of_isAlgClosed` is group-scheme-specific and uses `GrpObj.mulRight` (KNOWN); for an external action you must rederive the action automorphisms. Reusable pieces are `dense_smoothLocus_of_perfectField`, `nonempty_inter_closedPoints`, `pointEquivClosedPoint`, `Scheme.Hom.preimage_smoothLocus_eq`, and `FormallySmooth.of_equiv` (KNOWN).

- **The Spec detour for (i):** necessary at v4.29, unless you first prove a ring-side wrapper. I found scheme-side generic smoothness and ring-side `Algebra.smoothLocus`, but not a ring-side dense/generic smoothness theorem.

- **Most-likely-to-break sub-step:** proving the smooth closed witness lies in the open orbit. L6 gives density/closure, not openness; irreducible plus dense subset is insufficient unless the orbit is locally closed, hence open in its closure.

- **Is (iv) sound?** yes if you have: `O_M` is a nonempty open subset of `Z_M`, smooth locus is dense open, `Z_M` is irreducible, and `Spec A` is Jacobson so the nonempty open intersection contains a closed point. Then alg-closed `k` identifies that closed point with a `k`-point, and transitivity applies.

- **Module-count estimate:** about 5-7 focused modules. Hardest sub-lemma: `exists_closed_smooth_point_mem_openOrbit`, packaging generic smoothness, Jacobson closed-point extraction, open orbit, and the k-point dictionary.

## C. Cross-Cutting
- **Ordering:** L6 must precede L0/L4d/L3 for `Z_M` as the orbit closure/domain/reduced scheme. L3 is needed before M3, but not needed if the final proof uses only L0 plus the orbit-dimension bridge.

- **Hidden hypotheses:** `κ(m_M)=k`, `m_M` maximal, `M ∈ Z_M`, finite presentation over `k`, reducedness/domain of `A`, chosen generators really generate `vanishingIdeal Z_M`, and L6 before using L1 for `Z_M`.

- **Most suspicious point:** treating `finrank range δ⁰ = dim O_M = varietyDim Z_M` as cheap. That is not supplied by the landed bricks and likely hides the hardest image/orbit-dimension formalization.