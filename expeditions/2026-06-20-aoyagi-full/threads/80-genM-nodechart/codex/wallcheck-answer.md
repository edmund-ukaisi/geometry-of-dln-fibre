**1. Verdict**

Yes. **[Inference]** The “single multi-axis `NodeAchieverChart M` for all `M`” is the wrong target for closing this theorem: it chases a stronger uniform chart abstraction than the divergence statement needs. **[Inference]** A 4-way single-pivot assembly is the right proof shape if the case split is exhaustive and each branch supplies either `NodeAchieverChart` or the radial-MP route.

**2. Precise Wall**

1. **Interior cov/det: bounded but heaviest engineering.**  
   **[Inference]** Since the rate and witness are already sorry-free and the remaining task is chart equality/determinant/COV bookkeeping, this sounds like a large Lean build, not a mathematical wall.

2. **Smeared rational `cov`: possible real interface gap, not clearly research.**  
   **[Inference]** The rational pole is mathematically harmless if the pole locus is null and the transport theorem accepts a.e. differentiability / local diffeomorphism off a null set.  
   **[Repo-contingent guess]** The risk is Lean-interface mismatch: `weightedThreshold_transport` may require a globally defined smooth/C¹ map, global determinant identity, or no exceptional set. If so, the theorem is conceptually adequate but its API is too rigid.

3. **4-way exhaustiveness: likely bounded, but this is the place to be suspicious.**  
   **Inference from your description only:** If the four branches are exactly `L=1`, boundary-clean `deepRank=deepRows`, interior `∃ p, r_p≥1 ∧ c_p≥1`, and residual smeared, then exhaustiveness should be a decidable finite case split over ranks/defects.  
   **Repo-contingent guess:** I cannot verify there is no fifth “boundary-dirty but not smeared” class; that is the main combinatorial coverage risk.

So: no clear research wall from the description. The closest design wall is the smeared `cov` API if it cannot express “valid off a null rational pole locus.”

**3. The Trap**

**[Repo-contingent guess]** The most likely way your verdict is wrong is over-optimism about exhaustiveness: the residual definition of “smeared” may accidentally exclude a boundary-degenerate family with no interior achiever, not clean, and not covered by the current rational templates.

**4. Cheapest Discriminating Next Step**

For smeared `cov`: instantiate `weightedThreshold_transport` on the smallest completed smeared case, e.g. `(1,2,1)`, with the actual rational `phi`; do not prove the theorem, just check the hypotheses elaborate.

For exhaustiveness: write a pure finite/Prop classifier lemma:

```lean
theorem achiever_cases_exhaustive (M) :
  L = 1 ∨ BoundaryClean M ∨ Interior M ∨ Smeared M := ...
```

Then test it first by brute-force enumeration for small widths/ranks, and only afterward formalize the rank inequalities.