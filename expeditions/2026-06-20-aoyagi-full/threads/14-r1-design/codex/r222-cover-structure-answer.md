1. **Composition Shape**

Rank: **(a) > (b) > (c)**. Use (a): set `g_i x := w_i x * g (φ_i x)` and recurse on the same ambient `E`. The decisive reason is that `g5_step` accepts an arbitrary `E → ℝ≥0∞`, so the previous Jacobian weight is not an extra hypothesis or obstruction. Extract a tree/n-level lemma only after this works; avoid the flat 24-chart route unless you want to prove global cover/disjointness all at once.

2. **Homeomorph Node**

Rank: **(ii) > (i)**. Handle Lemma-2 by a direct measure-preserving / c-o-v rewrite and fold the homeomorphism into the adjacent composite chart. The decisive reason is that it is not a branching cover, and `|det| = 1`, so making it a singleton `g5_step` only adds dummy sums and cover obligations. In the final Jacobian bookkeeping, record its determinant factor once as `1`.

3. **Cover Obligation**

Lowest pain: prove a **target-side image characterization** for each pivot chart:
`φ_i '' (V_i \ Z_i) = {y | coord i y ≠ 0 ∧ ∀ j ∈ block, |coord j y| ≤ |coord i y|}`.
Then prove cover/disjointness using these target cells, not existential image membership.

For `hcover`: outside the all-zero block, use a finite max argument to choose a coordinate of maximal absolute value; the all-zero block is null.

For `hdisj`: if `i ≠ j`, the overlap of weak-max cells lies in `{y | |coord i y| = |coord j y|}`, hence in `{coord i = coord j} ∪ {coord i = -coord j}`, a finite union of affine hyperplanes, hence null.

Confident Mathlib anchors in v4.29: `Finset.exists_max_image`, `Finite.exists_max`, `AEDisjoint`, `AEDisjoint.of_null_left`, `AEDisjoint.of_null_right`, `AEDisjoint.mono`, `AEDisjoint.congr`, `lintegral_biUnion_finset₀`, `ae_eq_set`, `setLIntegral_congr`, `addHaar_submodule`, `addHaar_affineSubspace`, `pi_hyperplane`, `abs_eq_abs`. I do **not** know a bundled Mathlib lemma saying “finite argmax weak cells form an a.e.-disjoint cover”; local grep found none.

4. **Scope Check**

**Yes**, the cleaner deliverable is the **nested per-step weighted identity**, not necessarily the flattened 24-term theorem. Reason: finiteness of a finite nested sum reduces to the same leaf integrals, while flattening to a 24-leaf `Finset` is mostly reindexing plus global presentation work. Just do not leave it as three unrelated bare one-step identities; the weights must be carried through recursively.