# Statement card — L6.3 the rank locus is Zariski-closed (thread 25)

Module: `lean/DLNFibre/Core/RankLocusClosed.lean` @ `935f114`. Network-free `Core` engine,
`[Field k]` only (no `IsAlgClosed`). Axioms `[propext, Classical.choice, Quot.sound]`;
`scripts/sorries` = 0; whole library green.

## Headline 1 — the rank locus is Zariski-closed

> **Claim.** The determinantal locus `orbitRankLocus M = {A | ∀ i ≤ j, rankPattern A i j ≤
> rankPattern M i j}`, flattened to a point set, is Zariski-closed.
>
> - **Lean:** `DLNFibre.Core.isZariskiClosed_orbitRankLocus`
> - **Gloss.** For `M : Tuple d` over a field `k`,
>   `IsZariskiClosed (canonicalCoord d '' orbitRankLocus M)` — the image equals the zero locus of
>   its own vanishing ideal (`IsZariskiClosed Z := Z = zeroLocus (vanishingIdeal Z)`).
> - **Proved.** Unconditionally, any `d`, any `M`, `[Field k]`. The locus is the `zeroLocus` of the
>   minor ideal `span (rankMinorSet M)` (`image_orbitRankLocus_eq_zeroLocus`), and a `zeroLocus` is
>   Zariski-closed by the Nullstellensatz Galois connection `l_u_l_eq_l`. No algebraic closedness.
> - **Assumed.** none beyond `[Field k]`.
> - **Cited.** none. (The determinantal-rank bridge it rests on is built in-module, Headline 2 —
>   NOT a cited interface.)
> - **Deferred.** The identification `orbitRankLocus M = Ō_M` (Lehalleur–Rimányi Thm 3.8) — i.e.
>   that this closed set IS the orbit closure — is L6.1/L6.2, not here. This card claims only
>   closedness + the easy `O_M ⊆ orbitRankLocus M` inclusion.
> - **Scope (caveat next to claim).** Closedness is for the **`canonicalCoord` entry-flattening**
>   (one variable per matrix entry) and relative to `k`-points (`zeroLocus k …`). It is the
>   topological fact that lets the Zariski closure of `O_M` stay inside `orbitRankLocus M` once the
>   orbit is contained in it (Headline 3); it is NOT the reverse inclusion `orbitRankLocus M ⊆ Ō_M`.

## Headline 2 — the determinantal-rank bridge (engine brick, built here)

> **Claim.** Over a field, a matrix has rank `≤ r` iff every `(r+1)×(r+1)` submatrix has
> determinant `0`.
>
> - **Lean:** `DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero`
> - **Gloss.** For `A : Matrix (Fin p) (Fin q) k` and `r : ℕ`, `A.rank ≤ r ↔ ∀ (er : Fin (r+1) →
>   Fin p) (ec : Fin (r+1) → Fin q), (A.submatrix er ec).det = 0`.
> - **Proved.** Both directions. `→` (`submatrix_det_eq_zero_of_rank_le`): a square submatrix has
>   rank `≤ A.rank ≤ r < r+1`, so not full rank, so `det = 0` (`cRank_submatrix_le`,
>   `rank_of_isUnit`). `←` (`exists_submatrix_det_ne_zero_of_le_rank`): from `r+1 ≤ A.rank`, extract
>   `r+1` independent rows then `r+1` independent columns of that block; the square block has
>   independent columns, hence is a unit, hence `det ≠ 0` (`exists_linearIndependent'`,
>   `LinearIndependent.rank_matrix`, `linearIndependent_cols_iff_isUnit`,
>   `isUnit_iff_isUnit_det`).
> - **Mathlib gap.** Mathlib v4.29 has NO packaged `rank ≤ k ↔ minors vanish` (verified by grep +
>   leansearch). This is built from scratch; the index-subfamily extraction
>   `exists_injective_linearIndependent_rows` is the reusable sub-brick.
> - **Assumed / Cited / Deferred.** none beyond `[Field k]`.

## Headline 3 — the easy orbit inclusion `O_M ⊆ orbitRankLocus M`

> **Claim.** The `G_d`-orbit of `M` is contained in the rank locus.
>
> - **Lean:** `DLNFibre.Core.orbitSet_subset_orbitRankLocus` (+ `orbit_subset_orbitRankLocus`
>   pre-flattening); ideal shadow `DLNFibre.Core.vanishingIdeal_orbitRankLocus_le_orbitSet`.
> - **Gloss.** `orbitSet M ⊆ canonicalCoord d '' orbitRankLocus M`, since a base change preserves
>   the rank pattern (`rankPattern_eq_of_smul`), so every orbit point satisfies the rank bounds with
>   equality. The ideal version: `vanishingIdeal (canonicalCoord '' orbitRankLocus M) ≤
>   vanishingIdeal (orbitSet M)` — the trivial order-reversing containment.
> - **Proved.** Unconditionally, `[Field k]`. Consumes `rankPattern_eq_of_smul` (`Core.Orbit`).
> - **Caveat next to claim.** The ideal inclusion is the *easy* direction the brief named: it is the
>   order-reversal of a set inclusion, not the genuine content. The genuine content of L6.3 is
>   Headline 1 (closedness), which is what makes the orbit-closure argument go through.

## Witnesses (in-file, `Witness` section)

- The bridge fires concretely both ways: the `2×2` zero matrix has rank `≤ 0` (all `1×1` minors
  vanish); the `2×2` identity does NOT have rank `≤ 1` (its `2×2` minor `= 1 ≠ 0`).
- The rank locus is inhabited: `canonicalCoord d M ∈ canonicalCoord d '' orbitRankLocus M`.
- The orbit inclusion is non-vacuous on the `(2,2,2)/ℚ` orbit witness `tupleWitnessQ`.

## Status

sorry-free; reviewer fidelity check pending. Axioms `[propext, Classical.choice, Quot.sound]`.
