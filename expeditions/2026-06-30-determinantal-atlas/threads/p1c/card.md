# P1.c statement cards — rank strata + pivot cover + ideal↔rank-locus connective

Home: `lean/DLNFibre/Core/RingTheory/Determinantal/Strata.lean` (bare `Matrix` namespace, L7
Mathlib-mirror of `Mathlib.LinearAlgebra.Matrix.Rank`). Re-home of the rank strata + cover from the
deleted `Core/RankMinorCover.lean`, plus the new connective tying P1.b's determinantal ideal
(`Core/RingTheory/Determinantal/Basic.lean`) to the rank locus. Field/coordinate level — the
scheme-point / `κ(P)` lift is the separate P2.d residue-bridge rung.

---

## The cover theorem (re-homed, the headline of the re-home)

> **Claim.** Over a field, the per-minor pivot charts cover the rank-exactly-`r` locus: every
> matrix of rank exactly `r` has some invertible `r × r` minor, so `{M | M.rank = r}` is contained
> in the union of the det-opens `{M | (M.submatrix s t).det is a unit}` over all selector pairs.
>
> - **Lean:** `Matrix.rankEqLocus_subset_iUnion_minorChart`
>   (`lean/DLNFibre/Core/RingTheory/Determinantal/Strata.lean` @ `392b8fa4`)
> - **Gloss.** `rankEqLocus r ⊆ ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)), minorChart k p q st.1 st.2`
>   where `rankEqLocus r = {M | M.rank = r}` and `minorChart s t = {M | IsUnit ((M.submatrix s t).det)}`.
>   The keystone is `exists_invertible_minor_of_rank` (a rank-`r` matrix over a field has an
>   invertible `r × r` minor — absent in Mathlib v4.29).
> - **Proved.** The set-inclusion cover, unconditionally over any field. Companion
>   `rankEqLocus_eq_iUnion_inter_minorChart` (the cover as an equality with the rank condition carried).
> - **Assumed.** `k` a field (the keystone needs it).
> - **Cited.** none (the keystone is proved in-file from Mathlib column-extraction lemmas).
> - **Deferred.** Topology — `minorChart`/`rankEqLocus`/`rankLeLocus` are bare `Set`s; "open"/"closed"
>   is geometric motivation, no topological theorem proved here.
> - **Status.** sorry-free + reviewed (fidelity PASS).

## The ideal ↔ rank-locus connective (the new content)

> **Claim.** Over a field `k`, a `p × q` matrix `M` has `rank M ≤ r` **iff** the determinantal
> `(r+1)`-minor ideal `determinantalIdeal p q k (r+1)` is killed by evaluation at `M` — i.e. `M`
> lies in the field-level vanishing locus of that ideal. The three-way identity "rank `≤ r`" ⟺
> "all `(r+1)`-minors vanish at `M`" ⟺ "in the vanishing locus of `determinantalIdeal (r+1)`".
>
> - **Lean:** `Matrix.mem_rankLeLocus_iff_determinantalIdeal_le_ker` (membership form) /
>   `Matrix.rankLeLocus_eq_vanishingLocus` (set-equality form)
>   (`lean/DLNFibre/Core/RingTheory/Determinantal/Strata.lean` @ `392b8fa4`)
> - **Gloss.** `M ∈ rankLeLocus r ↔ determinantalIdeal p q k (r+1) ≤ RingHom.ker (MvPolynomial.eval
>   (fun ij ↦ M ij.1 ij.2))`, where `rankLeLocus r = {M | M.rank ≤ r}` and the evaluation ring hom
>   sends the coordinate `X (i, j)` to the entry `M i j`. The kernel is the ideal of polynomials
>   vanishing at the `k`-point `M`; `ideal ≤ ker` is "every generator (every `(r+1)`-minor) vanishes
>   at `M`".
> - **Proved.** The iff, unconditionally over any field, at the `k`-point level. Chains
>   `determinantalIdeal_le_iff` (P1.b) + `RingHom.mem_ker` + `eval_detMinorPoly` (P1.b) +
>   `rank_le_iff_forall_submatrix_det_eq_zero` (`Core/Matrix/RankMinors.lean`).
> - **Assumed.** `k` a field (the rank criterion needs it; the ideal/`detMinorPoly` are over any
>   `CommRing`, meeting the field side correctly).
> - **Cited.** none.
> - **Deferred.** The scheme-point lift — vanishing at *every* prime `P` of the coordinate ring
>   (rank over each residue field `κ(P)`), which is the P2.d residue-field-rank bridge. This card is
>   strictly the `k`-rational-point level.
> - **Route.** (controller/formaliser) chain the ideal's generator criterion with the field-level
>   minor↔rank criterion through the evaluation hom; `forall₂_congr` over the `(s,t)` selectors.
> - **Status.** sorry-free + reviewed (fidelity PASS; decorrelated Codex xhigh confirmed orientation,
>   off-by-one, and the `r+1 > min(p,q)` non-degeneracy).

---

## Re-home + consumer sweep (L2)

Re-homed verbatim (namespace `DLNFibre.Core` → bare `Matrix`, DLN-flavour docstrings dropped; the
witness's `show` → `change` per linter, def-eq): `exists_injective_cols_linearIndependent`,
`exists_invertible_square_minor_of_cols_linearIndependent`, `exists_invertible_minor_of_rank`,
`minorChart`, `rankEqLocus`, `rankEqLocus_subset_iUnion_minorChart`,
`rankEqLocus_eq_iUnion_inter_minorChart`, the non-vacuity witness. New: `rankLeLocus`,
`mem_rankLeLocus`, `mem_rankEqLocus`, `rankEqLocus_subset_rankLeLocus`, the two connective theorems.

Consumers swept: `FibreBundlePerMinor` (import retargeted to `Strata` + docstring attribution);
`FibreBundleLocallyTrivialFull` (imports `Strata` directly — uses `exists_invertible_minor_of_rank`,
previously via the transitive `FibreBundleTransition → RankMinorCover` path now severed);
`FibreBundleTransition` (drops its now-unused `RankMinorCover` import); aggregator `DLNFibre.lean`
retargeted. `Core/RankMinorCover.lean` deleted.

**Gates.** Full aggregator green (`scripts/lb DLNFibre`, 3829 jobs); `scripts/sorries` = 0;
`#print axioms` on `rankEqLocus_subset_iUnion_minorChart`, `mem_rankLeLocus_iff_determinantalIdeal_le_ker`,
`rankLeLocus_eq_vanishingLocus`, `exists_invertible_minor_of_rank` = `[propext, Classical.choice,
Quot.sound]`.
