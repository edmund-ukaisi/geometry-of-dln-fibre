# Statement card — S1 rank-bridge keystone

> **Claim.** For a prime `P` of the chart-closure ring `sweepSigmaRing k d r` (the coordinate ring of
> `Σ̄^r`), membership in the rank-`= r` open `rankROpen d r` is equivalent to the universal product
> matrix `Matrix.of (multPoly d)`, evaluated entrywise over the residue field `κ(P) =
> P.asIdeal.ResidueField`, having rank exactly `r`. Since rank `≤ r` holds for *every* prime (rank
> `≤ r` is baked into `Σ̄^r`), this also reads as `rankROpen = {P | rank over κ(P) = r}` as a set of
> primes.
>
> - **Lean:** `DLNFibre.Core.mem_rankROpen_iff_rank_universalMatrixResidue_eq`
>   (`lean/DLNFibre/Core/FibreRankBridge.lean` @ `06b30931` — base; controller pins merge SHA)
> - **Gloss.** Over a field `k`, for `d : Fin (N+2) → ℕ`, `r : ℕ`, and a prime
>   `P : PrimeSpectrum (sweepSigmaRing k d r)`:
>   `P ∈ rankROpen d r ↔ (universalMatrixResidue d r P).rank = r`,
>   where `universalMatrixResidue d r P := (Matrix.of (multPoly d)).map (residueMap d r P)` and
>   `residueMap d r P := (algebraMap _ P.asIdeal.ResidueField).comp (Ideal.Quotient.mk …)` is the
>   composite `MvPolynomial (RepCoord d) k → sweepSigmaRing k d r → κ(P)`.
> - **Proved (unconditionally).**
>   - The headline `↔` above.
>   - `rank_universalMatrixResidue_le`: `(universalMatrixResidue d r P).rank ≤ r` for **every** prime
>     `P` (the rank-`≤ r` half, true on all of `Spec`).
>   - `r_le_rank_universalMatrixResidue_of_notMem`: a non-vanishing pivot minor `chartDsigAt s t ∉ P`
>     forces rank `≥ r` over `κ(P)` (the rank-`≥ r` half).
>   - `mem_rankROpen_iff_exists_notMem`: `P ∈ rankROpen d r ↔ ∃ (s,t), chartDsigAt s t ∉ P.asIdeal`
>     (the def-level unfolding via the banked cover identity).
>   - `det_submatrix_universalMatrixResidue` / `_eq_residueMap`: the minor-det bridge
>     (det over `κ(P)` of an `(s,t)`-minor = residue-field image of `chartDsigAt s t`).
>   - `det_submatrix_multPoly_mem_vanishingIdeal_sweepSigma`: the `(r+1)`-minors of the universal
>     matrix vanish in `sweepSigmaRing` (the "rank ≤ r baked into Σ̄^r" fact, on the rank-exactly-r
>     locus `sweepSigma`).
> - **Assumed.** `[Field k]`, with `k : Type` (= `Type 0`, matching `rankROpen`'s declaration
>   context; the headline's universe is `0`). `[Infinite k]` is in scope (forced by `rankROpen`'s
>   declaration context) but is `omit`-ed everywhere — no lemma uses it. The `r = 0` and `r ≥ 1` cases
>   are both handled inside the proof (no extra hypothesis: `r = 0` ⟹ empty pivot minor is the unit
>   `1 ∉ P`).
> - **Non-vacuity caveat.** The headline carries NO `r ≤ d (last (N+1))` / `r ≤ d 0` (nor
>   `kostantPartitions`-nonempty) hypothesis. When rank `r` is unachievable by the block shapes,
>   `productRankLocus d r = ∅` ⟹ `sweepSigma = ∅` ⟹ `vanishingIdeal ∅ = ⊤` ⟹ `sweepSigmaRing` is the
>   zero ring ⟹ `PrimeSpectrum (sweepSigmaRing)` is empty ⟹ the `∀ P` iff is **vacuously true**. The
>   iff is never false, so this is sound, but non-vacuity (existence of primes with rank `= r`) holds
>   only in the rank-achievable regime (`nonempty_image_productRankLocus`, gated on `kostantPartitions`
>   nonempty). Flagged at fidelity review (PASS-WITH-NOTES); not an overclaim of the headline, which is
>   only `∀ P, (…)`.
> - **Cited.** none new. Banked inputs reused: the over-field determinantal-rank criterion
>   `rank_le_iff_forall_submatrix_det_eq_zero` + `submatrix_det_eq_zero_of_rank_le` +
>   `rank_submatrix_le_rank` (`Core.RankLocusClosed`); `eval_det_submatrix_multPoly`
>   (`Core.DeterminantalChartRing`); `iSup_pivot_basicOpen_eq_rankROpen` + `rankROpen` + `chartDsigAt`
>   + `ΔPdeepAt` (`Core.FibreBundleLocallyTrivialFull` / `Core.FibreChartConjugation`). Residue-field
>   API from Mathlib v4.29 (`Ideal.ResidueField`, `Ideal.algebraMap_residueField_eq_zero`).
> - **Deferred.** The bridge is **prime-pointwise** (an iff for each `P`), which (with the automatic
>   rank-`≤ r`) gives `rankROpen = {P | rank over κ(P) = r}` as a **set of primes**. It is not packaged
>   as a scheme/locus-with-structure-sheaf identity beyond that set equality; no separate scheme-object
>   identity is claimed.
> - **Status.** sorry-free, axiom-clean (`#print axioms
>   mem_rankROpen_iff_rank_universalMatrixResidue_eq` = `[propext, Classical.choice, Quot.sound]`).
>   **Reviewed** — fidelity PASS-WITH-NOTES (vacuity caveat above is the one substantive note;
>   independent Codex `xhigh` concurred; no mathematical discrepancy, objects/directional-lemmas/
>   hypotheses/`r=0`-branch all faithful).

## Notes on naming (name = content)

- The headline name is `mem_rankROpen_iff_rank_universalMatrixResidue_eq` — it denotes exactly the
  proved `↔` (membership iff rank `= r`). The two directional halves are named lemmas so the
  one-directional content is not over-named: `rank_universalMatrixResidue_le` (≤, always) and
  `r_le_rank_universalMatrixResidue_of_notMem` (≥, from chart membership).
- "Universal matrix over κ(P)" = `Matrix.of (multPoly d)` pushed through `residueMap` into the
  residue field; the `(s,t)` minor det of that matrix is the residue class of the pivot chart element
  `chartDsigAt s t`, tying the rank to the `rankROpen` def cleanly.
