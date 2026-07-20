<task>
Lean 4 + Mathlib v4.29. I am formalising a scheme-level "rank bridge" for a determinantal locus and want a design red-team BEFORE I write ~250 lines. Please vet the plan for correctness and for the cleanest Mathlib route, and flag any gotcha at the v4.29 pin.

CONTEXT (banked objects, all proved/defined in the repo):
- `d : Fin (N+2) → ℕ`, `r : ℕ`. `RepCoord d` is a Fintype index of coordinate variables.
- `multPoly d : Fin (d last) → Fin (d 0) → MvPolynomial (RepCoord d) k` : the "universal product matrix" entries (entries of the generic matrix product), over a field `k`.
- The universal matrix is `U := Matrix.of (multPoly d) : Matrix (Fin (d last)) (Fin (d 0)) (MvPolynomial (RepCoord d) k)`.
- `sweepSigma k d r : Set (RepCoord d → k)` is the image (under coordinate iso) of the rank-EXACTLY-r product locus `{A | (mult d A).rank = r}`.
- `sweepSigmaRing k d r := MvPolynomial (RepCoord d) k ⧸ MvPolynomial.vanishingIdeal k (sweepSigma k d r)`. Call this `R`. `mk : MvPolynomial _ k →+* R` is `Ideal.Quotient.mk _`.
- `ΔPdeepAt d r s t := ((U).submatrix s t).det : MvPolynomial _ k`, for selectors `s : Fin r → Fin (d last)`, `t : Fin r → Fin (d 0)`.
- `chartDsigAt d r s t := mk (ΔPdeepAt d r s t) : R`.
- `rankROpen d r : Set (PrimeSpectrum R)` is DEFINED as `(PrimeSpectrum.zeroLocus (Set.range (fun st ↦ chartDsigAt d r st.1 st.2)))ᶜ` — complement of common-vanishing locus of all the pivot minors.
- BANKED matrix lemmas (over a field): `rank_le_iff_forall_submatrix_det_eq_zero : A.rank ≤ r ↔ ∀ er ec, ((A.submatrix er ec).det) = 0` (er,ec : Fin (r+1) → ...). `rank_submatrix_le_rank`, `Matrix.rank_of_isUnit`, `Matrix.isUnit_iff_isUnit_det`.
- BANKED: `det_submatrix_multPoly_mem_sigmaIdeal` says every (r+1)-minor of U lies in the vanishing ideal of the rank-≤-r locus `productRankLocusLE`. But I want it for `sweepSigma` (rank EXACTLY r), so I will RE-PROVE it directly on `sweepSigma` via `eval_det_submatrix_multPoly` (eval of a minor of U at coords of A = that minor of `mult d A`) + `submatrix_det_eq_zero_of_rank_le` (rank=r ≤ r ⟹ (r+1)-minor = 0). `mem_vanishingIdeal_iff : p ∈ vanishingIdeal k V ↔ ∀ x ∈ V, aeval x p = 0`.

Mathlib v4.29 residue-field API I plan to use:
- For a prime `I : Ideal Rr` `[I.IsPrime]`, `I.ResidueField := IsLocalRing.ResidueField (Localization.AtPrime I)`, with `algebraMap Rr I.ResidueField : Rr →+* κ`.
- `Ideal.algebraMap_residueField_eq_zero : algebraMap Rr I.ResidueField x = 0 ↔ x ∈ I`.
- `Ideal.ResidueField` is a Field (so `Nontrivial`, and "nonzero ⟹ IsUnit" in a field).
- `PrimeSpectrum.mem_basicOpen f x ↔ f ∉ x.asIdeal`; `mem_zeroLocus x s ↔ s ⊆ x.asIdeal`.

THE PLAN (the theorem I want):
For `P : PrimeSpectrum R`, set `κ := P.asIdeal.ResidueField`, `φ := (algebraMap R κ).comp mk : MvPolynomial _ k →+* κ`, and `Mκ := U.map φ : Matrix _ _ κ`. Claim:
  `P ∈ rankROpen d r  ↔  Mκ.rank = r`.

Proof sketch:
- minor det over κ: `(Mκ.submatrix s t).det = φ (ΔPdeepAt s t) = algebraMap R κ (chartDsigAt s t)` (RingHom.map_det + map/submatrix commute).
- (⟹, rank ≥ r): `P ∈ rankROpen` ⟺ `∃ (s,t), chartDsigAt s t ∉ P.asIdeal` (unfold zeroLocus complement + Set.range_subset_iff + not_forall) ⟹ `algebraMap R κ (chartDsigAt s t) ≠ 0` (algebraMap_residueField_eq_zero) ⟹ that r×r minor of Mκ is a nonzero det ⟹ IsUnit (field) ⟹ Mκ.submatrix has rank r ⟹ Mκ.rank ≥ r (rank_submatrix_le_rank).
- (rank ≤ r always on `Spec R`): every (r+1)-minor of U is in `vanishingIdeal (sweepSigma)`, i.e. `mk` kills it, so `φ` kills it, so `(Mκ.submatrix er ec).det = 0` for all (r+1)-selectors ⟹ `Mκ.rank ≤ r` (rank_le_iff_forall_submatrix_det_eq_zero).
- Combine: rank = r iff (rank ≤ r always) ∧ rank ≥ r, and rank ≥ r ⟺ some pivot minor nonzero ⟺ P ∈ rankROpen. So the iff is `P ∈ rankROpen ↔ Mκ.rank = r`.

QUESTIONS:
1. Is the iff `P ∈ rankROpen ↔ Mκ.rank = r` correct as stated, given rank ≤ r holds for EVERY prime P of R? In particular: is rankROpen exactly the set of P with rank ≥ r (equivalently = r)? Any edge case at r=0 (then there are no (r... ) selectors issues; Fin 0 → ...; the "≥ r" direction is vacuous and rankROpen would be... the complement of zeroLocus of range over Fin 0 → ... selectors; chartDsigAt with r=0 is det of 0×0 submatrix = 1, the unit, so basicOpen(1) = ⊤, rankROpen = univ, and Mκ.rank ≥ 0 = r always — consistent. Confirm r=0 is fine, not a special case to carve out.)
2. The cleanest way in Lean v4.29 to get `(Mκ.submatrix s t).det = algebraMap R κ (chartDsigAt s t)`. Is `RingHom.map_det φ (U.submatrix s t)` plus `Matrix.submatrix_map`/`(U.map φ).submatrix = (U.submatrix).map φ` the right chain? Exact lemma names for "map and submatrix commute" and "det commutes with map" at this pin.
3. `Matrix.rank_of_isUnit` needs `[Nontrivial R]` on the ring and `[DecidableEq n]` on the index — κ is a field so Nontrivial is fine; the submatrix index is `Fin r`, DecidableEq fine. Any `Fintype`/`StrongRankCondition` instance that won't be found automatically for `Matrix _ _ κ` where κ is `IsLocalRing.ResidueField (Localization.AtPrime ...)`? Will typeclass inference find `Field κ`, `Fintype (Fin _)`, etc., or do I need explicit `haveI`?
4. Universe issue: `R : Type u`, `MvPolynomial (RepCoord d) k : Type u`, κ is built from `Localization.AtPrime` of `R` so also `Type u`. `Matrix.rank` works over a commutative ring with the right instances. Any universe pitfall combining `PrimeSpectrum R` (lives where?) with the matrix rank machinery?
5. Is there a SHORTER packaging — e.g. should I instead phrase the headline as `P ∈ rankROpen ↔ r ≤ Mκ.rank` (since ≤ r is automatic) and add `Mκ.rank = r` as a corollary, or vice versa? Which is the more honest/useful "rank bridge" name? I will also state `Mκ.rank ≤ r` as its own lemma (true for all P).
6. Any reason the composite `φ = (algebraMap R κ).comp mk` is not literally `algebraMap (MvPolynomial _ k) κ`? `mk` is the quotient algebra map and `algebraMap R κ` exists; is there an `IsScalarTower`/`algebraMap_eq` that makes `φ` definitionally the MvPolynomial→κ algebra map, simplifying `map_det`?
</task>

<output_contract>
Answer the 6 numbered questions, each ≤ 8 lines. Lead with a one-line GO / GO-WITH-CHANGES / RECONSIDER verdict on the overall plan. Then, if any step is wrong or has a cleaner route, give the corrected lemma chain (names only, no full proofs). Flag explicitly which claims are v4.29-confirmed vs your inference.
</output_contract>

<grounding_rules>
You do NOT have the repo. Treat banked lemma names as given (assume they typecheck as described). For Mathlib lemma names, mark each as "confident" or "guess — verify with grep" since the pin is v4.29 and names drift. Do not invent lemmas; if unsure a lemma exists, say so and name the most likely candidate.
</grounding_rules>
