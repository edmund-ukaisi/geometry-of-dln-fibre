<task>
Lean 4 + Mathlib v4.29 formalisation. I am building "B3": a genuine per-minor-position
open-cover for the rank-exactly-r locus of matrices, generalising a single top-left-pivot
chart that is already built.

CONTEXT (what is already LANDED, zero-sorry, in `DLNFibre.Core`):

1. `DeterminantalChart.lean`:
   - `rank_fromBlocks_eq_card_iff_schur_inv (Δ : Matrix m m k) (B12 : Matrix m n k)
       (B21 : Matrix l m k) (B22 : Matrix l n k) (hΔ : IsUnit Δ.det) :
       (fromBlocks Δ B12 B21 B22).rank = Fintype.card m ↔ B22 = B21 * Δ⁻¹ * B12`
   - `pivotRankChart k m l n : Set (Matrix (m ⊕ l) (m ⊕ n) k) :=
       {M | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det}`  -- the TOP-LEFT pivot chart
   - `pivotRankChartEquiv : {M // M ∈ pivotRankChart k m l n} ≃
       {Δ : Matrix m m k // IsUnit Δ.det} × Matrix m n k × Matrix l m k`  -- explicit bijection
   So: on the chart where the top-left rxr block is invertible, rank = r iff the Schur
   complement vanishes, and the chart ≃ GL_r × Mat × Mat (the (2,2)-block is Schur-forced).

2. `FibreNormalForm.lean` — base-change homogeneity of the FIBRE (over an infinite field):
   `exists_baseChange_of_rank_eq (d) (hN : 0 ≠ Fin.last N) (B B') (h : B.rank = B'.rank) :
       ∃ P : BaseChangeGroup d, B' = P_last * B * (P_0)⁻¹`
   and `image_smul_fibre`, giving: every rank-r fibre is a GL×GL base-change image of the
   normal-form fibre. Plus the single top-left chart trivialization
   `reducedFibre_chartDsig_tensorEquiv_reducedVariety : Away chartDsig ≃ₐ[k]
       SchurLoc ⊗_k sweepFibreRing` (the reduced fibre coordinate ring).

GOAL B3, three rungs:
- B3-1 per-minor chart family: for each pivot position (S ⊆ Fin p, T ⊆ Fin q, |S|=|T|=r),
  the analogue of `pivotRankChart` localized at the (S,T) minor (det of the S×T submatrix).
- B3-2 the open cover of Mat^{=r}: rank = r ⟹ SOME r×r minor is nonzero (invertible), so the
  {det of (S,T)-submatrix ≠ 0} opens cover the rank-exactly-r locus.
- B3-3 transitions + a LocallyTrivial-style packaged statement.

KEY UNKNOWN I verified: Mathlib v4.29 has NO lemma "rank ≥ r ⟹ ∃ r×r submatrix with nonzero
det / invertible". `Matrix.rank_submatrix`, `rank_submatrix_le`, `rank_of_isUnit` exist; no
determinantal-rank existence direction. So B3-2 requires building the bridge
"rank A = r ⟹ ∃ (s : Fin r → m) (t : Fin r → n) injective, IsUnit (A.submatrix s t).det".

QUESTIONS (rank by cost; give the cheapest correct route for each):

Q1. The rank↔minor bridge for B3-2. Over a field k, A : Matrix (Fin p) (Fin q) k of rank r.
    I want `∃ (s : Fin r → Fin p) (t : Fin r → Fin q), Function.Injective s ∧ Function.Injective t
    ∧ IsUnit (A.submatrix s t).det`. What is the cleanest Mathlib v4.29 route?
    Candidate ideas: (a) rank = finrank of column span; pick r linearly independent COLUMNS
    (Submodule / Basis.ofVectorSpace?), giving an injective t with submatrix-of-those-columns
    of rank r (full column rank, p×r); then within that pick r independent ROWS giving the
    invertible r×r minor; relate `linearIndependent rows ⟺ IsUnit det` of a square matrix
    (`Matrix.linearIndependent_rows_iff_isUnit`? / `Matrix.nondegenerate`? / via
    `Matrix.rank_eq_card... `). Is there a Mathlib lemma `rank A = r ⟹ ∃ injective col-selector
    with the submatrix columns linearly independent`? (`Matrix.exists_... `?) And the square-case
    `r×r matrix invertible ⟺ rows lin indep ⟺ rank = r` — exact lemma names.
    Estimate the LoC and flag the single hardest step.

Q2. The per-minor chart B3-1. The top-left `pivotRankChart` uses a literal `m ⊕ l` / `m ⊕ n`
    sum decomposition. For a general (S,T) pivot, is the cleanest route to (i) reindex the
    matrix by an equiv `(Fin r ⊕ Fin (p-r)) ≃ Fin p` that puts S first (and T first on columns),
    reducing the (S,T)-minor case to the top-left `pivotRankChart` literally by
    `Matrix.submatrix`/`reindex`; OR (ii) restate the Schur criterion directly for an arbitrary
    injective pair (s,t) with its complement, avoiding the sum type? Which keeps the
    `pivotRankChartEquiv` bijection reusable with least friction? Note p,q,r are bare ℕ here and
    S,T would be `Finset (Fin p)` / `Finset (Fin q)` of card r, OR a chosen `Fin r ↪ Fin p`.
    Recommend the indexing type for the pivot position that makes both the cover (B3-2) and the
    chart (B3-1) cleanest.

Q3. Scope call. Given B3-2's rank↔minor bridge is genuinely new infra, and B3-3's transition
    coherence (e_{S,T} ∘ e_{S',T'}⁻¹ on overlaps) requires comparing two DIFFERENT chart
    AlgEquivs that are each ~250 LoC of localization machinery: is the honest high-value
    deliverable for ONE tide = (B3-2 cover, fully proved + matrix-level B3-1 per-minor pivot
    chart family with its GL_r×Mat×Mat bijection), explicitly DISCLAIMING B3-3 transition
    coherence? Or is there a cheap way to get a genuine LocallyTrivial statement (e.g. transitions
    are AUTOMATIC because all charts factor through the same base-change-homogeneous model, so the
    transition is just a base change — no need to compare localization AlgEquivs)? Assess whether
    base-change homogeneity (already landed) gives the transitions "for free".
</task>

<output_contract>
Three sections Q1, Q2, Q3. For Q1 and Q2: the recommended route as a numbered lemma chain with
exact Mathlib v4.29 lemma names (flag any you are <80% sure exists), a LoC estimate, and the
single hardest step. For Q3: a decisive recommendation (one of: "ship B3-2+B3-1, disclaim B3-3"
OR "B3-3 is cheap via base-change, here's how") with the reasoning. Be concrete; ≤ 900 words.
</output_contract>

<grounding_rules>
Flag any lemma name you are not confident exists in Mathlib v4.29 as "(UNVERIFIED — check)".
Distinguish "this definitely exists" from "something like this should exist". Do not invent
lemma signatures; if unsure of the exact form, describe the content and say it must be located.
</grounding_rules>
