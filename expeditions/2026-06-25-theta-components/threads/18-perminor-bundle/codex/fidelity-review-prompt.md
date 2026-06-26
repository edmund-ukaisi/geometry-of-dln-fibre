<task>
You are an independent fidelity reviewer of two Lean 4 + Mathlib modules. Judge whether the Lean
STATEMENTS faithfully match the informal mathematical claims, and whether anything OVERCLAIMS.
You do not have the repo; judge from the verbatim statements below. Mathlib v4.29 pin.

INFORMAL CLAIM (task B3, deliberately SCOPED): build the per-minor open cover of the
rank-exactly-r locus Mat^{=r}, plus a per-minor chart family realizing each chart as the
top-left chart of a coordinate-permuted matrix. The transition coherence (cocycle of localized
coordinate-ring AlgEquivs on overlaps, "B3-3") is DELIBERATELY NOT built and must be honestly
disclaimed; the package must NOT be named "locallyTrivial" / "bundle".

=== Module A: RankMinorCover.lean (k a field, p q : ℕ) ===

theorem exists_injective_cols_linearIndependent (A : Matrix (Fin p) (Fin q) k) :
    ∃ t : Fin A.rank → Fin q, Function.Injective t ∧ LinearIndependent k (A.col ∘ t)
-- proof: rw A.rank_eq_finrank_span_cols; Submodule.exists_fun_fin_finrank_span_eq on range A.col;
--        choose column indices t; A.col ∘ t = f (lin indep), so t injective by .of_comp.

theorem exists_invertible_square_minor_of_cols_linearIndependent {r : ℕ}
    (C : Matrix (Fin p) (Fin r) k) (hC : LinearIndependent k C.col) :
    ∃ s : Fin r → Fin p, Function.Injective s ∧ IsUnit ((C.submatrix s id).det)
-- proof: Cᵀ rank = r (rows of C = C.col indep, .rank_matrix); extract r indep cols of Cᵀ by
--        index s₀; recast Fin Cᵀ.rank to Fin r via finCongr; rows of the minor are lin. indep,
--        so Matrix.linearIndependent_rows_iff_isUnit gives IsUnit det.

theorem exists_invertible_minor_of_rank {r : ℕ} (A : Matrix (Fin p) (Fin q) k) (hr : A.rank = r) :
    ∃ (s : Fin r → Fin p) (t : Fin r → Fin q), Function.Injective s ∧ Function.Injective t
      ∧ IsUnit ((A.submatrix s t).det)

def minorChart {r : ℕ} (s : Fin r → Fin p) (t : Fin r → Fin q) :
    Set (Matrix (Fin p) (Fin q) k) := {M | IsUnit ((M.submatrix s t).det)}

def rankEqLocus (r : ℕ) : Set (Matrix (Fin p) (Fin q) k) := {M | M.rank = r}

theorem rankEqLocus_subset_iUnion_minorChart (r : ℕ) :
    rankEqLocus r ⊆ ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)), minorChart k p q st.1 st.2

theorem rankEqLocus_eq_iUnion_inter_minorChart (r : ℕ) :
    rankEqLocus r = ⋃ (st : (Fin r → Fin p) × (Fin r → Fin q)),
          (rankEqLocus r ∩ minorChart k p q st.1 st.2)

-- non-vacuity: example showing !![1,0;0,0] over ℚ ∈ minorChart at the (0,0) 1×1 pivot.

=== Module B: FibreBundlePerMinor.lean ===

noncomputable def perMinorEquiv (s : Fin r → Fin p) (hs : Function.Injective s) :
    Fin r ⊕ ↥(Set.range s)ᶜ ≃ Fin p :=
  (Equiv.sumCongr (Equiv.ofInjective s hs) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range s))

theorem submatrix_eq_toBlocks₁₁_reindex (M : Matrix (Fin p) (Fin q) k)
    (s : Fin r → Fin p) (hs : Function.Injective s) (t : Fin r → Fin q) (ht : Function.Injective t) :
    M.submatrix s t = (reindex (perMinorEquiv s hs).symm (perMinorEquiv t ht).symm M).toBlocks₁₁

-- pivotRankChart k m l n := {M : Matrix (m ⊕ l) (m ⊕ n) k | M.rank = Fintype.card m ∧ IsUnit M.toBlocks₁₁.det}
-- (from a separate module, the SINGLE top-left pivot chart, with explicit GL_r × Mat × Mat equiv
--  pivotRankChartEquiv).

theorem mem_minorChart_inter_rankEqLocus_iff (M : Matrix (Fin p) (Fin q) k)
    (s : Fin r → Fin p) (hs : Function.Injective s) (t : Fin r → Fin q) (ht : Function.Injective t) :
    (M ∈ rankEqLocus r ∧ M ∈ minorChart k p q s t)
      ↔ reindex (perMinorEquiv s hs).symm (perMinorEquiv t ht).symm M
          ∈ pivotRankChart k (Fin r) (↥(Set.range s)ᶜ) (↥(Set.range t)ᶜ)

noncomputable def minorChartEquiv (s : Fin r → Fin p) (hs : Function.Injective s)
    (t : Fin r → Fin q) (ht : Function.Injective t) :
    {M : Matrix (Fin p) (Fin q) k // M ∈ rankEqLocus r ∧ M ∈ minorChart k p q s t}
      ≃ {Δ : Matrix (Fin r) (Fin r) k // IsUnit Δ.det}
          × Matrix (Fin r) (↥(Set.range t)ᶜ) k × Matrix (↥(Set.range s)ᶜ) (Fin r) k
-- (TopLeftReduction section restricts to k : Type, i.e. universe 0, for the pivotRankChart reuse.)

All ten headlines build sorry-free; #print axioms = [propext, Classical.choice, Quot.sound] on all.
</task>

<output_contract>
Answer these, each in 2-4 sentences, flagging INFERENCE vs verifiable-from-the-statement FACT:

1. Does `exists_invertible_minor_of_rank` faithfully state "rank-r matrix over a field has an
   invertible r×r minor with INJECTIVE selectors"? Any way the injectivity could be vacuous or the
   selectors degenerate? Is [Field k] genuinely the only assumption it needs, or is there a hidden
   r ≤ min(p,q) gap that makes it vacuous (e.g. if r > p or r > q)?
2. Is the cover (rankEqLocus_subset_iUnion / _eq_iUnion_inter) a GENUINE cover, or could it be
   vacuously true / collapse to a single chart? Does ranging over ALL (s,t) (not just injective
   ones) weaken or invalidate the "cover by det-opens" reading?
3. Does mem_minorChart_inter_rankEqLocus_iff + minorChartEquiv genuinely realize each per-minor
   chart as the top-left pivotRankChart of a permuted matrix, inheriting the GL_r×Mat×Mat bijection?
   Is the universe-0 restriction honest/harmless or does it silently weaken the claim?
4. OVERCLAIM CHECK: given the names (minorChart, rankEqLocus, minorChartEquiv,
   rankEqLocus_subset_iUnion_minorChart), does any name promise more than the statement delivers —
   in particular is anything implying a full "locally trivial bundle" / transition coherence that
   is NOT actually proved? Is "not named locallyTrivial" the right call?
5. Is the B3-3 disclaimer accurate — i.e. do these statements secretly NEED or ASSUME the
   transition-coherence/cocycle data anywhere, or is it cleanly absent?

Then: a one-line verdict PASS / PASS-WITH-CONCERNS / FAIL with the single most important concern.
</output_contract>

<grounding_rules>
Judge ONLY from the statements given. If a concern depends on the proof body or on a Mathlib lemma's
exact behavior you cannot see, say so explicitly and mark it INFERENCE. Do not invent Lean API.
A "vacuous theorem" (true but contentless) is a fidelity FAIL even if it compiles — call it out.
</grounding_rules>
