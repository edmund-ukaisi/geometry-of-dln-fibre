<task>
You are red-teaming a Lean 4 + Mathlib (v4.29) proof for SOUNDNESS. Do NOT trust the
prose; reason about whether the stated lemma chain actually proves the claim, and whether
any index/cardinality step is subtly wrong. This is the "hard" direction of the
determinantal-rank criterion over a field.

CLAIM (the headline iff, over a field k):
  rank_le_iff_forall_submatrix_det_eq_zero {p q r : ℕ} (A : Matrix (Fin p) (Fin q) k) :
    A.rank ≤ r ↔ ∀ (er : Fin (r+1) → Fin p) (ec : Fin (r+1) → Fin q),
      (A.submatrix er ec).det = 0

The HARD direction (←) is proved contrapositively by exhibiting a nonzero (r+1)-minor when
r+1 ≤ A.rank. Here is the actual proof skeleton (Mathlib lemma names are real v4.29 names):

STEP 0 — support lemmas (proved separately, assume correct):
  rank_submatrix_le_rank : (A.submatrix f g).rank ≤ A.rank   -- via cRank_submatrix_le, toNat cast
  det_eq_zero_of_rank_lt (A : Matrix (Fin p)(Fin p) k) (h : A.rank < p) : A.det = 0
        -- by_contra; IsUnit A from isUnit_iff_isUnit_det; rank_of_isUnit gives A.rank = card(Fin p)=p; omega

STEP 1 — exists_injective_linearIndependent_rows (A) {s} (hs : s ≤ A.rank) :
    ∃ er : Fin s → Fin p, Injective er ∧ LinearIndependent k (fun i ↦ A.row (er i))
  Proof: obtain ⟨κ, a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' k A.row
    -- exists_linearIndependent' v : ∃ κ a, Injective a ∧ span(range (v∘a)) = span(range v) ∧ LinearIndependent (v∘a)
    Finite κ from ha_li.finite; Fintype κ from Fintype.ofFinite.
    hcard : Fintype.card κ = A.rank — via finrank_span_eq_card ha_li (= finrank (span (range (A.row∘a))) = card κ),
            rewrite ha_span, then A.rank_eq_finrank_span_row.
    hsle : s ≤ Fintype.card κ (rw hcard; exact hs).
    Embedding ι : Fin s ↪ κ from Function.Embedding.nonempty_of_card_le (card (Fin s) ≤ card κ via Fintype.card_fin).
    Return (fun i ↦ a (ι i)); injective = hιinj ∘ ha_inj; independence = ha_li.comp ι hιinj.

STEP 2 — exists_submatrix_det_ne_zero_of_le_rank (A) (hr : r+1 ≤ A.rank) :
    ∃ er ec, Injective er ∧ Injective ec ∧ (A.submatrix er ec).det ≠ 0
  (1) ⟨er, her_inj, her_li⟩ := exists_injective_linearIndependent_rows A hr     (s := r+1)
  (2) B := A.submatrix er id : Matrix (Fin (r+1)) (Fin q) k.
      B.row = fun i ↦ A.row (er i) (by funext; rfl), so LinearIndependent k B.row.
      hBrank : B.rank = r+1  — from LinearIndependent.rank_matrix (rows independent ⟹ rank = card m), Fintype.card_fin.
  (3) hBTrank : r+1 ≤ Bᵀ.rank — via rank_transpose (Bᵀ.rank = B.rank).
      ⟨ec, hec_inj, hec_li⟩ := exists_injective_linearIndependent_rows Bᵀ hBTrank   (s := r+1)
  (4) C := A.submatrix er ec : Matrix (Fin (r+1)) (Fin (r+1)) k.
      hCcol : C.col = fun i ↦ Bᵀ.row (ec i)  (by funext i j; simp [col/row/transpose/submatrix_apply]).
      hCli : LinearIndependent k C.col (rw hCcol; exact hec_li).
      IsUnit C from linearIndependent_cols_iff_isUnit; det ≠ 0 from isUnit_iff_isUnit_det.

The headline ← then: by_contra (¬ rank ≤ r), so r+1 ≤ A.rank; get the nonzero minor; contradiction
with the hypothesis "all (r+1)-minors vanish" (applied at the produced er, ec).

KEY SOUNDNESS QUESTIONS to attack:
1. STEP 2(4): C.col is claimed = (fun i ↦ Bᵀ.row (ec i)). But ec : Fin(r+1) → Fin q indexes COLUMNS
   of B (rows of Bᵀ), and C = A.submatrix er ec. Is "C has linearly independent COLUMNS" the correct
   thing extracted from "Bᵀ has r+1 independent ROWS selected by ec"? I.e. does picking r+1 independent
   ROWS of Bᵀ (= r+1 independent COLUMNS of B) actually make the SQUARE A.submatrix er ec have
   independent columns? Note B = A.submatrix er id, so B's columns ARE A's columns restricted to rows er;
   C's columns = B's columns restricted to the ec selection. Verify the column j of C equals column (ec j)
   of B equals row (ec j) of Bᵀ — i.e. the identity C.col = (fun i ↦ Bᵀ.row (ec i)) is TRUE, not just plausible.
2. Is there a circularity or a place where "rank" (the ℕ-valued Matrix.rank) is conflated with cardinal cRank?
3. The independence transported through exists_injective_linearIndependent_rows Bᵀ gives independent
   ROWS of Bᵀ; the proof uses them as independent COLUMNS of C. Could the square block C be a different
   matrix than the (r+1)×(r+1) sub-block whose columns those are? (er is REUSED for C's rows; is that the
   block whose columns were shown independent?)
4. Any hidden assumption that r+1 ≤ q or r+1 ≤ p needed but not supplied? (Does the embedding step or
   linearIndependent_cols_iff_isUnit silently require it, and is it discharged by r+1 ≤ A.rank ≤ min p q?)
</task>

<output_contract>
  Section 1: VERDICT — one of {sound, unsound, under-determined} for the ← direction as skeletoned.
  Section 2: For each of the 4 key questions, a 2-4 sentence adjudication. If you find a genuine gap,
             give the SPECIFIC step and a minimal concrete failure (e.g. a 2×3 matrix where the
             identity in question fails), not "seems risky".
  Section 3: Any OTHER soundness hole you found that the 4 questions missed (or "none").
  Keep it under ~500 words. Be precise, not polite.
</output_contract>

<grounding_rules>
  Mark each claim as (FACT: Mathlib semantics I'm confident of) vs (INFERENCE: my reasoning about the
  composition). If you're unsure whether a Mathlib lemma has the signature I stated, say so explicitly
  rather than assuming. Do not invent Mathlib lemma names. The question is logical soundness of the
  COMPOSITION given the stated lemma signatures — assume each individually-stated support lemma is
  correctly proved unless its STATEMENT is itself wrong.
</grounding_rules>
