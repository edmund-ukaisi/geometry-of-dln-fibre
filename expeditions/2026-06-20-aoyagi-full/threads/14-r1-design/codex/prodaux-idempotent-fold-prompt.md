<task>
Lean 4 + Mathlib v4.29. I am proving a `prodAux` (left-fold matrix product) idempotent-fold lemma and
hit a `finCongr`-cast normalization wall (3 attempts spent). I need the DIAGNOSIS of why my simp-strip
fails and the cheapest tactic to strip the `finCongr` reindex, NOT a full rewrite.

CONTEXT (all decls exist, build green except the target):

`prodAux H A : (k:ℕ) → (k < L+1) → Matrix (Fin (H 0)) (Fin (H ⟨k,_⟩)) ℝ` is a left-fold:
  prodAux 0 _ = 1 ; prodAux (k+1) hk = prodAux k _ * (by rw[e1,e2]; exact A ⟨k,hkL⟩)
where e1 : H ⟨k,hk'⟩ = H (⟨k,hkL⟩.castSucc), e2 : H ⟨k+1,hk⟩ = H (⟨k,hkL⟩.succ), both `by rfl`
(defeq, Fin proof-irrelevance), hkL : k<L, hk' : k<L+1.

I PROVED (green):
  theorem prodAux_succ (H A k hk) (e1 e2) :
    prodAux H A (k+1) hk = prodAux H A k _ *
      Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k,hkL⟩)
  := by obtain rfl : e1 = rfl := Subsingleton.elim _ _; obtain rfl : e2 = rfl := Subsingleton.elim _ _; rfl

  theorem corner_reindex_mul {a b c r} (eA : Fin a ≃ Fin r ⊕ Fin (a-r)) (eB ...) (eC ...) :
    reindex eA.symm eB.symm (fromBlocks 1 0 0 0) * reindex eB.symm eC.symm (fromBlocks 1 0 0 0)
      = reindex eA.symm eC.symm (fromBlocks 1 0 0 0)
  := by simp only [reindex_apply, Equiv.symm_symm]; rw [submatrix_mul_equiv ...]; congr 1; rw [fromBlocks_multiply]; simp

  framedParamsReg_zero : framedParamsReg H r hr hL 0 s
    = reindex (rThresholdSplit r (H s.castSucc) _).symm (rThresholdSplit r (H s.succ) _).symm (fromBlocks 1 0 0 0)

TARGET (the wall):
  prodAux_framedParamsReg_zero_aux : ∀ k hk, 1 ≤ k →
    prodAux H (framedParamsReg H r hr hL 0) k hk
      = reindex (rThresholdSplit r (H 0) _).symm (rThresholdSplit r (H ⟨k,hk⟩) _).symm (fromBlocks 1 0 0 0)
  induction k; succ case: after `rw [prodAux_succ ... e1 e2, framedParamsReg_zero ... ⟨k,hkL⟩]`
  and `obtain rfl : e1 = rfl; obtain rfl : e2 = rfl`, the goal is (trace_state, verbatim):

    ⊢ prodAux H (framedParamsReg H r hr hL 0) k ⋯ *
        (reindex (finCongr ⋯) (finCongr ⋯)
          (reindex (rThresholdSplit r (H (⟨k,hkL⟩.castSucc)) ⋯).symm
                   (rThresholdSplit r (H (⟨k,hkL⟩.succ)) ⋯).symm (fromBlocks 1 0 0 0)))
      = reindex (rThresholdSplit r (H 0) ⋯).symm (rThresholdSplit r (H ⟨k+1,hk⟩) ⋯).symm (fromBlocks 1 0 0 0)

  The OUTER `reindex (finCongr ⋯) (finCongr ⋯)` is from prodAux_succ; the `⋯` proofs are e1.symm/e2.symm,
  now `rfl` (post obtain rfl) but TYPED `H ⟨k,hk'⟩ = H (⟨k,hkL⟩.castSucc)` (defeq-not-syntactic LHS/RHS).

WHAT FAILED (all 3 attempts, "simp made no progress" or "rewrite pattern not found"):
  (1) simp only [finCongr_refl, Equiv.refl_symm, Matrix.reindex_refl_refl]  -- no progress
  (2) rw [show <the explicit nested reindex term> = <stripped> from rfl]    -- pattern not found
  (3) simp only [finCongr_refl, Matrix.reindex_refl_refl, eq_mpr_eq_cast, cast_eq]  -- no progress

DIAGNOSIS I have: finCongr_refl's LHS is `finCongr (rfl : n = n)` (syntactic `n = n`); here the proof
inside `finCongr ⋯` has type `H ⟨k,hk'⟩ = H (⟨k,hkL⟩.castSucc)` — the two sides are DEFEQ but NOT
syntactically identical, so finCongr_refl won't unify.

Mathlib facts confirmed present at v4.29: `finCongr (rfl : n=n) = Equiv.refl (Fin n)` holds `by rfl`;
`Matrix.reindex_refl_refl : reindex (Equiv.refl _) (Equiv.refl _) A = A` (rfl); `reindex_apply`,
`submatrix_submatrix`, `submatrix_mul_equiv`, `fromBlocks_multiply`.
</task>

<output_contract>
1. ROOT CAUSE (2-3 sentences): exactly why the three strips fail on this goal term.
2. CHEAPEST FIX: the single tactic block (≤8 lines) that strips the outer `reindex (finCongr ⋯) (finCongr ⋯)`
   to leave the bare inner reindex, so `corner_reindex_mul` (after `rw [ih ...]`) closes it. Prefer:
   - a `convert ... using N` that absorbs the finCongr into a `Subsingleton.elim`/`Fin.cast` residual, OR
   - generalizing the finCongr proofs with `generalize`/`cases` to collapse them, OR
   - a `Matrix.reindex_reindex`/`submatrix_submatrix` composition that merges outer+inner reindex then aligns.
   State which Mathlib lemma names you rely on (must exist at v4.29; flag any you're unsure of).
3. IF the clean strip is genuinely an HEq-induction (no cheap tactic): say so explicitly, and give the
   minimal restructure (e.g. state the aux lemma with `Fin.cast`/`finCongr` ABSORBED into the statement so
   the induction step never produces a stray finCongr).
</output_contract>

<grounding_rules>
Flag any lemma name you are not certain exists at Mathlib v4.29 (the pin) as "VERIFY". Distinguish "this
will work" (you've reasoned it through the types) from "try this" (plausible but unverified). Do not invent
lemma names. The goal term above is OBSERVED (trace_state output), not my paraphrase.
</grounding_rules>
