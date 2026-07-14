<task>
Lean 4 + Mathlib v4.29. I must prove ONE theorem (currently `sorry`):

  theorem routeMLayerBoxIntegral_comp_rev (M : Fin (L + 1) → ℕ) (c' : ℝ) :
      routeMLayerBoxIntegral M c' 1 = routeMLayerBoxIntegral (M ∘ Fin.rev) c' 1

Definitions:
  Params (H : Fin (L+1) → ℕ) := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ
  prodAux H A : (k:ℕ) → k<L+1 → Matrix (Fin (H 0)) (Fin (H ⟨k,_⟩)) ℝ
     | 0 => 1 ; | k+1 => (prodAux H A k) * (layer k, reindexed to running widths)   -- LEFT-assoc PREFIX fold
  prod H A : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ := prodAux H A L _
  frobSq (X : a → b → ℝ) := ∑ i, ∑ j, (X i j)^2       -- squared Frobenius
  paramsBoxM M T := {A : Params M | ∀ s i j, A s i j ∈ Icc (-T) T}   -- entrywise box
  routeMLayerBoxIntegral M c' T := ∫⁻ A in paramsBoxM M T, ENNReal.ofReal ((frobSq (prod M A))^(-c'))

Math: reversing the chain M ↦ M∘Fin.rev and transposing each layer sends A=(A_0,…,A_{L-1}) to
revParams A with (revParams A) s = reindex (finCongr h_r) (finCongr h_c) ((A (Fin.rev s))ᵀ) (Fin.rev on Fin L),
and prod (M∘Fin.rev) (revParams A) = (prod M A)ᵀ (up to a width reindex), frobSq is transpose-invariant,
so the two box integrals are equal via a measure-preserving change of variables.

BANKED lemmas available (all sorry-free, exact names):
  - prodAux_succ H A k hk (e1 e2 : rfl-true width eqs) :
        prodAux H A (k+1) hk = prodAux H A k _ * Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k,_⟩)
  - prod_front_peel (M : Fin (L+1+1)→ℕ) A (emid ecol) :
        prod M A = A 0 * Matrix.reindex (finCongr emid) (finCongr ecol) (prod (Mtail M) (Atail M A))
      where Mtail M i = M i.succ, Atail M A s = (A s.succ) recast.
  - reindex_finCongr_mul (ha hb hc : nat eqs) X Y :
        reindex (finCongr ha) (finCongr hc) (X*Y) = reindex (finCongr ha)(finCongr hb) X * reindex (finCongr hb)(finCongr hc) Y
  - mul_three_reassoc a b c : a*b*c = a*(b*c)  (dodges dependent-HMul rw failure)
  - paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ), measure-preserving (measurePreserving_paramsEquivFlat),
      with decode  paramsEquivFlat_decodeM M A idx : paramsEquivFlat M A (equivFin (FlatIdx M) idx) = A idx.1.1 idx.1.2 idx.2,
      and paramsEquivFlat_preimage_paramsBoxM M T : paramsEquivFlat M ⁻¹' cubeBox = paramsBoxM M T.
      FlatIdx M = Σ (q : Σ s:Fin L, Fin (M s.castSucc)), Fin (M q.1.succ).
  - Mathlib: measurePreserving_piCongrLeft (f : ι'≃ι) : MeasurePreserving (MeasurableEquiv.piCongrLeft α f) (pi (μ∘f)) (pi μ);
      volume_measurePreserving_piCongrLeft; MeasurableEquiv.piCongrLeft (π) (f) : (∀ b, π (f b)) ≃ᵐ ∀ a, π a.
      Matrix.transpose_mul (M*N)ᵀ=NᵀMᵀ; Matrix.transpose_reindex; Matrix.transpose_transpose; Matrix.transpose_one.
      Fin.val_rev, Fin.rev_rev, Fin.revPerm.  NO transpose/pi-swap MeasurePreserving lemma exists in Mathlib.
  - MeasurePreserving.setLIntegral_comp_preimage_emb (used already):
        (mp).setLIntegral_comp_preimage_emb (emb) g s : ∫⁻ y in s, g y = ∫⁻ x in f⁻¹' s, g (f x).

Two design questions:

Q1 (the crux identity `prod_revParams`): cleanest way to prove
   prod (M∘Fin.rev) (revParams A) = reindex (finCongr e_row) (finCongr e_col) ((prod M A)ᵀ)?
   The obstruction: prodAux is a PREFIX fold; reversing turns prefix into SUFFIX, so a naive induction
   on prodAux (M∘rev) doesn't line up with prodAux M. I have prod_front_peel (peel FIRST layer of M).
   Option A: induction on L, peel A_0 off the front of prod M A (prod_front_peel) + peel the LAST layer
     off prod(M∘rev)(revParams A) (prodAux_succ, whose last layer = (A_0)ᵀ), then relate the middle to
     prod((Mtail M)∘rev)(revParams(Mtail M)(Atail M A)) by IH — but this needs a "prodAux (M∘rev) L = prod
     of a HEAD-truncated chain" step (drop the last vertex), a DIFFERENT truncation than Mtail. Is there a
     slicker invariant?
   Give the recommended induction statement (exact, with the reindex casts) + the key rewrite steps.

Q2 (the measure-preserving change of variables): which is cleaner —
   Route A: build revParams as an explicit MeasurableEquiv = (piCongrLeft.symm layer-reversal on Fin.revPerm)
     ∘ (per-layer transpose) ∘ (per-layer finCongr reindex), proving MP factor-by-factor. Blocker: transpose
     MP and per-fiber piCongrRight MP are not in Mathlib (I can prove transpose-MP via Measure.pi_eq + Finset.prod_comm ~15 lines).
   Route B: conjugate revParams through paramsEquivFlat on both sides and show
     paramsEquivFlat M' ∘ revParams = piCongrLeft (fun _=>ℝ) σ ∘ paramsEquivFlat M for an explicit index
     bijection σ realizing ((s,i),j) ↦ ((rev s,j),i); MP then from measurePreserving_piCongrLeft + the two flat MPs.
     Need flatDim M = flatDim M' and the decode-matching.
   Recommend one, with the specific Mathlib lemma names for the MP factors and the sharpest way to prove
   box-preservation (revParams '' paramsBoxM M 1 = paramsBoxM M' 1) and the frobSq transpose+reindex invariance.
</task>

<output_contract>
Two sections, Q1 and Q2. For Q1: the exact recommended lemma statement(s) (Lean, with the finCongr/reindex
casts spelled out) and an ordered list of the rewrite steps (naming banked lemmas). For Q2: pick Route A or B,
justify in 2-3 sentences, then give the concrete construction + the exact Mathlib lemma names for each MP
factor, plus one-line strategies for box-preservation and frobSq invariance. Be concrete about cast handling
(equiv-level, per CLAUDE.md's prodAux-reassoc kernel). Flag any step you are UNCERTAIN compiles vs is standard.
</output_contract>

<grounding_rules>
Mark each claimed Mathlib lemma name as (confident) or (guess — verify). If a route has a hidden wall, say so.
Do not invent lemma names; if unsure a lemma exists, say "verify existence".
</grounding_rules>
