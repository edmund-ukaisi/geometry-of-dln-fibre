<task>
Lean 4 Mathlib v4.29. ONE stuck goal — a dependent-cast/smul commute in a matrix-product induction.
I've tried 4 routes (subst, ▸-form helper, Eq.mpr); all fail to match. Need the exact tactic.

CONTEXT: `prodAux` (matrix-chain product) unfolds its successor step with a `by`-block that does
`rw [e1, e2]; exact A ⟨k, hkL⟩` where e1 e2 : Fin (L+1) index equalities. So `prodAux _ (k+1)` reduces
to `prodAux _ k * (Eq.mpr h1 (Eq.mpr h2 (layer)))` — the layer matrix wrapped in TWO `Eq.mpr` casts
(type equalities of `Matrix (Fin (H _)) (Fin (H _)) ℝ` across value-equal Fin indices).

THE EXACT STUCK GOAL (verbatim from the error; `⋯.mpr` are the two Eq.mpr casts):

  (prodAux H A k hk' *
      have e1 := ⋯; have e2 := ⋯;
      ⋯.mpr (⋯.mpr (c • A ⟨k, hkL⟩)))
    =
  c • (prodAux H A k hk' *
        have e1 := ⋯; have e2 := ⋯;
        ⋯.mpr (⋯.mpr (A ⟨k, hkL⟩)))

where c : ℝ, A ⟨k,hkL⟩ : Matrix (Fin (H ⟨k,hkL⟩.castSucc)) (Fin (H ⟨k,hkL⟩.succ)) ℝ, and the casts
retype it to Matrix (Fin (H ⟨k,hk'⟩)) (Fin (H ⟨k+1,hk⟩)) ℝ.

MATH: trivially true — c • commutes with the type-transport cast (ℝ-linear), then Matrix.mul_smul
pulls c out of the product. The ONLY friction is getting Lean to see `cast (c • M) = c • cast M`
through the TWO Eq.mpr layers.

WHAT FAILED:
1. `private theorem cast_smul_comm (c) (M) (e : α = β) : e ▸ (c•M) = c • (e ▸ M) := by subst e; rfl`
   → `subst e; rfl` FAILS: "⋯ ▸ (c • M) is not definitionally equal to c • ⋯ ▸ M" (motive goes through H).
2. `rw [hcast]` with hcast stated in `e1 ▸ e2 ▸` form → "Did not find pattern ⋯ ▸ ⋯ ▸ (c • ?M)"
   (goal has Eq.mpr, not ▸).

QUESTIONS:
1. The single cleanest tactic to discharge this goal. Options to rank: (a) `simp only [eq_mpr_eq_cast,
   cast_smul, ...]` with the right cast/smul-commute simp lemmas; (b) `Matrix.ext` entrywise then
   `Matrix.cast_apply`/`Matrix.smul_apply`; (c) reformulate to avoid the cast (a prodAux_step HEq
   helper consuming `HEq (A⟨k,hkL⟩) Mstep` then `Matrix.mul_smul` on the clean Mstep). Which is most
   robust at v4.29?
2. If (a): the exact Mathlib simp lemma names for "Eq.mpr/cast commutes with SMul" and "cast of a
   matrix product/smul". (`cast_smul`? `eq_mpr_eq_cast`? `Matrix.cast_apply`?)
3. If (c): how to set up the prodAux_step HEq helper so BOTH the scaled and unscaled successor unfold
   to `prodAux k * Mstep` with Mstep clean (no cast), so Matrix.mul_smul applies directly. (I have a
   working prodAux_step: HEq (A ⟨k,_⟩) Mstep → prodAux (k+1) = prodAux k * Mstep.)
</task>

<output_contract>
Rank the 3 options by robustness at v4.29; give the WINNING one as concrete tactic lines + exact
Mathlib lemma names. If (c) wins, show how to instantiate Mstep for the scaled side (Function.update
layer) so the cast vanishes. Terse, copy-pasteable. Flag any lemma name you're unsure exists at v4.29.
</output_contract>

<grounding_rules>
Reason from the goal + prodAux structure given. Don't invent lemma names — flag uncertain ones. The
math is trivial; I need the Lean idiom for the Eq.mpr-cast/smul commute specifically.
</grounding_rules>
