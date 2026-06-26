<task>
Lean 4 + Mathlib v4.29. ONE precise tactic-level goal I'm stuck on (3+ attempts). I need the exact
tactic block to CLOSE it. This is a defeq-vs-syntactic friction, not a math question.

CONTEXT. Inside an induction (`endpoint_telescoping`), at the base case `k+1 = 1`. After
`rw [reindex_mul_distrib_left ...]` (distributed `reindex (P⟨0⟩ * A⟨0⟩)`) and
`rw [show finCongr e1.symm = Equiv.refl _ from finCongr_refl _, show finCongr e2.symm = Equiv.refl _ ...]`
(`e1, e2 : rfl`-typed index equalities), the goal is (trace_state, verbatim):

    ⊢ 1 *
        ((reindex (Equiv.refl (Fin (H ⟨0, hkL'⟩.castSucc))) (Equiv.refl (Fin (H ⟨0, hkL'⟩.castSucc)))) (P ⟨0, hkL'⟩) *
          (reindex (Equiv.refl (Fin (H ⟨0, hkL'⟩.castSucc))) (Equiv.refl (Fin (H ⟨0, hkL'⟩.succ)))) (A ⟨0, hkL'⟩)) =
      P ⟨0, ⋯⟩ *
        (1 * (reindex (Equiv.refl (Fin (H ⟨0, hkL'⟩.castSucc))) (Equiv.refl (Fin (H ⟨0, hkL'⟩.succ)))) (A ⟨0, hkL'⟩))

where:
- `H : Fin (Lm+2) → ℕ`, `hkL' : 0 < Lm+1`, `⟨0, hkL'⟩ : Fin (Lm+1)`.
- `P ⟨0, hkL'⟩ : Matrix (Fin (H ⟨0,hkL'⟩.castSucc)) (Fin (H ⟨0,hkL'⟩.castSucc)) ℝ` (square).
- `A ⟨0, hkL'⟩ : Matrix (Fin (H ⟨0,hkL'⟩.castSucc)) (Fin (H ⟨0,hkL'⟩.succ)) ℝ`.
- The TWO `1`s and the RHS `P ⟨0, ⋯⟩` are typed at `Fin (H 0)` (= `Fin (H (0 : Fin (Lm+2)))`),
  while the products live at `Fin (H ⟨0,hkL'⟩.castSucc)`. `H 0` and `H ⟨0,hkL'⟩.castSucc` are
  DEFINITIONALLY EQUAL (`(0:Fin(Lm+2)) = (⟨0,hkL'⟩:Fin(Lm+1)).castSucc` by `Fin.ext`) but NOT syntactic.
- The RHS `P ⟨0, ⋯⟩` is `h0cs ▸ P ⟨0, hkL'⟩` where `h0cs : (⟨0,_⟩:Fin(Lm+1)).castSucc = (0:Fin(Lm+2))`.

WHAT FAILS:
- `rw [Matrix.one_mul]` / `simp only [Matrix.one_mul]` → "did not find pattern" / "no progress": the `1`'s
  type `Matrix (Fin (H 0)) (Fin (H 0))` doesn't syntactically match the product's row type
  `Fin (H ⟨0,hkL'⟩.castSucc)` (defeq only), so `Matrix.one_mul`'s LHS `(1 : Matrix m m) * M` won't unify.
- `rw [Matrix.reindex_refl_refl ...]` → "did not find pattern" (the implicit type metavars don't unify;
  same defeq friction on the `Equiv.refl (Fin (H ⟨0,hkL'⟩.castSucc))`).
- `simp only [Matrix.reindex_refl_refl]` → "no progress" (likely already defeq-reduced, nothing to rewrite).
- `ext i j; simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
  Equiv.coe_refl, id_eq, Matrix.one_apply, ...]` → leaves an unsolved goal (submatrix not fully collapsed).

The MATH is trivial: `reindex (refl)(refl) M = M`, `1 * M = M`, and `reindex refl refl P⟨0⟩ = h0cs ▸ P⟨0⟩`
(both transport `P⟨0⟩` across defeq index proofs). So both sides equal `P⟨0⟩ * A⟨0⟩`. The ENTIRE obstacle
is the defeq-not-syntactic `H 0` vs `H ⟨0,hkL'⟩.castSucc` blocking `one_mul`/`reindex_refl_refl`.
</task>

<output_contract>
Give the EXACT tactic block (Lean 4 / Mathlib v4.29) that closes this goal, with a one-line why for each
tactic. Prioritize ROBUST idioms for defeq-blocked-rewrite (e.g. `Matrix.ext` + `Matrix.mul_apply` +
`Matrix.one_apply` + `Finset.sum` collapse done RIGHT; or `convert`-with-`using`; or `show` to retype the
`1`/reindex to the syntactic form first; or `Matrix.reindex_refl_refl` applied via `conv`; or
`simp [Matrix.submatrix_id_id]` after `Equiv.refl_symm`). If the entry route is right, give the COMPLETE
correct simp set (what was missing from my attempt). Flag any lemma name as "(verify)" if unsure it exists
in v4.29. Keep under 350 words.
</output_contract>

<grounding_rules>
This is a concrete goal — give a concrete tactic block, not strategy prose. If you're unsure a lemma
exists, say so and give the fallback. Distinguish "this will close it" from "try this."
</grounding_rules>
