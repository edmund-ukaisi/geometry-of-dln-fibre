<task>
Lean 4 / Mathlib v4.29. I'm proving a matrix-product characterization and stuck on a dependent-`cast` on a `Matrix` type. Need the clean cast-elimination idiom (NOT more `simp` permutations).

CONTEXT. `prod` is defined via a recursion `prodAux` that builds `A⁽⁰⁾ · A⁽¹⁾ · …` over a dependent `Fin`-indexed family. For the L=2 case `H = ![2,2,2]`, the layers are
  `A 0 : Matrix (Fin (H 0.castSucc)) (Fin (H 0.succ)) ℝ`   -- = Matrix (Fin 2) (Fin 2) ℝ
  `A 1 : Matrix (Fin (H 1.castSucc)) (Fin (H 1.succ)) ℝ`   -- = Matrix (Fin 2) (Fin 2) ℝ
where the index Nats `H 0.succ`, `H 1.castSucc` are all DEFEQ to 2 (via `Matrix.cons_val`) but NOT syntactically `2`. `prodAux`'s recursion does `rw [e1, e2]` with `e1 e2 : Fin-index equalities`, producing `cast`s on the matrix TYPE (these are `congrArg`-casts, not `rfl`).

TARGET:
  `prod (![2,2,2]) A i j = ∑ k : Fin 2, A 0 i k * A 1 k j`   (i j : Fin 2)

After `unfold prod; simp only [prodAux, Matrix.mul_apply, eq_mpr_eq_cast, Fin.sum_univ_two]`, the goal is:
  `⊢ ∑ x, (1 * cast h₁ (A ⟨0,_⟩)) i x * cast h₂ (A ⟨1,_⟩) x j = A 0 i 0 * A 1 0 j + A 0 i 1 * A 1 1 j`
where `h₁ : Matrix (Fin 2) (Fin (H 0.succ)) ℝ = Matrix (Fin 2) (Fin (H 1.castSucc)) ℝ`-style (the inner contraction dim differs propositionally), the `1 *` is `(1 : Matrix _ _) *`, and the LHS `∑ x` is over the cast-typed index so `Fin.sum_univ_two` does NOT fire on it.

WHAT I'VE TRIED (all stall): `simp [cast_eq]` (no progress — cast proof isn't rfl); `Matrix.cast_apply` (unknown constant); `Matrix.one_mul` (won't fire — cast between `1*` and matrix); `norm_num [...]` (reduces RHS + double-cast→single but LHS sum + `1*` + single cast survive).
</task>

<output_contract>
Give the SHORTEST robust tactic idiom to eliminate the `cast h (A k)` on a `Matrix (Fin a)(Fin b) ℝ` type where a,b are defeq-to-2-but-not-syntactic, so the goal closes. Rank 2-3 concrete approaches (e.g. (a) a `Fin.cast`/`finCongr` reindex pushing cast to indices via which exact Mathlib lemma; (b) `subst`ing the underlying `Nat` equality `H s = 2` to make cast `rfl`; (c) a clean helper lemma `(cast (congrArg (Matrix (Fin a) ·) hn) M) i k = M i (Fin.cast hn.symm k)` proved by `cases hn`/`subst`). For the top pick give the exact ~3-5 line Lean tactic block. Be terse; this is Lean-idiom, not math.
</output_contract>

<grounding_rules>
Mathlib v4.29 — if you name a lemma, flag it as "verify exists" (I'll grep). Prefer `cases`/`subst` on the Nat-eq or a `congr`-based push over guessing simp-lemma names. The math is trivially true (it's the def of matrix mult); this is purely discharging the dependent-`Fin`-cast bookkeeping.
</grounding_rules>
