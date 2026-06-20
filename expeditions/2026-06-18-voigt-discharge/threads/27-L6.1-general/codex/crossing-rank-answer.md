**Recommendation**
- Option **A**, but streamline it: bound `rank ≤ 1` with `rank_le_card_height`, then split on `rank = 0` vs `> 0`, proving the nonzero branch by exhibiting a single witness entry. keeps types unchanged and avoids det/isUnit hassles.

**Key Mathlib Ingredients**
- `Matrix.rank_le_card_height`, `matrix_eq_zero_of_rank_eq_zero`, `one_le_rank_of_ne_zero`.
- `Matrix.mul_apply` + `Matrix.ext` (only once) to unfold the triple product; immediately use `simp` with lemmas you already landed (`submult_dirSum`, `submult_intervalModule_subset`, `rankPattern_intervalModule`).
- `LinearIndependent.rank_eq_card_basis_image` is optional ammo if you need a quick “rank 1” once the witness entry is nonzero.
- `Finset`-free facts: `Fin.exists_iff` for picking the unique row index, `by_cases h : ...` then `simp [intervalDim, d₂, h]` to collapse any 0/1 dimensions without touching equality casts.

**Pitfalls to Watch**
- `Matrix.mul_apply` nests `finSumFinEquiv`; always follow with `simp` using `[simp]` lemmas for your `submult_dirSum`/interval modules to annihilate the off-diagonal blocks immediately, or the sums balloon.
- Be aggressive with `simp [intervalDim, d₂, Nat.succ_le_succ_iff, Fin.lt_iff_val_lt_val]` before `matrix_eq_zero_of_rank_eq_zero`; otherwise `Fin.cast` coercions proliferate and block the zero-entry check.
- When extracting the decisive entry, ensure the indices live in the 1-element fibres; use `have hrows : Nonempty (Fin (d₂ j)) := ...` before `choose` to avoid `isEmpty`-related elaboration failures that only show up on the `j > e` branch.

Happy to sketch the tactic script if that’d help.
