**Ranking**
1. **(a)** Best: swap `p` with `0`; no need to order `active`, and the matrix becomes lower triangular directly.
2. **(e)** Sound, but more plumbing: `twoBlockTriangular_det'` splits active/spectator cleanly; reusing all-active det adds subtype/cardinality casts.
3. **(c)** Sound all-x, but Laplace on general `Fin N` is avoidable cofactor bookkeeping.
4. **(b)** The division column-clear is unsound for all `x`; a division-free multilinearity variant exists but is not clean.
5. **(d)** Sound but worst: determinant permutation support is combinatorial noise.

**TOP PICK**
Use route **(a)**.

1. Define `z : Fin N := ⟨0, ... from p.isLt⟩`, `σ : Fin N ≃ Fin N := Equiv.swap z p`.
   `Equiv.swap_apply_left/right`, `Equiv.swap_apply_eq_iff` — confident (v4.29).

2. Work with `Mσ := M.submatrix σ σ`.
   `Matrix.det_submatrix_equiv_self (e : n ≃ m) (A) : det (A.submatrix e e) = det A` — confident (v4.29).

3. Prove `Mσ.BlockTriangular OrderDual.toDual`.
   `Matrix.BlockTriangular`, `OrderDual.toDual_lt_toDual` — confident (v4.29).
   After rewriting, the hypothesis is `i < j`; use `pbon_entry`.

4. Key zero facts inside the triangular proof:
   `σ j = p ↔ j = z`, and `i < j` implies `j ≠ z`; also `i < j` gives `σ j ≠ σ i`.

5. Apply triangular determinant:
   `Matrix.det_of_lowerTriangular (M) (h : M.BlockTriangular OrderDual.toDual) : M.det = ∏ i, M i i` — confident (v4.29).

6. Diagonal formula:
   `Mσ i i = if i = z then 1 else if σ i ∈ active then x p else 1`.
   This is `pbon_entry` plus `σ i = p ↔ i = z`.

7. Let `S := Finset.univ.filter fun i => i ≠ z ∧ σ i ∈ active`.
   Convert product to `(x p) ^ S.card` using:
   `Finset.prod_ite_mem`, `Finset.prod_const` — confident (v4.29).

8. Count `S.card = active.card - 1` by mapping `S` to `active.erase p` via `σ`.
   `Finset.card_equiv`, `Finset.mem_erase`, `Finset.card_erase_of_mem hp` — confident (v4.29).

**Trickiest step:** the finite-set count in step 8. Prove the membership equivalence for `Finset.card_equiv σ`:
`i ∈ S ↔ σ i ∈ active.erase p`,
using `σ i = p ↔ i = z`. This also handles the `p = 0` case.