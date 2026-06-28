<task>
Lean4/Mathlib. I'm proving `prod (paramRowFirst R A) = (prod A).submatrix R id`, the row-permutation
analog of an existing `prod_paramColPermLast` (last-layer column perm). Need the cleanest induction shape.

## Defs (exact)
- `Params H := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`
- `prodAux H A : (k:ℕ) → (hk:k<L+1) → Matrix (Fin (H 0)) (Fin (H ⟨k,hk⟩)) ℝ`
    | 0,_ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
    | k+1,hk => (prodAux H A k _) * (A ⟨k,_⟩  [cast to the right widths])
  So it's a LEFT-associated PREFIX fold; the FIRST layer A⟨0⟩ enters at the k=0→1 step
  (prodAux 1 = 1 * A⟨0⟩ = A⟨0⟩).
- `prod H A := prodAux H A L (Nat.lt_succ_self L)`
- `firstLayer hL : Fin L := ⟨0,_⟩`; (firstLayer).castSucc = (0 : Fin (L+1)), so A(firstLayer) has
  row-width H 0.
- `paramRowFirst H hL (R : Equiv.Perm (Fin (H 0))) (A : Params H) : Params H :=`
    `Function.update A (firstLayer hL) ((A (firstLayer hL)).submatrix (R-as-fun, into the H 0 width) id)`
  (row-permute ONLY the first layer; the row index R lives on Fin (H 0) = Fin (H (firstLayer).castSucc)).

## The subtlety
The colPerm proof peels the LAST layer (one prodAux_succ step at the top). For rowPerm the perm enters
the FIRST layer = the BASE of the fold. The natural invariant
   prodAux (τ_R A) k = (prodAux A k).submatrix R id
does NOT hold at k=0 (prodAux 0 = 1, but 1.submatrix R id = permutation matrix ≠ 1). It holds for k≥1,
established at k=1 (prodAux 1 = A⟨0⟩ → (A⟨0⟩).submatrix R id) and propagated by left-submatrix
distributing over right-multiplication: (M.submatrix R id) * N = (M * N).submatrix R id.

## Available
- `prodAux_succ` / `prodAux_step` (HEq-discharged succ-step: prodAux (k+1) = prodAux k * Mstep, with
  HEq A⟨k⟩ Mstep). Used in colPerm's proof.
- `submatrix_mul_equiv` (Mathlib): the colPerm proof used
    `rw [← submatrix_mul_equiv (prodAux ...) Mstep id (Equiv.refl _) Pfun]` to push a RIGHT submatrix
    through the product. I need the LEFT analog: a row-submatrix on the LEFT factor pulls out of the product.
- For interior layers k≥1 the τ_R-tuple AGREES with A (Function.update only touched firstLayer), so
  prodAux(τ_R) and prodAux(A) share all step matrices except the k=0 one.

## Questions
1. Cleanest induction: prove `∀ k (hk:k<L+1), 1 ≤ k → prodAux (τ_R A) k hk = (prodAux A k hk).submatrix R id`
   by induction on k, base k=1, step via prodAux_step + the left-submatrix-mul lemma? Or is there a slicker
   route (e.g. prove prodAux(τ_R) k = (perm-matrix) * prodAux(A) k for ALL k≥0 including 0, where at k=0
   it's perm*1 = perm, sidestepping the base-shift — then prod = perm * prod A, and perm * M = M.submatrix R id)?
   I lean toward the second (the "factor the permutation matrix on the left" invariant holds at k=0 too:
   prodAux(τ_R) 0 = 1 = (R-perm-matrix) * 1? NO — prodAux(τ_R) 0 = 1, not perm. Hmm.) Clarify which invariant
   is clean.
2. The EXACT Mathlib lemma for "left row-submatrix pulls out of a matrix product":
   `(M.submatrix R id) * N = (M * N).submatrix R id`? Is it `Matrix.submatrix_mul` / `submatrix_mul_equiv`
   with the right equiv slots (R on the left rows, id on the shared middle, id on N's cols)? Give the exact
   call (the colPerm one was `submatrix_mul_equiv A B e₁ e₂ e₃` form).
3. Is `paramRowFirst` as a `Function.update` of the first layer the right def, matching how colPerm did
   `paramColPermLast` (update of last layer)? Any first-vs-last asymmetry in the Function.update /
   prodAux_update_eq_of_le reasoning I should expect?

Answer crisply: the recommended invariant + induction, the exact submatrix-mul lemma call, and any
first-layer-specific gotcha vs the last-layer colPerm proof.
