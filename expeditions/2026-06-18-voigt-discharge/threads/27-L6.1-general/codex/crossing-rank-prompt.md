# Crossing-rank computation in Lean 4 (Mathlib v4.29): cleanest tactic route

I'm formalising a type-A quiver "box move". I need the rank of a specific 3-fold matrix product
and want the LIGHTEST Lean tactic route, avoiding `finSumFinEquiv`/`fromBlocks` entry-chasing thrash.

## Setup (all landed, sorry-free)

`Tuple d` = `(t : Fin N) → Matrix (Fin (d t.succ)) (Fin (d t.castSucc)) k`, `k` a field.
`submult d A i j : Matrix (Fin (d j)) (Fin (d i)) k` = product `A_j ⋯ A_{i+1}` (identity at i=j).
`rankPattern d A i j := (submult d A i j).rank`.
`intervalDim i j l := if i ≤ l ∧ l ≤ j then 1 else 0`.
`intervalModule i j : Tuple (intervalDim i j)` = const-1 on active edges.
`dirSum A B : Tuple (fun l ↦ d l + d' l)` = `reindex finSumFinEquiv (fromBlocks A_t 0 0 B_t)`.
Landed: `submult_dirSum` (submult of dirSum = reindex fromBlocks of the two submults);
`submult_intervalModule_subset i j : [i',j']⊆[i,j] → submult (M_ij) i' j' = (fun _ _ ↦ 1)` (const-1);
`rank_const_one` (const-1 over Unique×Unique types = 1); `rank_eq_zero_of_isEmpty_rows/cols`;
`rankPattern_dirSum` (= sum of the two); `rankPattern_intervalModule` (= containment indicator).

`d₂ l := intervalDim a e l + intervalDim c b.castSucc l`.
`U₂ := dirSum (intervalModule a e) (intervalModule c b.castSucc)`.
`splice λ : Tuple d₂` = `U₂` off edge `b`; at edge `b` (entrywise, scalar-level)
  `splice λ b r s = match finSumFinEquiv.symm s with inl _ => λ | inr _ => 1`  (the `[λ,1]` row).

Landed crossing factorization (for `i ≤ b.castSucc`, `b.succ ≤ j`):
  `submult (splice λ) i j = submult U₂ b.succ j * splice λ b * submult U₂ i b.castSucc`.

## The regime and target

Non-split box: `a < c`, `c ≤ b.castSucc`, `b.succ ≤ e`. Crossing: `i ≤ b.castSucc`, `b.succ ≤ j`.
Note `intervalDim c b.castSucc j = 0` (j > b.castSucc): so `d₂ j = intervalDim a e j` ∈ {0,1}; row
count ≤ 1, so `rank ≤ 1` (have `rank_le_card_height`). I have helpers
`matrix_eq_zero_of_rank_eq_zero` and `one_le_rank_of_ne_zero` (nonzero entry ⟹ rank ≥ 1).

Target (sympy-certified): for `i ≤ b.castSucc < b.succ ≤ j`,
  `rankPattern (splice λ) i j = if (j ≤ e) ∧ ((λ ≠ 0 ∧ a ≤ i) ∨ c ≤ i) then 1 else 0`.
(matches upstairs `[a≤i∧j≤e]+[c≤i∧j≤b]` for λ≠0 and downstairs `[a≤i∧j≤b]+[c≤i∧j≤e]` for λ=0,
 using `j > b.castSucc` to kill the `j ≤ b.castSucc` indicators).

## Question

What is the cleanest Lean tactic route to compute this crossing rank?

Options I'm weighing:
(A) `rank ≤ 1` via height + nonzero-entry / matrix-is-zero split, evaluating the triple product
    entry `((above*recomb)*below) r₀ s₀` via `Matrix.mul_apply` twice through `fromBlocks`/
    `finSumFinEquiv.symm`. Worried about index thrash.
(B) Rewrite the `intervalDim … = 0/1` to literals first (so the `Fin` types become concrete
    `Fin 0/1/2`), reducing `fromBlocks`/`finSumFinEquiv`, then `fin_cases`/`decide`. Worried about
    the `▸`/`Eq.mpr` casts from the dim rewrites contaminating the matrix.
(C) Use that `above = submult U₂ b.succ j` is a 1×1 const-1 (= unit, det 1) when j≤e and reduce
    `rank (above * X) = rank X` — but the square-type needed by `rank_mul_eq_right_of_isUnit_det`
    is `Fin (d₂ j)` vs `Fin (d₂ b.succ)`, not syntactically equal. Is there a clean way?
(D) Avoid the factorization: compute `submult (splice λ) i j` directly by `Fin.induction` peeling
    from j, tracking the matrix as a single row vector once past edge b.

Give me: the recommended option, the specific Mathlib lemmas/tactics, and the 2-3 worst pitfalls
for that route at the v4.29 pin. Concrete and Lean-specific. No need to write full proofs.
