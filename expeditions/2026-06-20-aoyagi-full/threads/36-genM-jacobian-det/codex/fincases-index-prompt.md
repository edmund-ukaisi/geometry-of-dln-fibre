# Lean 4 (Mathlib v4.29) tactic question — matrix entry equality at dependent-Fin widths

I'm proving a `Matrix.ext` layer equality in Lean 4 / Mathlib v4.29. After `ext i j; fin_cases i; fin_cases j`,
I have residual scalar goals of this exact form (the matrices are typed at DEPENDENT-Fin widths that are
defeq but not SYNTACTICALLY `Fin 1`/`Fin 2`):

```
⊢ (x 0 • !![1, x 7] - !![x 1] * !![x 2, x 3]) ⟨0, ⋯⟩ ⟨0, ⋯⟩ =
    vecCons (![x 0 - x 1 * x 2, x 0 * x 7 - x 1 * x 3] ⟨0, ⋯⟩) (fun i => ![x 2, x 3] ⟨0, ⋯⟩) ⟨0, ⋯⟩
```

Here:
- The LHS `x 0 • !![1, x 7]` is `Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ`,
  where `Text M222 tach222 2` REDUCES to `1` and `Wext M222 2` reduces to `2` by `decide`/`rfl`, but the
  type is NOT the syntactic literal `Fin 1` / `Fin 2`.
- `!![x 1] : Matrix (Fin (Text M222 tach222 2)) (Fin (Wext M222 1 - Text M222 tach222 2)) ℝ` (1×1),
  `!![x 2, x 3] : Matrix (Fin (Wext M222 1 - Text M222 tach222 2)) (Fin (Wext M222 2)) ℝ` (1×2).
- The RHS is `!![x0-x1*x2, x0*x7-x1*x3; x2, x3] : Matrix (Fin (Wext M222 1)) (Fin (Wext M222 2)) ℝ`
  (the index after `fin_cases` is `⟨0, ⋯⟩ : Fin (Wext M222 1)`, where `Wext M222 1` reduces to `2`).

KEY OBSERVATIONS (both verified to elaborate):
1. `(!![a,b;c,d] : Matrix (Fin (Wext M222 1)) (Fin (Wext M222 2)) ℝ) (⟨0, by decide⟩) (⟨0, by decide⟩) = a`
   closes by `rfl`. So `!![..]` applied at an explicit `⟨k, by decide⟩` Fin.mk index DOES reduce by `rfl`.
2. The EXACT scalar goal, when stated DIRECTLY with explicit `⟨0, by norm_num⟩` / `⟨0, by decide⟩` indices
   (NOT via `fin_cases`), closes by plain `simp [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
   Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul]`.

THE PROBLEM: When the index `⟨0, ⋯⟩` is produced by `fin_cases j` (instead of `⟨0, by decide⟩`), `simp`
(both `simp` and `simp only [...]` with the full `cons_val`/`of_apply` set) makes NO PROGRESS — neither
`Matrix.sub_apply` nor `Matrix.mul_apply` fire on the LHS, and the RHS `vecCons (...) ⟨0,⋯⟩` does not reduce.
The `fin_cases`-generated index `⟨0, ⋯⟩` (with an opaque proof term `⋯`) seems to block the matrix-apply
simp lemmas from unifying, whereas an explicit `⟨0, by decide⟩` does not.

There is NO `OfNat (Fin (Wext M222 2)) 0` instance (the width is not a syntactic numeral), so I cannot
`rw [show (⟨0,⋯⟩ : Fin (Wext M222 2)) = (0 : Fin (Wext M222 2)) from rfl]`.

QUESTION: What is the cleanest, robust way to close these `fin_cases`-produced residual goals? Specifically:
(a) Is there a way to normalize the `fin_cases`-generated `⟨0, ⋯⟩` index so the matrix-apply lemmas fire
    (e.g. `Fin.mk_zero`, `Fin.mk_one`, a `Fin.cast_mk`, `Fin.eta`, or `show`-ing the index)?
(b) Should I avoid `fin_cases j` entirely and instead reduce the matrix equality differently (e.g. prove
    each row as a 1×width matrix equality, or use `Matrix.etaExpand`, or `funext` + `Fin.cases`)?
(c) Is `decide`/`Finset.decide` viable here (the entries are ℝ so no), or a `Matrix.ext_iff` + per-entry
    `Fin.cons`-aware closer?

The winning pattern used elsewhere in this file was: prove a clean product-form identity `prod0_eq` at
LITERAL `Fin` types, then `rw [hA, ← prod0_eq]` to put BOTH sides in the SAME form so `fin_cases <;> rfl`
fires. Could a similar "both-sides-same-form" trick work here, and what is the cleanest realization?

Give concrete Lean 4 tactic code.
