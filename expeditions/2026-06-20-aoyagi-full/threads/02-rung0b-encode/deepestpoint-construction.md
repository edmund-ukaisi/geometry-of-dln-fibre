# deepestPoint_exists — verified construction (ready to formalise once `hr` lands)

`deepestPoint_exists` is FALSE as frozen (`hB : B.rank = r` alone): counterexample `H=(3,1,3), r=2,
B=diag(1,1,0)` — `B.rank=2` but the fibre is empty (product through width-1 middle has rank ≤ 1).
Controller adding `hr : ∀ s, r ≤ H s` (task #18). With `hr`, the construction below works (numpy-verified
for `(3,3,3)/r2, (2,2,2)/r1, (4,1,4)/r1, (5,3,4,3)/r2, (2,2,2,2)/r0` — prod = B, every layer rank = r).

## Construction (consumes L1 `block_elimination`)

Rank factorization `B = U·V`, `U : Fin(H 0) × Fin r`, `V : Fin r × Fin(H last)`, both rank `r`
(from `block_elimination`: `B = P⁻¹ · diag(E_r,0) · Q⁻¹`, split `diag(E_r,0) = [E_r;0]·[E_r|0]`, so
`U = P⁻¹·[E_r;0]`, `V = [E_r|0]·Q⁻¹`). Layers:
- `w 0 : H 0 × H 1` = `U` in the first `r` columns, `0` elsewhere. rank `r` (needs `r ≤ H 1` ✓ hr).
- `w s` (`0 < s < L-1`), `H s × H (s+1)` = `[[I_r,0],[0,0]]` (rank `r`; needs `r ≤ H s, H (s+1)` ✓ hr).
- `w (L-1) : H (L-1) × H L` = `V` in the first `r` rows, `0` elsewhere. rank `r` (needs `r ≤ H (L-1)` ✓).

(L=1 single layer: `w 0 = B` directly, rank `r`. r=0: all-zero tuple, the origin.)

Product telescopes: the middle `[[I_r,0],[0,0]]` blocks act as the rank-`r` identity on the first `r`
coords, so `prod w = (U padded)·(I_r blocks)·(V padded) = U·V = B`. Each layer rank exactly `r`.

## Lean formalisation plan (~150 lines, once statement frozen with hr)
1. From `block_elimination H r B hB`: get `P,Q` units with `P·B·Q = diag(E_r,0)`.
2. `U := P⁻¹ · embed_cols`, `V := embed_rows · Q⁻¹` (the rank factorization); `B = U·V` by assoc.
3. Define layer matrices via `Matrix.of` with the block patterns above; each `rank = r` (rank of a
   block-`I_r` matrix; use `r ≤ H s` from hr for the embedding to be valid).
4. `prod w = B`: unfold `prodAux`, telescope the `I_r` middle blocks (matrix-mul of the block forms).
5. `IsDeepLayers`: `prod w = B` (in optimalSet) ∧ `∀ s, (w s).rank = r`.
6. r=0 special-case: all-zero tuple (cleaner; `(0).rank = 0`, `prod 0 = 0 = B` since `B.rank=0 ⟹ B=0`).

The telescoping (step 4) is the fiddly part (dependent Fin dims, like `prod` itself). The rank-of-block
facts (step 3) reuse the L1 `LinearMap`/basis machinery or a direct `Matrix.rank` of a block-identity.

## SECOND bug found (2026-06-20, before proving): L=0 corner — needs `1 ≤ L`
Even WITH `hr`, `deepestPoint_exists` (and the headline) are FALSE for `L=0` (zero layers): `prod` is
the empty product `= (1 : identity)` by `rfl`, so the fibre is nonempty only if `B = I` (rank `H 0`);
`L=0, H=![2], r=0` gives `hr` ✓ but `prod ≡ I₂ ≠ 0 = B`, empty fibre. Fix: add `(hL : 1 ≤ L)`.
EXHAUSTIVELY verified `1 ≤ L ∧ hr` SUFFICES (484/484, L∈{1,2,3}). Reported to controller; HELD pending.

## Confirmed reusable sub-lemma (form-independent): `rank = 0 ⟹ B = 0`
```lean
example {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℝ) (hB : B.rank = 0) : B = 0 := by
  have hr0 : LinearMap.range B.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero (R := ℝ)]; exact hB
  rw [LinearMap.range_eq_bot] at hr0
  ext i j
  have := LinearMap.congr_fun hr0 (Pi.single j 1)
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using congrFun this i
```
This closes the `r=0` case (all-zero tuple witness, once `1 ≤ L` lands so a layer exists to be zero).
