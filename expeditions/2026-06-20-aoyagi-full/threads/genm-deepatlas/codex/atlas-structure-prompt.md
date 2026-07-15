<task>
Lean 4 + Mathlib (v4.29) formalisation DESIGN question — lock the cleanest route before I sink a
large dependent-width build. Argue whichever way; if a route is a trap, say so.

CONTEXT. Deep linear network. `prod H A : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ` = the layer
product A⁽¹⁾…A⁽ᴸ⁾ (left fold), `H : Fin (L+1) → ℕ`, `A : Params H = ∀ s : Fin L, Matrix (Fin (H
s.castSucc)) (Fin (H s.succ)) ℝ`. Banked: `prodAux_succ` peels the last layer
(`prod (k+1) = prodAux k * reindex(A_k)`). Goal (Tide B of a stratified-resolution atlas): build the
finite unit-Jacobian-chart atlas of `{A | (prod H A).rank = s}` + a null-overlap gluing wiring
(per-cell integral-finiteness left as a HYPOTHESIS for a later tide). Charts must stay UNIT-JACOBIAN
(no radialization) — the Jacobian weight is ≡1 in these coords.

BANKED PIECES (verified, sorry-free), all over ℝ:
- (tide A, TOP-LEFT pivot only) `deepReduce_skeleton (Δ)(U)(V)(hΔ:IsUnit Δ.det) : fromBlocks Δ U V (V*Δ⁻¹*U) = fromRows Δ V * Δ⁻¹ * fromCols Δ U` (CUR at a top-left pivot);
  `deepReduce_rank (X)(Δ)(U)(V)(hΔ) : (X * fromBlocks Δ U V (V*Δ⁻¹*U)).rank = (X * fromRows Δ V * Δ⁻¹).rank`.
- `rank_mul_eq_of_mul_eq_one (X)(D)(D')(h:D*D'=1) : (X*D).rank = X.rank` (arbitrary Fintype index).
- (base brick) `rankEqLocus_eq_iUnion_pivot_inter (r) : {M | M.rank = r} = ⋃ (ρ:Fin r↪Fin m)(κ:Fin r↪Fin n), ({M | IsUnit (M.submatrix ρ κ)} ∩ {M | M.rank ≤ r})`.
- `pivotLocus_eq_iUnion`, `exists_nonsingular_submatrix_of_le_rank`, `isUnit_submatrix_le_rank`.
- gluing consumer `lintegral_lt_top_of_finite_cover {ι}[Fintype ι](C:ι→Set α)(D)(f)(hcover:μ(D\⋃ C)=0)(hfin:∀ i, ∫⁻ C_i f<⊤):∫⁻_D f<⊤`.

THE LOAD-BEARING BRIDGE I need (the "pivot-reindexing cost"): lift `deepReduce_rank` from a TOP-LEFT
pivot to a GENERAL pivot `(ρ : Fin r ↪ Fin m, κ : Fin r ↪ Fin n)`. Target shape (the general-pivot
CUR skeleton / rank reduction):
  `M.rank = r → IsUnit (M.submatrix ρ κ) →`
  `(X * M).rank = (X * (M.submatrix id κ) * (M.submatrix ρ κ)⁻¹).rank`
i.e. rank(X·M) = rank(X · [pivot columns of M] · [pivot minor]⁻¹) — reduce to r columns.
I have a pen-and-paper proof via a rank factorization M = P·Q (P: m×r full col rank, Q: r×n full row
rank), with P[ρ,:], Q[:,κ] invertible, giving M = C·U⁻¹·R.

ROUTES I'm weighing for the general-pivot bridge:
 (A) permute rows/cols so the pivot is top-left (an equiv σ,τ with σ∘(first r)=ρ etc.), rewrite M as
     `M.submatrix σ τ = fromBlocks Δ U V W` with W = VΔ⁻¹U (since rank=r ⟹ Schur E=0), apply the banked
     top-left `deepReduce_rank`, un-permute via `Matrix.rank_reindex`/`rank_submatrix_equiv`.
 (B) prove the general-pivot CUR skeleton `M = (M.submatrix id κ) * (M.submatrix ρ κ)⁻¹ * (M.submatrix ρ id)`
     directly from a rank factorization M = P·Q, then rank(X·M)=rank(X·C·U⁻¹) via the right-inverse of R.
 (C) something else / a Mathlib lemma I'm missing.
</task>

<output_contract>
1. ROUTE VERDICT. Rank (A)/(B)/(C) for the general-pivot bridge by (reachability × low-thrash-risk).
   Pick ONE. Give its ordered sub-lemma list with one-line Lean-ish signatures, marking banked vs new,
   and FLAG the single hardest sub-lemma.
2. MATHLIB CHECK. Does v4.29 have: (i) a rank factorization `M.rank = r → ∃ P Q, M = P*Q ∧ …` (name?);
   (ii) `Matrix.rank_reindex` / `rank_submatrix_equiv` / rank invariance under an equiv reindex (name?);
   (iii) `(A*B)⁻¹ = B⁻¹*A⁻¹` for square invertible / `Matrix.mul_inv_rev` (name?). Mark each
   VERIFIED-name / UNVERIFIED-guess / ABSENT.
3. EFFECTIVE-STATE RECURSION. The cleanest way to run the chain induction that AVOIDS constructing a
   reduced `Params` tuple: carry a state `(j, q, Q : Matrix (Fin (H j)) (Fin q), hQ : Q.rank = q)`
   representing `prodAux j * Q`, descend j→j−1 by the general-pivot bridge on the effective last layer
   `M := reindex(A_{j-1}) * Q`. Confirm this closes (`prod = state at j=L, Q=1`; terminate at j=0), give
   the descent lemma signature, and say whether a flat `Fintype` cell-index is needed for the gluing or
   nested per-level unions suffice.
3. CHEAPEST FIRST GREEN. The single smallest genuine theorem to land first as a green checkpoint
   (I report incrementally). Rough LoC band for it and for the whole Tide B.
</output_contract>

<grounding_rules>
Flag inference vs fact. Mark any Mathlib lemma name UNVERIFIED unless you're sure it exists at v4.29.
Prefer a route that maximally reuses the banked top-left `deepReduce_rank`. Distinguish "mathematically
right" from "cheaply reachable in Lean now". If route (A)'s permutation bookkeeping is the classic
Lean time-sink, say so and prefer (B).
</grounding_rules>
