<task>
Lean 4 / Mathlib v4.29 design review. Validate the proof design for a "frame fact" lemma; resolve one
reindex/permutation subtlety. I want the DIAGNOSIS + the precise lemma chain, NOT code.

SETUP (all in-repo, banked sorry-free):
- A : Matrix (Fin a) (Fin b) ℝ, the deepest last layer. A.rank = r. Tail rows vanish: A i j = 0 when (i:ℕ) ≥ r. (So r ≤ a, r ≤ b.)
- Q : Matrix (Fin b) (Fin b) ℝ, IsUnit Q, with A * Q = corM, corM i j = (if (i:ℕ)=(j:ℕ) ∧ (i:ℕ)<r then 1 else 0).
- KEYSTONE (banked): toBlocks22_isUnit_of_pivot_corner
    (VJ : Matrix (Fin r)(Fin r)) (VK : Matrix (Fin r)(Fin m)) (Q11 : Matrix (Fin r)(Fin r)) (Q12 : Matrix (Fin r)(Fin m))
    (Q21 : Matrix (Fin m)(Fin r)) (Q22 : Matrix (Fin m)(Fin m))
    (hVJ : IsUnit VJ) (hQ : IsUnit (fromBlocks Q11 Q12 Q21 Q22))
    (htop1 : VJ*Q11 + VK*Q21 = 1) (htop2 : VJ*Q12 + VK*Q22 = 0) : IsUnit Q22.   [here m = b - r]
- exists_pivot_cols_of_rank : (V : Matrix (Fin r)(Fin c) K) → V.rank = r → ∃ J : Fin r ↪ Fin c, IsUnit (V.submatrix id J).
- e := pivotThresholdSplit r b ha J : Fin b ≃ Fin r ⊕ Fin (b-r). Banked API:
    pivotThresholdSplit_symm_inl : e.symm (inl k) = (pivotSupport r b J).orderEmbOfFin _ k   (k-th SORTED pivot column)
    pivotThresholdSplit_symm_inr : e.symm (inr k) = (pivotSupportᶜ).orderEmbOfFin _ k          (k-th sorted complement)
    pivotThresholdSplit_symm_inl_mem_range : e.symm (inl k) ∈ Set.range J.
- Mathlib v4.29: isUnit_submatrix_equiv (A.submatrix e1 e2 unit ↔ A unit for e1 e2 equivs), submatrix_mul_equiv,
    reindex_apply (reindex e1 e2 M = M.submatrix e1.symm e2.symm), reindexAlgEquiv, Matrix.linearIndependent_cols_iff_isUnit.

GOAL: ∃ J, IsUnit ((Matrix.reindex e e Q).toBlocks₂₂)   [e = pivotThresholdSplit r b ha J].

PROPOSED DESIGN:
- V := A.submatrix (Fin.castLE (h:r≤a)) (id : Fin b → Fin b)   [top r rows of A]; claim V.rank = r.
- J from exists_pivot_cols_of_rank V.
- Set m := b - r. Define the keystone inputs from (reindex e e Q):
    Q11 := (reindex e e Q).toBlocks₁₁, Q12 := …₁₂, Q21 := …₂₁, Q22 := …₂₂.
    (reindex e e Q).toBlocksᵢⱼ entries are Q (e.symm (inl/inr i)) (e.symm (inl/inr j)).
  Define VJ := of (fun (i k : Fin r) => V i (e.symm (Sum.inl k))), VK := of (fun (i)(k:Fin m) => V i (e.symm (Sum.inr k))).
- Then IsUnit (fromBlocks Q11 Q12 Q21 Q22): it equals reindex e e Q (fromBlocks_toBlocks), IsUnit by isUnit_submatrix_equiv from IsUnit Q.
- htop1/htop2: from A*Q = corM restricted to the top r rows, reindexed columns by e.

QUESTIONS (resolve each, tersely):
1. VJ-unit subtlety. VJ's columns are V indexed by the SORTED pivots e.symm(inl k), but exists_pivot_cols gives IsUnit (V.submatrix id J) — J in J's OWN order. These differ by a permutation σ of Fin r. What is the cleanest bridge to IsUnit VJ? Is it: VJ = (V.submatrix id J).submatrix id σ for a permutation equiv σ : Fin r ≃ Fin r with J ∘ σ = (sorted pivots), then isUnit_submatrix_equiv? How do I GET σ as an Equiv (the sorted-pivot enumeration is an orderEmbOfFin of the SAME finset univ.map J, so there's a canonical Fin r ≃ Fin r identifying the two enumerations of pivotSupport)? Name the Mathlib construction (Finset.orderEmbOfFin / orderIsoOfFin, or build σ := (some equiv) explicitly). Or is there a SLICKER route avoiding σ entirely — e.g. choose J ALREADY sorted so e.symm(inl ·) = J definitionally?
2. htop1/htop2 derivation. With V = top r rows, V*Q = (A*Q).submatrix castLE id = corM.submatrix castLE id. I want VJ*Q11 + VK*Q21 = 1 (Fin r × Fin r). Claim: (V*Q) split by e on columns gives toBlocks; the LEFT block of (reindex_columns_only e of V*Q) = VJ*Q11+VK*Q21 (matrix mult distributes over the b = r ⊕ (b-r) column split). And (V*Q) top-left = (corM top r rows) left-block = I_r. Is the cleanest path: prove (reindex (Equiv.refl) e (V*Q)).toBlocks₁₁ = VJ*Q11 + VK*Q21 via a block-multiply identity (V columns split ⊕ Q rows split), then equate to (reindex refl e corM_topr).toBlocks₁₁ = I_r? What is the exact Mathlib block-mult lemma (Matrix.fromBlocks_multiply / submatrix split of mul over the middle index e)? The middle index b is split by e: V*Q = (V reindexed cols by e) * (Q reindexed rows by e) since e is an equiv — submatrix_mul_equiv on the shared index. Confirm the identity (V*Q).submatrix id e.symm decomposed = fromBlocks VJ VK _ _ * fromBlocks Q11 Q12 Q21 Q22 and read top-left.
3. V.rank = r: top r rows of A, with A's other rows zero. Is rank V = rank A clean? (A = V padded with zero rows = V.submatrix surjection? Actually A's rows ≥ r are zero, so A factors through its top block.) Cheapest Mathlib route to V.rank = r given A.rank = r and tail rows zero.
4. Overall: is this design SOUND and is there a materially shorter route I'm missing (e.g. defining the keystone inputs so htop1/htop2 are near-definitional)?
</task>

<output_contract>
Four numbered answers matching the questions, each ≤ 8 lines. For Q1 and Q2 give the exact Mathlib lemma
names (v4.29) and the order to apply them. End with a one-line VERDICT: design sound / design has a gap (name it).
No Lean code blocks longer than a single expression; name lemmas, don't write proofs.
</output_contract>

<grounding_rules>
Flag any lemma name you are not >80% sure exists in Mathlib v4.29 as "verify". Distinguish "this lemma exists"
from "a lemma of this shape should exist". If the permutation bridge (Q1) is genuinely fiddly, say so and give the
fallback (choose J sorted).
</grounding_rules>
