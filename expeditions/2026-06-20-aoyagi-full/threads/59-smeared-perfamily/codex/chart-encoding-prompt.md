<task>
Lean 4 + Mathlib. I am building the L=2 BOUNDARY-SMEARED chart for deep linear networks, the last
piece of a rate F=z²·U. I have BANKED (axiom-clean) the abstract rate chain; the ONLY remaining gap is
the CHART-EVAL: prove `prod M (chartParams u) = z • (P₁ · H̄)` over OPAQUE widths.

SETUP (L=2): Params M = (A⁰ : Matrix (Fin (M 0)) (Fin (M 1)) ℝ, A¹ : Matrix (Fin (M 1)) (Fin (M 2)) ℝ).
prod M A = A⁰ · A¹  (decoded entrywise by the BANKED `prod_two_layer221 : prod M A i j = ∑ k1 : Fin(M 1),
A 0 i k1 * A 1 k1 j`). The smeared chart: M 1 = r + s (r = deepRank, s = smear), and the deepest factor
A¹'s TOP r rows are `z·H̄ − Λ₀·S_bot` (H̄ : Matrix (Fin r)(Fin(M 2)), Λ₀ : Matrix (Fin r)(Fin s),
S_bot : Matrix (Fin s)(Fin(M 2))), BOTTOM s rows are `S_bot`. P₁ = A⁰[:,:r], P₂ = A⁰[:,r:].
The telescope (BANKED): A⁰·A¹ = P₁(z·H̄ − Λ₀ S_bot) + P₂ S_bot = z·(P₁ H̄) given P₁·Λ₀ = P₂.

The OBSTACLE is the OPAQUE-WIDTH row-split of A¹ (rows Fin (M 1) = Fin r ⊕ Fin s) — the dependent-Fin
cast trap. I have a BANKED abstract lemma `smeared_rate_of_cancel` that works on ABSTRACT block matrices
P₁,P₂,H̄,S_bot,Λ₀ (no Fin (M ·)), and `prod_two_layer221` that gives the entrywise sum over Fin (M 1).

<output_contract>
1. The CHEAPEST encoding of A¹'s row-split over opaque Fin (M 1) = Fin (r+s). RANK these 3 options by
   cast-pain, ONE LINE each + the single key Mathlib lemma each needs:
   (a) A¹ := (Matrix.fromBlocks (z·H̄ − Λ₀ S_bot) ... S_bot ...) reindexed by `finSumFinEquiv : Fin r ⊕
       Fin s ≃ Fin (r+s)` then `finCongr (hrs : r+s = M 1)`;
   (b) A¹ k j := define via `Fin.addCases`/`Sum.elim` on `(finCongr hrs.symm).symm`-split of k;
   (c) keep A¹ ABSTRACT as a hypothesis `A¹ = <reindexed block>` and prove the prod-collapse by reindexing
       the SUM `∑ k1 : Fin(M 1)` to `∑ over Fin r ⊕ Fin s` via `Fintype.sum_equiv`/`Equiv.sum_comp`, so
       the cast lives in ONE sum-reindex step, not in A¹'s definition.
2. For the winner: the EXACT statement of the one prod-collapse lemma (chartParams-free, taking A⁰, the
   block data, hrs : r+s=M 1, and P₁Λ₀=P₂ as hyps) that yields `prod M A i j = z·(P₁·H̄) i j` per-entry.
3. The single TRAP in the sum-reindex (e.g. `finSumFinEquiv` direction, `Fin.sum_univ_sum`/`Finset.sum_sum_elim`).
</output_contract>

<grounding_rules>
Flag inference vs fact. You don't have my files. If a Mathlib lemma name is uncertain, say "verify name".
Prefer the option that minimises dependent-Fin casts even if more verbose.
</grounding_rules>
