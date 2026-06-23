<task>
Lean 4 + Mathlib v4.29. I am proving a SIGNED ring identity (all entries ℤ, no admissibility):

  Mval M T = codimForm L m,   where m = diffRank (cascadeRank M T) : ℤ → ℤ → ℤ

  codimForm L m = ∑ i ∈ Finset.Icc (1:ℤ) L, ∑ u ∈ Finset.Icc i (L:ℤ), ∑ j ∈ Finset.Icc u (L:ℤ),
                    ∑ v ∈ Finset.Icc j (L:ℤ),  m (i-1) (j-1) * m u v

  Mval M T = ∑ k : Fin L, (tPrev M T k - (T k : ℤ)) * ((M k.succ : ℤ) - (T k : ℤ))
    where tPrev M T k = M 0 (if k=0) else T (k-1).

I can prove these SUPPORT closed forms for m = diffRank (cascadeRank M T) (ρ = expSurvivor, ρ_0=M_0,
ρ_{s+1}=T_s; q_a = M_a - ρ_a, q_0 = 0; cascadeRank clamped to 0 outside [0,L]×[0,L]):
  - m a b = 0  unless (a = 0 ∧ 0 ≤ b < L)  [top row]  OR  (1 ≤ a ≤ L ∧ b = L)  [right col].
  - m 0 b = ρ_b - ρ_{b+1}   for 0 ≤ b ≤ L-1.
  - m a L = q_a - q_{a-1}   for 1 ≤ a ≤ L.
The collapse: factor1 m(i-1)(j-1) (j-1 ranges in [0,L-1], so never the right col) is nonzero only at i=1;
factor2 m(u)(v) (u≥1, never top row) is nonzero only at v=L. ⟹
  codimForm = ∑_{1≤u≤j≤L} (ρ_{j-1}-ρ_j)(q_u - q_{u-1})
            = ∑_{j=1}^L (ρ_{j-1}-ρ_j) · (∑_{u=1}^j (q_u - q_{u-1}))
            = ∑_{j=1}^L (ρ_{j-1}-ρ_j) · q_j        [inner telescopes, q_0=0]
            = Mval M T                              [reindex j=k+1].

The algebra is trivial; the PAIN is purely Finset.Icc bookkeeping over ℤ.
</task>

<output_contract>
Give a CONCRETE Lean 4 / Mathlib v4.29 tactic strategy, in this order:
1. The single cleanest way to reduce the quadruple sum to ∑_{1≤u≤j≤L}(ρ_{j-1}-ρ_j)(q_u-q_{u-1}):
   pick ONE of {nested Finset.sum_eq_single on i and v; rewrite-factors-to-zero + Finset.sum_eq_zero;
   one big Finset.sum_congr to a restricted summand}, and justify why it is least fragile given the
   TRIANGULAR Icc dependence (Icc i L, Icc u L, Icc j L all depend on the outer index). Name the exact
   Mathlib lemmas (Finset.sum_eq_single_of_mem signature, Finset.mem_Icc, etc.).
2. The j/v reordering: to do the v-sum first (isolate v=L) while the j-sum is Icc u L and v-sum is Icc j L,
   what is the v4.29 idiom? Is Finset.sum_sigma'/Finset.sum_comm' needed, or can sum_eq_single_of_mem on v
   (inside the j-sum, since v=L ∈ Icc j L always) avoid any swap? Prefer the no-swap route if it exists.
3. The inner telescope ∑_{u ∈ Icc 1 j} (q_u - q_{u-1}) = q_j - q_0: exact Mathlib v4.29 lemma
   (Finset.sum_Icc_id_mul_two is wrong; I want a telescoping-over-Icc lemma — Finset.sum_range_succ_sub_sum?
   Finset.sum_Ioc_consecutive? or prove via Finset.sum_range telescoping after shifting Icc 1 j to range j?).
4. The final ℤ-Icc → Fin L reindex ∑_{j ∈ Icc 1 L} f j = ∑_{k : Fin L} f (k+1): cleanest bridge
   (Finset.sum_bij / Finset.sum_nbij' / Finset.sum_range + Fin.sum_univ_eq_sum_range, with the ℤ↔ℕ↔Fin casts).

For each, give the lemma name and a one-line usage sketch. Flag any lemma you are NOT sure exists at the
v4.29 pin (I will verify with `rg` over .lake/packages/mathlib). Prefer the route with the FEWEST fragile
reindex steps even if it needs one extra support lemma.
</output_contract>

<grounding_rules>
You may not have the exact v4.29 lemma signatures memorized — explicitly mark each lemma name as
"confident" or "verify" so I know which to grep. Do not invent a lemma that bundles the whole collapse;
if the cleanest route is several standard steps, say so. Distinguish "this definitely works" from "this is
the shape, names may differ at the pin".
</grounding_rules>
