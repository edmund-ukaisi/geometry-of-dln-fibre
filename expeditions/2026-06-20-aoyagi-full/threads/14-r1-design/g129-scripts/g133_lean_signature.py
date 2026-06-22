# Draft the Lean-grade obligation SIGNATURE (the statement, not the proof). Two layers:
#   (I) the chart tree as data: ι (paths) + per-path (d,k,h) — already resolution_charts' existential.
#   (II) the SURJECTION + CODIM-MATCH connecting ι to Adm M + Mval, the consumable lemma.
# Express the obligation as a lemma resolution_charts can apply, given the chart-tree data.
print(r"""
=== The Lean-grade R1.6 obligation (statement only) ===

Inputs (the chart-tree data, an instance of resolution_charts' existential witness):
  M : Fin (L+1) → ℕ
  ι : Type, [Fintype ι]                       -- the root-to-leaf PATHS of the pivot tree
  d : ι → ℕ                                   -- per-path chart dimension
  k h : (i:ι) → Fin (d i) → ℕ                 -- per-path monomial exponents (k_E = vanishing, h = Jacobian)
  stratum : ι → (Fin L → ℕ)                   -- the rank stratum each path resolves (its branch tuple)

THE OBLIGATION (a Prop bundling the three conjuncts):

  structure IsResolutionAtlas (M : Fin (L+1) → ℕ)
      (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ)
      (stratum : ι → (Fin L → ℕ)) : Prop where
    -- (S) SURJECTIVITY onto the admissible cone (the 'no missed branch' = EXHAUSTIVENESS):
    strata_admissible : ∀ i, stratum i ∈ Adm M
    strata_surjective : ∀ T ∈ Adm M, ∃ i, stratum i = T
    -- (C) per-path CODIM-MATCH + multiplicity-1 (the 'no undershoot'):
    mult_one        : ∀ i (j : Fin (d i)), k i j = 1            -- k_E = 1 (regular sequence, via multilinearity)
    codim_match     : ∀ i, (⨅ j : Fin (d i), axisRatio (h i j) (k i j))
                              = (1 / 2 : ℝ≥0∞) * (Mval M (stratum i)).toNat
                          -- the path's monomial threshold = ½·(its stratum's codim)
                          -- [each binding divisor on path i has ratio (h+1)/(2·1) summing to ½·Mval]

  -- THE CONSEQUENCE resolution_charts consumes (proved FROM the structure + monomial_rlct S2):
  theorem resolution_value_of_atlas
      (M) (ι) [Fintype ι] (d k h stratum)
      (hatlas : IsResolutionAtlas M ι d k h stratum) :
      (⨅ i : ι, monomialThreshold (d i) (k i) (h i))
        = ENNReal.ofReal (lambdaCore M) := by
    -- ⨅_i monomialThreshold = ⨅_i ⨅_j axisRatio          [monomial_rlct.1, S2]
    --                      = ⨅_i ½·Mval(stratum i)        [codim_match]
    --                      = ½·⨅_{T∈Adm M} Mval M T        [strata_surjective ⟹ the image of stratum = Adm M]
    --                      = ofReal (lambdaCore M)          [lambdaCore = ½·(Adm M).inf' Mval]
    sorry  -- STATEMENT ONLY; the proof is pure ⨅-rearrangement once the structure holds

NOTES on each conjunct's status:
  strata_admissible : structural (recursion pivots only on {∏C=0}) — Codex fact 2; cheap once stated.
  strata_surjective : THE residual real work (every admissible stratum reached) — the combinatorial core.
  mult_one          : #132 multilinearity argument (F = x²·reduced) — exact-algebra certified.
  codim_match       : #131 (Schur S=D-ba, codim S(t)=Mval(t)) + R1.2 divisor-ratio (regular seq) — certified-ish.
""")
