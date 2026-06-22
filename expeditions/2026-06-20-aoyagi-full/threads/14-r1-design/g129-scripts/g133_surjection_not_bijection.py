# CRITICAL FIDELITY: is it a BIJECTION (paths ↔ strata) or a SURJECTION (paths ↠ strata, many paths
# per stratum)? The g3 memo: (2,2,2) had 24 LEAVES but only 3 admissible strata. So paths OUTNUMBER
# strata — the map paths → strata is SURJECTIVE (every stratum hit) but NOT injective (a stratum is hit
# by several charts: pivot-coordinate choice + affine-minor choice multiply the leaf count).
#
# WHY surjectivity (not bijectivity) is the RIGHT obligation for resolution_charts:
#   rlctAtOn(core) 0 = ⨅_{paths i} monomialThreshold(d_i,k_i,h_i)        [S1.1 min-over-cover]
# The ⨅ is over PATHS (leaves of the chart tree), NOT over strata. For the ⨅ to equal ½·min_t Mval:
#   (≤, no-undershoot)  every path's threshold ≥ ½·min_t Mval        [k_E=1 ⟹ ratio=codim/2 ≥ ½·min]
#   (≥, no over-estimate / EXHAUSTIVE) some path's threshold = ½·min_t Mval, AND every stratum is
#       represented so no SMALLER-codim direction is missed.
# The exhaustiveness obligation is: the map (path ↦ the rank-stratum it resolves) is SURJECTIVE onto
# Adm M, AND each path's min-codim-along-its-centers = Mval(stratum). Then:
#   ⨅_paths threshold = ⨅_paths ½·(min codim along path) = ½·(min over strata Mval) = ½·min_t Mval. ✓
# Surjectivity guarantees the MIN stratum is hit (no missed branch ⟹ ⨅ not too big); the per-path
# codim-match + k_E=1 guarantees no path undershoots (⨅ not too small). BIJECTION is NOT needed (extra
# paths hitting the same stratum give the SAME threshold — they don't change the ⨅).
print("FIDELITY: the obligation is a SURJECTION paths ↠ Adm M (+ codim-match), NOT a bijection.")
print("  (2,2,2): 24 leaves ↠ 3 strata — many charts per stratum; the ⨅ only needs every stratum HIT.)")
print("""
The precise obligation (3 conjuncts):
  (S) SURJECTIVITY:   ∀ T ∈ Adm M, ∃ path π in the chart tree with stratum(π) = T.
                      [every admissible rank stratum is reached by some root-to-leaf path]
  (C) CODIM-MATCH:    ∀ path π, minCodim(π) = Mval M (stratum(π))   [path's binding divisor = stratum codim]
                      AND every exceptional divisor on π has k_E = 1 (multiplicity-1, via multilinearity).
  (V) VALUE:          hence ⨅_paths monomialThreshold = (½ : ℝ≥0∞)·(min_{T∈Adm M} Mval M T)
                            = ofReal (lambdaCore M).     [the resolution_charts RHS]
Conjuncts (S)+(C) ⟹ (V); (S) is the genuine 'no missed branch' exhaustiveness, (C)'s k_E=1 is the
'no undershoot'. BIJECTIVITY is a red herring (multiplicity in the cover is harmless for a ⨅).
""")
