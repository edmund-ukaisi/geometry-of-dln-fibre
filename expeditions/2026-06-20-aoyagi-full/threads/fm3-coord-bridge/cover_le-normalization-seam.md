# cover_le normalization seam — unit-factor + signed-box (fm3, for the routeM_cover_le grind)

The one real interface seam between my landed leaf CoV and crux2's IsRouteMCover.cover_le RHS.
Confirmed against the banked Case222 precedent (crux2 asked me to check the shape constraint).

## The mismatch
- crux2's cover_le RHS: Σ_i ∫⁻_{unitBox (d i) = [0,1]^d} ENNReal.ofReal (monomialIntegrand (d i)(k i)(h i) c' y)  [BARE monomial, [0,1]^d]
- my landed leaf CoV (per leaf): ∫⁻_{chartDomOn = [−1,1]^d} ENNReal.ofReal (monomialIntegrand · |unit_i|^{−c'})  [monomial × UNIT, signed box]

Two constant-factor inflations between them:
1. UNIT FACTOR unit_i^{−c'} (unit_i ≥ a_i > 0, two-sided bounded): ≤ a_i^{−c'}, a constant. Reduce
   monomial·unit^{−c'} → bare monomial via the BANKED `integrableOn_monomial_mul_unit_iff`
   (Case222Cover; needs 0 < a ≤ |unit| ≤ B). Case222's Eleaf_integrable is the precedent.
2. SIGNED BOX [−1,1]^d vs [0,1]^d = unitBox: 2^d-orthant factor. Bridge via the BANKED
   `integrableOn_Icc_symm_of_even` (Case222CoverGE; even-reflection [0,1]→[−1,1]).

## Resolution (pending crux2's a/b/c choice; I lean c)
(c) I land crux2's EXACT RHS (bare monomial, unitBox) on MY side, absorbing the a_i^{−c'}·2^d
constants in the ≤, using the two banked precedent lemmas. Keeps crux2's bridge unchanged. Requires
cover_le's ≤ to be the loose finiteness-transfer ≤ (not a tight equality) — confirm with crux2.
The constants do NOT move monomialThreshold (the ⨅ value), so the bridge's value-extraction is safe.

## Why this matters for the grind
routeM_cover_le's proof = the g5_pivotNode/recStep cover SPLIT (∫_U = Σ_leaves ∫_{chart preimage})
+ per-chart CoV (node_loss_pivot_factor pullback + node_jacobian_det) landing ∫_{[−1,1]^d} monomial·unit
+ THIS normalization (→ bare monomial/[0,1]^d). The normalization is the LAST step before the RHS
matches crux2's cover_le. Banked precedent for both halves; the grind is generalizing Case222CoverGETail's
recStep assembly + threading the per-leaf normalization.
