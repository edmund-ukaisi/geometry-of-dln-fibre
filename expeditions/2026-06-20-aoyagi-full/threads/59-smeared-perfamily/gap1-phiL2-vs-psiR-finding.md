# Gap #1 verify-first finding — `phiL2` vs the contract's `ψ∘R` (the load-bearing reconciliation)

**Date:** 2026-06-29. **Seat:** lean-formaliser (genm-smeared2). **Status:** VERIFIED (sympy, the
κ_bare-style verify-first the controller emphasized). NOT yet built in Lean — scoping for the next leg.

## The question

`routeMCore_box_diverges_on_smearedSubBox` (banked) needs the rate in the contract's form
`routeMCore M (ψ (R u)) = z²·U`, where `R` is the radial `pivotBlowupOn` (the sole Jacobian carrier,
`|det| = |u p|^{minAdm−1}`) and `ψ` the shear∘reshape. My banked `routeMCore_phiL2` is
`routeMCore M (phiL2 …) = z²·‖P₁·Hbar‖²` with `phiL2 = paramsEquivFlat ∘ chartL2Params` and the deepest
factor's top block `= z•Hbar` (Hbar a FREE `r×c` block). Codex flagged: `phiL2 = ψ∘R` is likely NOT
literally true.

## The finding (VERIFIED, sympy exact)

- **`phiL2` and `ψ∘R` AGREE on the rate, DIFFER on the chart map + Jacobian.**
- The contract's `R = pivotBlowupOn` sends the `r·c` deepest flat coords `(z, h₁,…,h_{rc−1}) ↦
  (z, z·h₁,…,z·h_{rc−1})`. Reshaped, the deepest factor's top block reads `z·H̄_unit` where
  `H̄_unit` is the angular block with the PIVOT entry fixed to `1` and the others `= hᵢ`.
- My `phiL2`'s deepest top is `z•Hbar` with `Hbar` a fully FREE `r×c` block (no pivot fixing, no radial
  blow-up — the `rc` entries are free coords, contributing `0` to the Jacobian).
- **Same rate:** `‖z·P₁·H̄_unit‖² = z²·‖P₁·H̄_unit‖²` (confirmed). So `routeMCore_phiL2`'s formula
  `z²·‖P₁·Hbar‖²` holds at `Hbar := H̄_unit`, matching the contract's `U = ‖P₁·H̄_unit‖²`.
- **Different Jacobian:** `phiL2` carries no radial det (Hbar free); the contract's `R` carries
  `|z|^{rc−1} = |z|^{minAdm−1}`. So `phiL2 ≠ ψ∘R` as maps — the gap is REAL.

## The consequence for the next leg (the path is clear, NOT a re-derivation)

The rate does NOT need re-deriving. The next-leg work is the CHART-MAP construction:

1. Define `R := pivotBlowupOn (deepestTopCoords) p` (the `r·c` top deepest coords radially blown), over
   opaque widths — generic `pivotBlowupOn` (banked det/injOn/fderiv).
2. Define `ψ := paramsEquivFlat ∘ pack ∘ shearM` (the reshape + the banked `measurePreserving_shearM`).
3. Show `(paramsEquivFlat M).symm (ψ (R u))` IS `chartL2Params … (Hbar := unit angular block read off
   R u)` — i.e. the composition decodes to the chart-params form with `Hbar = H̄_unit` (pivot=1).
   Then `routeMCore_phiL2` / `prod_chartL2Params` (banked) give the rate `z²·‖P₁·H̄_unit‖²` IMMEDIATELY.

So the banked `prod_chartL2Params` is the RIGHT reusable core — it takes the deepest-top `z•Hbar` for ANY
Hbar, so feeding `Hbar = H̄_unit` (the R-blown unit block) closes the rate side of the contract. The only
genuinely-new construction is the `ψ`/`R` flat maps + the decode `symm (ψ(R u)) = chartL2Params … H̄_unit`
(the pack231/shear231/R231 generalization to opaque widths).

## Recommendation

Build the `ψ`/`R` maps + the decode as the next sub-tide. The rate (`routeMCore_phiL2`), the divergence
(`smearedSubBox_weighted_diverges` / `hSdiv_of_peeled_rate`), and the headline interface
(`routeMCore_box_diverges_on_smearedSubBox`) are all banked — so once the decode lands, the L=2 headline
closes. Field A (containment) is the other remaining piece.
