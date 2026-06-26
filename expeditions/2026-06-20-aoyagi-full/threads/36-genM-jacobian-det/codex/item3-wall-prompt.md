# Lean 4 / Mathlib — adjudicate an architectural wall in a factored-chart determinant proof

CONTEXT. I'm proving |det Dφ_flat| = ∏_j |u_j|^{leafH j} for a flat achiever chart
φ_flat : (Fin N → ℝ) → (Fin N → ℝ), φ_flat = paramsEquivFlat ∘ chartParamsFlat, where
chartParamsFlat = chartParamsGen ∘ genBlkFlat. The plan (route B+b1): build a FACTORED chart
`composeFold fs` (fs = list of conjugated ChartFactors: radial, per-boundary Schur, LDU, chain — each
acting on a block of Fin N and identity elsewhere, conjugated via a CLE E_s : (Fin N → ℝ) ≃L Block × Rest),
prove its det telescopes to the leafH monomial (DONE — item 2 + the det telescope skeleton are banked),
and prove the MAP EQUALITY `composeFold fs = φ_flat` (item 3) so the fderiv transfers.

THE BLOCKING FINDING (want confirmed/refuted). The det side is done. The map equality requires the
factor CLEs E_s to be the SPECIFIC chartIdxEquiv-based coordinate decoders (disjoint structured flat
slots, one Schur/LDU/chain block per boundary) so that composeFold reshapes EXACTLY to
chartParamsGen ∘ genBlkFlat. But the banked `genBlkFlat` reads its block data via an ARBITRARY MODULAR
HASH:  Bmat (k+1) i j := x ( (i*31 + j*7 + (k+1)*3) % N ),  Nblk k i j := x ((i*31+j*7+k*13+1) % N), etc.
This hash was deliberately chosen because the RATE identity routeMCore_phiGen is coordinate-AGNOSTIC
(the docstring states the specific coordinatization is "not load-bearing for the rate"). The blocks
even OVERLAP/wrap under %N. So:

CLAIM: `composeFold fs = φ_flat` is UNPROVABLE with the current genBlkFlat. To make item 3 work,
genBlkFlat must be REDEFINED to decode blocks via the chartIdxEquiv coordinatization (disjoint slots,
one summand per role), and the factor CLEs built from the same coordinatization, with the boundary
index alignment I derived: the Schur frame at boundary s (size (t_s+r_s)(t_s+c_s) = t_{s-1}·M_s)
aligns with schurDim (s-1) [= t_{s-1}·M_s], NOT schurDim s. Then re-establish that the rate STILL
transfers under the new (structured) genBlkFlat — which should be free since the rate is coord-agnostic
(routeMCore_phiGen only needs the C-0=identity-boundary condition hC0, not the specific decoder).

QUESTIONS:
1. Is the CLAIM correct — is the arbitrary modular genBlkFlat fundamentally incompatible with a
   factored-chart map equality, forcing a genBlkFlat REDEFINITION (not just a tactical s-induction)?
2. Is the redefinition the right move, or is there a way to prove `composeFold fs = φ_flat` by choosing
   fs's CLEs to MATCH the modular hash (i.e. absorb the hash into the E_s)? (My read: the hash's %N
   wrapping makes the blocks non-disjoint, so no honest block-extraction CLE can match it — the E_s
   must be genuine linear ISOs, and a wrapping hash isn't injective-on-blocks. Confirm.)
3. Given a REDEFINED structured genBlkFlat, is the boundary index alignment schurDim(s-1)↔frame(s)
   the correct one, and does the rate-transfer survive unchanged (only hC0 needs re-checking)?
4. Scope estimate: is the redefinition + re-proving rate-transfer + building the chartIdxEquiv CLEs +
   the entry-wise map match a multi-pass effort, or is there a shortcut I'm missing?

Be concrete and skeptical. If the CLAIM is wrong, say exactly how composeFold = φ_flat could be proven
with the modular genBlkFlat.
