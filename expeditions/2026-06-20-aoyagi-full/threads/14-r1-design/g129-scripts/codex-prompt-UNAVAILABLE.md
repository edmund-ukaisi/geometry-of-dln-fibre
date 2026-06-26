<task>
Adjudicate, with exact algebra, whether a specific clean factorisation is reachable by a
measure-preserving change of variables, for a polynomial loss arising in a deep-linear-network
RLCT computation.

SETUP (the (3,3,3) "reduced node" after one blow-up):
- Â is a 3x3 real matrix with Â[0,0] = 1 a HARD constant (post-blow-up pivot), and 8 free real
  entries: Â = [[1,p,q],[r,s,t],[u,v,w]].
- A2 is a free 3x3 real matrix with 9 entries b0..b8 (row-major).
- The loss is the squared Frobenius norm of the matrix product:  F = ‖Â · A2‖²
  (a polynomial in the 17 real coordinates p,q,r,s,t,u,v,w, b0..b8).
- We work in the germ at the origin (all 17 coords = 0).

THE TWO COMPETING CLAIMS to reconcile:
(A) A prior matrix-level result: there exist unipotent (det=1) transvections L,R with
    L·Â·R = blockdiag[1, S],  S = D − b·a  (Schur complement), where D = lower-right 2x2 of Â,
    a = Â[0,1:], b = Â[1:,0]. This block-diagonalizes the MATRIX. The prior result claimed this
    gives a "clean decoupling" of the LOSS:  ‖Â A2‖² = [regular pivot-row terms] + ‖S·A2red‖²
    with S·A2red E-free (disjoint coords), A2red = rows 1,2 of A2.
(B) A separate result for a different (L2) chart found that the analogous "clean" coordinate
    factorisation F∘χ = u·(ΣEᵢ² + G²) (u a single bounded unit, G the E-free core) is NOT reachable
    by a measure-preserving change of variables — only a two-sided SQUEEZE c₁·Φ ≤ F ≤ c₂·Φ works.

QUESTION:
For the loss F = ‖Â A2‖² above, is the CLEAN factorisation  F∘χ = u·(ΣEᵢ² + G²)
(u a single bounded unit defined near 0, the Eᵢ regular coordinates, G an E-free "core")
reachable by a MEASURE-PRESERVING change of variables χ on the 17 loss coordinates?
If not the clean single-unit form, what IS the exact reachable form, and does it still give the
additive RLCT split rlct(F) = nReg/2 + rlct(core)?
</task>

<output_contract>
1. State whether the clean single-unit form F∘χ = u·(ΣEᵢ²+G²) is reachable by an MP c-o-v. YES/NO.
2. If NO, derive the exact reachable form by completing the square in the regular generators
   Eⱼ := (Â A2)[0,j] (j=0,1,2). Give the E-quadratic coefficient, whether there are E_iE_j cross
   terms, the shift β needed, and the resulting E-free remainder. State whether the remainder equals
   the Schur core ‖S·A2red‖² or differs.
3. State whether the matrix identity L·Â·A2 = blockdiag[1,S]·(R⁻¹A2) implies a VALUE identity for
   the loss ‖Â A2‖². Note L is unipotent but not orthogonal.
4. Conclude: for the per-node R1 chart, is the right obligation a clean MP-factor, or a two-sided
   squeeze (like L2), or a "weighted regular squares + core" form? Spell the exact form and whether
   the additive RLCT split survives.
</output_contract>

<grounding_rules>
- Exact algebra only for load-bearing claims. You may reason symbolically; do not rely on numerics
  for the value-identity / form questions.
- "Measure-preserving" = the change of variables has Jacobian determinant identically 1 (or a unit
  whose effect is a benign Jacobian-unit), defined and smooth near the origin.
- A "bounded unit" is a smooth function nonzero at the origin.
- Distinguish a MATRIX identity (entries rearranged) from a VALUE identity (Frobenius norm preserved).
- Be adversarial against BOTH claim (A) and claim (B). Do not assume either is correct.
</grounding_rules>
