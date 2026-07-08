# ≥-leg flatness kill-condition — certificate (`genm-dgeflat`)

**Seat:** pen-and-paper obstruction (exact-algebra + decorrelated Codex xhigh, red-team). **Date:** 2026-07-08.
**Verdict: FLAT — bounded CONFIRMED. Kill-condition NOT met** (no non-removable non-adjacent Morse coupling at
any stratum: r=1 or r=2, L=3 or L=4). **Charge the ≥-leg tide.** (Recorded by controller — dgeflat's worktree was
the contested `genm-r1frontcharge-wt`/`genm-hcfinish` dir under the #67 collision, so it could not write here.)

## What was tested
Not the corner-elimination bookkeeping — the LOAD-BEARING truth-value directly: the exact local structure of the
DLN loss `K = ‖A₀···A_{L-1} − B‖²` at an optimal point, on the slice {product's regular blocks pinned to B}. Whether
the residual core, after peeling the nReg regular squares, is flat along the off-pivot affine fibre (bounded) or
carries a non-removable degree-2 Morse coupling between non-adjacent layers (wall).

## The certificate
- **L=3, r=1, (2,2,2,2): FLAT.** On {P₀₀=1,P₀₁=0,P₁₀=0} the residual core is exactly `P₁₁ = ∏ₖ det(Aₖ) =
  ∏ₖ(pivotₖ·Sₖ)` (exact identity, L=3 and L=4) — a product of independent per-layer determinants, no cross-layer
  coupling. The flagged `Y₀Z₁`/`Y₁Z₂` non-adjacent degree-2 term is a product of two REGULAR coordinates (P₁₀,P₀₁
  linear parts) — swallowed by the regular squares.
- **L=3, r=2, (4,4,4,4), non-commuting gates: FLAT.** Full block-LDU (48 params). At the deepest point the Jacobian
  rank is 12: P₁₁,P₁₂,P₂₁ regular (via free pivots/Y₂/Z₀); P₂₂ the sole core block. Exact core `P₂₂ = S₀·W₁·S₂`
  (W₁=Z₁Y₁+S₁ = layer-1's own core) — clean per-layer triple product. The apparent gate coupling
  `P₁₁−I = Y₀Z₁+Y₁Z₂+Y₀W₁Z₂` lives in the REGULAR P₁₁ block (peeled with regular squares), NOT a core Morse term.
- **L=4, r=2: FLAT.** core = `S₀·(A₁A₂)₂₂·S₃` — recursion continues at width H−r (Aoyagi's structure), no stray
  coupling.
- **General identity (Codex, neutral red-team, conclusion withheld; dgeflat re-verified exact-rational, not
  rubber-stamped):** `S(A₀A₁A₂) = S₀·Q₁·S₁·Q₂·S₂` with gate factors `Qᵢ = (I+ZᵢY̅…)⁻¹` INVERTIBLE UNITS; base
  `S(D(P,S)·U(Y)·L(Z')·D(P',S')) = S·(I+Z'Y)⁻¹·S'` verified exact-rational (3 random cases). Off-pivot gates enter
  ONLY as units, absorbed by the coordinate change `Tₖ = Sₖ·unit` ⟹ residual = reduced-core product. No additive
  off-pivot quadratic outside the units.

## Why it can NEVER be a Morse coupling (structural — the decisive general argument)
`K = ‖resid‖²` with `resid = 0` at the optimum ⟹ by Gauss–Newton `Hess K = 2·JᵀJ` vanishes on `ker J`. So on the
fibre tangent the core is ALWAYS degree ≥3 — a product-type / reduced-DLN singularity, never a nondegenerate
degree-2 Morse form. There is nothing for a Morse-with-parameters split to bite on.

## Scope / caveats
- Geometry (loss local-structure) level: confirms the corner-elimination CoV is a clean SUBMERSION (off-pivot fibre
  flat), the route's load-bearing premise. The RLCT=½·codim lift stays Cited-Aoyagi (untouched).
- Gate-unit absorption is LOCAL, needs the common invertible r×r pivot across all L layers at v — holds at/near any
  optimal v (deepest: gates=I; unconditional existence banked via `exists_jacFlatL2_minor`/Cauchy–Binet). Mid-stratum
  r=2 (S₀,S₂-unit / W₁=0) checked: Jacobian full rank 16 → smooth/Morse, trivially flat.
- Watch (belt-and-suspenders, nothing outstanding): an optimal v where the interior gate `I+ZY` degenerates — but the
  local pivot choice precludes it in the neighborhood the RLCT reads.
- Scripts (exact-rational, reproducible): were left at `/tmp/dgeflat/*.py` (verify_detprod / r2_confirm /
  r2_midstratum / L4_flat / verify_codex) + `/tmp/dgeflat/codex/` (ephemeral).
