# Thread 20 — L2b tangent-identification design (pen-and-paper, 2026-06-19)

## VERDICT: L2b is NOT a bounded module — it pulls a SUB-LIBRARY (every non-circular route). ⚠ SCOPE SURPRISE.

### Circularity diagnosis CONFIRMED
- Forward `range δ⁰ ⊆ ker(jacobian)`: easy, unconditional (differentiate `g∘μ_M=0`, `g∈vanishingIdeal(O_M)=ker μ_M^*`
  [landed]; orbit-map differential at 1 is `δ⁰`). = the orbit-⊆-closure tangent inclusion.
- Reverse `ker(jacobian) ⊆ range δ⁰` via orbit-map/smoothness IS circular: `T_M O_M = range δ⁰ ⟺ dim O_M = r`
  (the goal); smoothness alone gives only `dim T_M Z_M = dim Z_M`, and `dim Z_M = dim O_M = r` is the unknown.
  No non-circular route through "open orbit + smoothness" without separately computing `dim O_M`. Codex converged.

### Both non-circular routes pull a sub-library
- **Determinantal (controller's primary):** L2a's hypothesis is `I = span(range g)`, so the minors must GENERATE
  `vanishingIdeal(Z_M)` as an ideal. Set-equality (Thm 3.8) + Nullstellensatz give only `radical(I_minors) =
  vanishingIdeal(Z_M)`; L2a needs `I_minors = vanishingIdeal(Z_M)` (radical/prime). That is the **equioriented
  type-A quiver determinantal-ideal primeness theorem (Lakshmibai–Magyar Thm 2.2 / Knutson–Miller–Shimozono)** —
  absent in Mathlib v4.29 (matrix minors/rank/Cotangent/Kähler present; NO quiver-determinantal prime/reduced/CM
  theory). **The ideal-level twin of L6** (the 2026-06-17 rankloc-probe flagged the same as non-CI). The Jacobian-
  kernel `ker J_M = range δ⁰` is uniform (not per-orbit) but its formalisation (differential of a sub-product +
  determinantal-stratum tangent + barcode/gauge count) is itself a local sub-library on top of the generation gate.
- **Orbit-stabiliser (Codex's cleanest):** `dim O_M = dim G − dim Stab = finrank C⁰ − finrank(ker δ⁰) =
  finrank(range δ⁰) = r` by rank-nullity (`finrank_range_add_finrank_ker` LANDED), then `dim Z_M = dim O_M`
  (orbit open dense in closure). Sidesteps L2a/L4★/L2b/IsSmoothAt entirely — cleanest on paper. BUT needs the
  affine-algebraic-group **orbit-dimension package** (dim orbit = dim G − dim stab; orbit locally closed; closure
  preserves dim) — absent in Mathlib (recon 01). "Cleaner on paper, not in Lean."

### Hardest step / the gate
`vanishingIdeal(Z_M) = (interval-subproduct minors)` as a prime/radical IDEAL — the Lakshmibai–Magyar/KMS theorem.
Gates the determinantal route entirely.

### L2b needs only finrank, not the subspace identity (minor simplification — does NOT avoid the sub-library).

### Recommended: SURFACE the scope surprise; pick the sub-library. (a) quiver-determinantal-ideal (Lakshmibai–
Magyar/KMS — SHARES cost with L6, reuses landed `vanishingIdeal(O_M)=ker μ_M^*` + L2a/L4★ → lower marginal cost)
vs (b) algebraic-group orbit-dimension (greenfield). De-risk (a): (2,2,2) Gröbner radical/prime check on thread-17's
6 generators. Codex artefacts: `codex/l2b-{prompt,answer}.md`.
