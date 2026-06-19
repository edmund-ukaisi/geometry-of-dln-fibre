# Thread 21 — route sizing: determinantal-KMS (a) vs orbit-stabiliser/Chevalley (b) [pen-and-paper, 2026-06-19]

## VERDICT: ROUTE (a) smooth-point assembly — smaller by a large factor. KMS determinantal sub-library AVOIDED.
Codex convergent.

### Decisive Mathlib facts (rg, v4.29)
- **Chevalley FIBRE-DIMENSION: ABSENT** (Mathlib's "Chevalley" = constructible image, not dim-of-fibres). No
  `dim source = dim target + dim fibre` in any form. Orbit-dimension package ABSENT. `ringKrullDim = trdeg` for
  f.g. domain/field ABSENT (so even the trdeg-additivity route to (b) is blocked). ⟹ route (b) = a from-scratch
  sub-library reusing NONE of the landed bedrock, AND still needs L6 (`dim Z_M = dim O_M`). Strictly dominated.
- Route (a) reuses all ~10 landed modules (L0, L4★ M1/M2/M3, L2a, L4d, OrbitVariety, OrbitLinearCodim, DeformationExt).

### KEY CORRECTION to thread 20 (the scope surprise was over-stated)
- **Determinantal PRIMENESS (KMS/Lakshmibai–Magyar) NOT needed.** Take `I = vanishingIdeal(Z_M)` directly —
  prime from `isPrime_vanishingIdeal_orbitSet` (O_M irreducible, LANDED) + `Z_M = Ō_M` (L6). The cotangent/regular
  chain runs on the reduced ring; never need "(minors) = vanishingIdeal".
- **L2b is non-circular** finite linear algebra at M: `ker(orbit-map differential dμ_M = δ⁰) = range δ⁰`
  (intrinsic). NOT via minor pderivs (that would re-import determinantal primeness — guard K2: use dμ_M=δ⁰).

### Assembly chain (all pieces have a home)
`varietyDim(Z_M) =[L4d] ringKrullDim(AtPrime m_M) =[M3 smooth⟹regular] finrank(cotangent) =[L2a, LANDED]
finrank(ker Jacobian) =[L2b: dμ_M=δ⁰] finrank(range δ⁰)`; then `codimRep =[L0] #σ − varietyDim = orbitLinearCodim`.

### Build sub-ladder (route a; ☑ landed / ☐ build) — ~8–10 modules, L6.2 the one sub-library piece
- L6.0 limit lemma ☑. L6.1 box-move degeneration via explicit 1-param family thru L6.0 ☐ module.
- **L6.2 rank-order `s≤r` ⟹ finite box-move chain (lace combinatorics, Abeasis–Del Fra) ☐ HARDEST (1–2 mod sub-library).**
- L6.3 easy direction (rank lower-semicontinuity, Ō_M ⊆ Z_M) ☐ module. L6.4 `vanishingIdeal(Z_M)=vanishingIdeal(O_M)`
  ideal-level ☐ module (reuses `vanishingIdeal_range_orbitMap_eq_ker`). L1 `(vanishingIdeal Z_M).IsPrime` ☐ short.
- L2b `ker(dμ_M)=range δ⁰` (dμ_M=δ⁰; reuse DeformationExt + rank-nullity) ☐ module.
- L3 `IsSmoothAt k m_M` homogeneity: L3.i Spec-detour smooth point ☐; L3.ii G-stable ☐; L3.iii transitivity ☑;
  L3.iv smooth pt ∈ open orbit ☐.
- L4-assembly (L4d+M3+L2a+L2b) ☐ module. L0-plug + L7 (discharge hVoigt) ☐ tide.

### Hardest + kill-conditions
1. L6.2 box-move generation (Abeasis–Del Fra; paper cites it). K1: if `s≤r ⟹ finite chain` doesn't reduce to a
   clean `diff`-induction, L6.2 inflates. De-risk: one box-move family + L6.0 on (2,2,2), then stress-test the induction.
2. L2b uniform `ker = range δ⁰`. K2: guard — go through `dμ_M=δ⁰`, NOT minor pderivs (else re-imports KMS primeness).
Codex artefacts: `threads/21-route-sizing/codex/route-sizing-{prompt,answer}.md`.
