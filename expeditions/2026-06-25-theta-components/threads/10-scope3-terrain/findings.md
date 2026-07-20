# Thread 10 — scope-3 terrain map (bundle + smoothness, LR Lemma 4.6 B) — certificate

**Persisted by the controller** (scout recon, read-only + decorrelated Codex xhigh). Codex artifacts:
`threads/10-scope3-terrain/codex/product-iso-{prompt,answer}.md`.

## HEADLINE — scope-3 splits into TWO tractable deliverables + ONE separable months-scale wall

The framing "climb the reducedness wall to get the bundle + smoothness" is wrong: **the bundle and
smoothness deliverables do NOT require the strict scheme-theoretic reducedness wall.** Separate the
**reduced fibre variety** (tractable, the chart `e_β` already lives there) from the **scheme cut**
`FibreAlg = k[Rep]/fibreGenIdeal` (the wall).

## PART 1 — the reducedness wall (`fibreGenIdeal d B` radical) — MONTHS-SCALE, SEPARABLE
- Target ⟺ `IsReduced (FibreAlg)` ⟺ `fibreGenIdeal = vanishingIdeal(fibre)` (the radical-collapse).
  Math certified TRUE (codim thread 16 + Singular ~11 cases + Codex).
- **Half-dismantled in Lean:** `Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`
  (radical GIVEN the product iso `e : Sred ≃ₐ SchurLoc ⊗ FibreAlg` + `IsReduced S`); `isReduced_of_tensor`,
  `DeepChartRing.isReduced_Sred`, the `SchurLoc`-algebra structure, `EndpointNormalization.gaugeEquiv` all
  built sorry-free. **The one open rung IS the wall:** the product iso `e` is logically the radical-collapse
  (upgrade radical-containment `sigmaIdeal ≤ √ker` to kernel-containment — the nilpotent-killing map
  injective). **Codex verdict: 8–12+ modules, genuinely fresh AG, MONTHS-SCALE; no Mathlib support**
  (determinantal-ideal radicality / Buch–Fulton / Kinser–Rajchgot not in Mathlib). Matches the codim
  expedition's "≥2-module from-scratch AG" judgment, more honestly costed.
- **Decision: surface to the operator as a STANDALONE strategic decision, NOT a tide.** The deliverables
  below don't need it.

## PART 2 — the local-trivial bundle — Tier-R TRACTABLE (~4–6 modules), no wall
The chart `e_β = chartLocalizedAlgEquiv` (`Away chartDsig ≃ₐ[k] Away chartGfib`) is BUILT and lives on the
**reduced** variety (`chartGfib` over `sweepFibreRing = k[Rep]/vanishingIdeal(F)`, not `FibreAlg`). Honest
minimal statement = a finite family of chart `AlgEquiv`s + the `{detΔ≠0}` open cover of `Mat^{=r}` +
transitions. Name it `reducedFibre_locallyTrivial_…` (reduced variety, not the scheme cut).
| rung | content | size |
|---|---|---|
| B1 | tensor-package `Away chartGfib ≃ SchurLoc ⊗_k sweepFibreRing` (`algebraTensorAlgEquiv`/`scalarRTensorAlgEquiv` + localization base-change) | 1–2 |
| B2 | compose with `e_β` ⟹ per-chart product | small |
| B3 | `{detΔ≠0}` open cover of `Mat^{=r}` + finite-family bundle statement | 2–3 |
| B4 | transition/no-drop wiring (reuse `Core.SourceNoDrop`, `Core.FibreNormalForm` — `exists_baseChange_of_rank_eq` = bundle-base homogeneity) | wiring |

## PART 3 — smoothness (smooth locus) — S-submersive route AVOIDS the wall, gated on S1
Global smoothness FALSE (fibre singular at the deepest stratum); honest statement = smooth away from it.
- **Do NOT use the `OrbitSmooth`/`dense_smoothLocus_of_perfectField` route** — it requires `[IsReduced X]`
  (`Smooth.lean:363`), so it inherits the Part-1 wall.
- **S-submersive (the lever):** a direct local Jacobian/submersive argument on the SCHEME cut, no global
  reducedness. Mathlib: `Algebra.PreSubmersivePresentation.naive` + `SubmersivePresentation` ⟹
  `IsStandardSmoothOfRelativeDimension` ⟹ `IsSmooth`. **KILL-CONDITION: read `SubmersivePresentation`'s exact
  hypotheses before committing — if they secretly force a reducedness side-condition, smoothness re-collapses
  onto the wall.**
| rung | content | size | seat |
|---|---|---|---|
| **S1** | a `(C+δ)×(C+δ)` minor of `fibreJacobianMatrix` is a unit on the generic stratum (the H3b "rank = C+δ" never completed — codim went via Krull dim, not the Jacobian) | hard | **pen-and-paper (witness)** |
| S2 | package `naive` + the selected minor as a `SubmersivePresentation` on `{minor≠0}` | 2–3 | formaliser |
| S3 | `SubmersivePresentation … ⟹ IsSmooth` | 1 | formaliser |
| S4 | identify the complement (deepest stratum) as the singular locus | 1–2 | formaliser |
`Core.FibreJacobian` has the Jacobian + `finrank(ker)+rank=card` but LACKS `rank = C+δ`. No Mathlib
`regular ⟹ smooth` (smoothness must be produced via the presentation, not derived).

## SEQUENCING (revises the brief's "wall first")
1. **Tier-R bundle (B1–B4, ~4–6 modules)** — high-value, near-term, no wall. Consolidates the codim/θ chart
   into a genuine (reduced) bundle.
2. **Smoothness** — commission **S1 (pen-and-paper witness)** first (single global `(C+δ)`-minor on the
   generic stratum, cf. thread-07's global `detΔ`, or per-component?); then S2–S4 formaliser (3–6 modules),
   after checking the S-submersive kill-condition.
3. **The reducedness wall (Part 1) — operator decision, months-scale, NOT required for 1–2.**
