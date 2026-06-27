# Thread 16 — generic smoothness of the reduced fibre (formaliser, #108) — certificate

**Formaliser tide, delivered at the FLOOR.** New file `lean/DLNFibre/Core/FibreGenericSmooth.lean`
(~135 LoC), wired into the aggregator by the controller; whole library green (3783 jobs); all results
axiom-clean `[propext, Classical.choice, Quot.sound]` (controller-gated). Reviewer PASS-WITH-NOTES.

## HEADLINE — generic smoothness lands as an HONEST CONDITIONAL
Everything is discharged unconditionally EXCEPT a single load-bearing input: `IsSmoothAt k q` of the
reduced-fibre ring `sweepFibreRing` at a top-component generic prime `q` — which is exactly **thread-14
fact (C)** (rank = C+δ on every top component, verified on 19 cases + the general (A)–(D) stratification
sketch, but NOT formalized). The fibre is REDUCIBLE for θ≥2, so the honest object is `IsSmoothAt`
(generic / pointwise), never a global `Smooth k`.

## Both unconditional routes proved walls INSIDE the tide (Codex-confirmed, decorrelated)
- **LEAD wall** (`OrbitSmooth × R-bundle`, orbit transport across `Away chartDsig ≃ SchurLoc ⊗
  sweepFibreRing`): two unbanked sub-walls. (a) `OrbitSmooth.isSmoothAt_normalFormIdeal` is about ONE
  orbit ring, but `sweepFibreRing` is the reducible UNION — needs a quotient-by-intersection
  localization comparison (`Loc.AtPrime (R⧸⋂Iⱼ) ≃ Loc.AtPrime (R⧸I_M)` off the other components) +
  "normal-form point lies off the other top components", neither in this harness. (b) the
  `IsSmoothAt`-across-a-tensor transport is a re-localization-of-base-change, not `A ⊗ Loc.AtPrime q`.
- **FALLBACK wall** (SubmersivePresentation): discharging `IsUnit (subJacobian)` needs determinantal
  rank theory Mathlib lacks — heavier than LEAD.

## Landed unconditionally (reusable bricks, axiom-clean)
- `Algebra.Smooth.tensorProduct` — `Smooth R A → Smooth R B → Smooth R (A ⊗[R] B)` (baseChange + comp +
  comm). General, reusable, promotable.
- `smooth_schurLoc` / `smooth_away_mvPolynomial` — the matrix factor `SchurLoc = Away (detSchurS)` is
  smooth over `k`.
- `isSmoothAt_of_smooth_localizationAway` — basic-open bridge: `Smooth k (Away g) + g ∉ q ⟹ IsSmoothAt k q`.
- `finitePresentation_sweepFibreRing` — instance.

## Headline (CONDITIONAL, honestly named)
`smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre`: given `IsSmoothAt k q` of `sweepFibreRing` at a
top-component generic prime, `∃ g ∉ q, Smooth k (SchurLoc ⊗ Localization.Away g)`. The one open input is
thread-14 fact (C); the hypothesis is load-bearing (reviewer confirmed it is NOT smuggling the
conclusion; non-vacuous; no overclaim).

## Cost to go UNCONDITIONAL (precise — the roadmap item)
(i) discharge `IsSmoothAt k q` of `sweepFibreRing`: either the LEAD sub-walls (a)+(b) — the
quotient-by-intersection localization comparison + normal-form-off-other-components, both FRESH (not in
the harness, but NOT the months-scale reducedness wall — these are bounded, ~multi-module) — or the
FALLBACK determinantal rank (Mathlib gap, larger). PLUS (ii) transport `SchurLoc ⊗ Away g ⟹
IsSmoothAt(Away chartDsig)` across `reducedFibre_chartDsig_tensorEquiv_reducedVariety` via the
localization-of-base-change identification `SchurLoc ⊗ Away g ≃ Away (1⊗g)`
(`IsLocalization.tensorProduct_tensorProduct`, the `FibreBundleReduced` ~60–80-line bookkeeping pattern)
+ the basic-open bridge through `e`. Step (ii) is tractable; step (i) is the genuine remaining content.

## Mathlib lemmas used (real)
`Algebra.Smooth.{comp, baseChange, of_equiv, of_isLocalization_Away}` (`Smooth/Basic.lean:553-572`);
`Algebra.TensorProduct.comm`; `Algebra.basicOpen_subset_smoothLocus_iff_smooth` +
`IsSmoothAt.exists_notMem_smooth` (`Smooth/Locus.lean:93-98,150`); `FinitePresentation.quotient`.

## Artifacts (committed @ c450983f / 48e6af44 / 37edc967)
`threads/16-generic-smooth/statement-card-*.md` (reviewed), `threads/16-generic-smooth/codex/`. Lean:
`Core/FibreGenericSmooth.lean`. Headline assumes `[Field k] [IsAlgClosed k]` (re-flagged per review N3).

## Net smoothness state (controller synthesis)
Smoothness is now: **all plumbing + tensor + chart bricks unconditional + axiom-clean; the single
geometric fact (C) carried as a clearly-named cited hypothesis (pen-and-paper-verified to bedrock in
thread-14).** This mirrors the paper's own posture (the SLT/RLCT cap is Cited to Aoyagi). Going
unconditional = formalize fact (C), a bounded-but-real multi-module build (LEAD sub-walls), NOT the
months-scale reducedness wall.
