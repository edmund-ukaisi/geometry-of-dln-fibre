# Thread 02 — θ + Lemma-4.6(B) Lean/Mathlib terrain map (scout) — certificate

**Persisted by the controller.** Read-only, off `dev`; mathlib rev `8a178386`. One decorrelated Codex (xhigh).

## AREA 1 — existing θ / component infrastructure

**θ-count + component↔Kostant bijection are PROVED unconditionally — but over `Σ̄^r`, NOT the fibre.**
- `Core.CCodimZeroStrict.numTop_eq_ncard_topComponents` (`CCodimZeroStrict.lean:889`), unconditional
  (`[IsAlgClosed][CharZero]` + `kostantPartitions.Nonempty`): `θ = numTop d r = #top-dim irreducible
  components of Σ̄^r` (`= productRankLocusLE d r`). `topComponents` (`ThetaComponentCount.lean:297`).
- **Bijection (not just count):** `ThetaComponentCount.bijOn_partitionIdeal_topComponents_of` (`:340`) —
  `m ↦ vanishingIdeal(Ō_{realizerD m})` is `Set.BijOn` from minimising Kostant partitions onto
  `topComponents`. + `SigmaComponents.minimalPrimes_sigmaIdeal_eq` (`:206`) + `≃o` to Mathlib
  `irreducibleComponents` (`:217`, via `Ideal.minimalPrimes.equivIrreducibleComponents`). `cTheta`
  (`CThetaValue.lean:74`).
- **THE GAP:** the **fibre `mult⁻¹(B)`** θ is genuinely new — `topComponents`/`numTop` never instantiate
  over `fibre` (grep-confirmed). For `B≠0` the fibre isn't `G_d`-stable, so the orbit-ideal machinery does
  not transfer directly. Only `FibreCodimMinPrimes` (height bounds, not a count) touches fibre min-primes.

## AREA 2 — the codim hand-build (consolidation target)

- `e = Core.ChartLocalizedAlgEquiv.chartLocalizedAlgEquiv` (`:88`): a full `AlgEquiv`
  `Localization.Away(chartDsig) ≃ₐ[k] Localization.Away(chartGfib)` between localizations of the **reduced
  `vanishingIdeal`-quotients** of `O(Σ^r)` and `O(F)`. **Already the localized fibre↔Σ^r chart bridge** —
  but radical-insensitive (heights/Krull-dim only, not scheme points).
- All PROVED: seams A–E, `hsig` (`SourceNoDrop`, min-prime avoidance, no `I_eq=I_le`), `hP`
  (`SchurSideNoDrop`), `hSweep` (`FibreCodimFinal.lean:117`), `hClosure` (`ClosureBridge`, codim-sandwich),
  `RouteCAssembly`, `G1` (`FibreNormalForm`).
- **Reducedness wall (R2-3b) it routed around** — a real reduced bundle needs: (1) `fibreGenIdeal=(mult−B)`
  radical (⟺ `F_E` reduced) — certified TRUE pen-and-paper (thread 16), Lean-unproven, `≥2-module
  from-scratch AG sub-project`; (2) scheme structure on the non-reduced quotient; (3) smoothness — only
  **generic/per-chart** (GLOBAL smoothness FALSE: `d(mult)` drops rank at `E`, fibre singular there). Codim
  is closed without (1)–(3) ⟹ **scope-B is a strict scope increase, not a free consolidation**; `e` likely
  stays a load-bearing radical-insensitive lemma.

## AREA 3 — Mathlib v4.29 coverage

- **Components/minimalPrimes — AVAILABLE:** `Ideal.minimalPrimes.equivIrreducibleComponents`,
  `IsLocalization.orderIsoOfPrime` (the (A)-transport brick), `height_comap`. NO `IsEquidimensional`/top-dim
  predicate (engine rolls its own; `Σ̄^r` pattern is the template).
- **Local-trivial bundles — NOT at scheme level (headline gap):** `Topology/FiberBundle/*` is
  homeomorphism-based; NO algebraic/scheme `AffineBundle`. Must hand-build (~200+ lines) — and NOT needed
  for codim/θ (`varietyDim`-additivity gives the dimension content).
- **Smoothness — PARTIAL + partly ported:** scheme `smoothLocus`, ring `IsStandardSmoothOfRelativeDimension`
  + free⟹standard-smooth + Jacobian criterion; engine ports `MatrixKaehler`, `CotangentJacobian`,
  `FibreJacobian.*` (already on the fibre), `SmoothPointRegular`. NO direct `regular ⟹ reduced` — hand-build.

## Biggest scope-B risks (ranked)
1. Reducedness wall (R2-3b) — highest; may NOT be on the θ critical path (see #4).
2. Smoothness generic/per-chart, not global (risk of re-walking thread-27 circularity).
3. No scheme bundle API — hand-build + cocycles; needed only if a result consumes "bundle" as an object.
4. **The (A) decoupling — de-risking lever.** Fibre θ-count/bijection likely reachable WITHOUT walls #1/#2,
   by transporting the proved `Σ̄^r` bijection through `e` via `orderIsoOfPrime` (minimal primes survive
   localization; nilpotents add none ⟹ reducedness NOT the blocker for *counting*). **Kill-condition:** does
   every top-dim component of `mult⁻¹(E)` meet the pivot-open `{detΔ≠0}` chart? Yes ⟹ fibre θ ≈ 1–3 light
   lemmas, walls off the θ path; a component in `V(detΔ)` ⟹ transport breaks, fibre-θ forces a wall.

## Recommended decisive next computation
Primary-decompose `fibreGenIdeal` on `(2,2,2),r=1` and `(2,2,2,2),r=1` (Singular/M2); per top-dim component
check whether `detΔ` is a non-zero-divisor / nonvanishing. Decisive fork for whether fibre-θ needs the wall.
