# thread 06 — phaseB-hybrid (conditional geometric codimension, defined-objects)

Formaliser tide. Goal: land the GEOMETRIC orbit-codimension result modulo ONE named, dischargeable
hypothesis (Voigt), in defined-objects form, so a later AG sub-expedition discharges it as a drop-in.

Module: `lean/DLNFibre/Core/OrbitCodim.lean` (≈120 LoC). Build green / 0 sorry / axiom-clean.

## Decision: `codimRep` route — PREFERRED (defined-objects), not abstract fallback

Codex consult (xhigh; `codex/codimrep-{prompt,answer}.md`) + Mathlib-v4.29 verification:

- Mathlib v4.29 has **no** ready Zariski-topology instance on a raw `Fin n → k` / `Tuple d`
  (`PrimeSpectrum.zariskiTopology` exists but only on a prime spectrum); `topologicalKrullDim`
  exists but needs a `TopologicalSpace`. So the topological-codim route would require building a
  topology instance — scaffolding.
- The **vanishing-ideal / height** route IS present and bounded: `MvPolynomial.vanishingIdeal`
  (`RingTheory.Nullstellensatz`) returns `Ideal (MvPolynomial σ k)`, and `Ideal.height : ℕ∞`
  (`RingTheory.Ideal.Height`) is the standard affine codimension. Both verified to exist & typecheck
  at the pin (`/tmp` probes).

Chosen: PREFERRED — a real `codimRep` via `Ideal.height ∘ vanishingIdeal`, NOT the abstract `ℕ`
parameter. The down-payment is genuine and bounded (2 defs + 1 abbrev + 1 `Finite` instance). The
coordinatisation `coord : Tuple d ≃ (RepCoord d → k)` is an explicit parameter (codimension is
the Voigt discharge fixes the canonical LINEAR flattening, at which the height is the genuine
geometric codimension and `hVoigt` is Voigt's lemma) — this avoids the only heavy piece
(constructing one specific flattening equiv via `Equiv.piCurry` plumbing) while keeping the
definition faithful. (An unconstrained set-bijection `coord` need not preserve height; the headline
is the honest implication for the supplied `coord` + `hVoigt`, asserting nothing when `hVoigt`
fails. Reviewer-flagged docstring correction, applied.) Definition only: none of the deep dimension theorems (catenary
`dim R/I = n − ht I`, determinantal height, Nullstellensatz radical bridge) are invoked — those ARE
the `voigt` sub-expedition. `Ideal.height : ℕ∞`, so the locus codimension is `ℕ∞`-valued (headline
extracts to `ℤ` via `ENat.toNat_coe`).

Faithfulness note (Codex-flagged trap): the geometric reading needs `[IsAlgClosed k]` only for the
`vanishingIdeal ↔ radical` Nullstellensatz bridge — that bridge is part of the FUTURE Voigt
discharge, not of the definition. As a definition, `(vanishingIdeal (coord '' Z)).height` is the
codimension of `Z`'s Zariski closure over any field, so the def is meaningful at our working fields
(`ℚ`, general). The discharge supplies whatever field hypotheses it needs.

## Statement card

### PROVED (modulo the single named hypothesis `hVoigt`)
- `codimRep_orbitRankLocus_eq_multSum`:
  `(L) (coord : Tuple (foldDim L) ≃ (RepCoord (foldDim L) → k))
     (hVoigt : codimRep coord (orbitRankLocus (⊕L)) = (orbitLinearCodim (⊕L) : ℕ∞)) ⊢
   ((codimRep coord (orbitRankLocus (⊕L))).toNat : ℤ)
     = Σ_{i∈[1,N]} Σ_{u∈[i,N]} Σ_{j∈[u,N]} Σ_{v∈[j,N]} m_{i-1,j-1} m_{uv}`  (m = multiplicityArray L)
  — the GEOMETRIC codimension of the orbit closure `Ō_M` equals Lehalleur–Rimányi Cor 3.5's
  quadratic form, GIVEN Voigt's lemma. Trivial from `hVoigt` + the committed
  `orbitLinearCodim_eq_multSum`.
- `codimRep_orbitRankLocus_eq_finrank_deformationExt1`: the `ℕ∞` restatement,
  `codimRep coord (orbitRankLocus M) = (finrank (deformationExt1 M M) : ℕ∞)` given `hVoigt` —
  geometric codim = dim Ext¹(M,M).
- `self_mem_orbitRankLocus`: `M ∈ orbitRankLocus M` (non-vacuity: the orbit closure contains `M`).

### PROVED — canonical-flattening addition (PR #2 reviewer precision point, 2026-06-18)
The general `codimRep coord` originally stated `hVoigt` at an *arbitrary* set-equiv `coord`; the
canonical linear flattening (one coordinate per matrix entry) was never constructed, so `hVoigt` was
not pinned to the intended geometric coordinatisation. Closed additively (general `codimRep` kept as
the honest general building block; `coord` parameter NOT removed):
- `canonicalCoord (d) : Tuple d ≃ (RepCoord d → k)` — THE canonical linear flattening
  `A ↦ fun ⟨i, r, c⟩ ↦ (A i) r c`, assembled from `Equiv.piCongrRight (Equiv.curry …).symm` +
  `(Equiv.piCurry …).symm`. `noncomputable def`.
- `canonicalCoord_apply` (`@[simp]`, `omit [Field k]`): `canonicalCoord d A x = A x.1 x.2.1 x.2.2`
  by `rfl` — the application IS the entry flattening.
- `codimRepCanonical (Z) := codimRep (canonicalCoord d) Z` — geometric codim at the canonical coord.
- `codimRepCanonical_orbitRankLocus_eq_multSum`: the Cor 3.5 quadratic-form headline with `hVoigt`
  now reading `codimRep (canonicalCoord (foldDim L)) (orbitRankLocus (⊕L)) = orbitLinearCodim (⊕L)`
  — Voigt's lemma at THE canonical flattening, not an arbitrary equiv. Direct specialisation of the
  general theorem (same proof). `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
- `codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1`: the `ℕ∞`/Ext¹ restatement at
  `canonicalCoord`.

### NOTED-AND-DEFERRED — linear-coordinate invariance (brief item 3)
The docstring claims the height is coordinate-independent for a *linear* `coord` (invariant under the
induced ring automorphism). NOT proved: Mathlib v4.29 has no transport lemma for `Ideal.height`
under a `RingEquiv`/`comap`. A proof would need (i) the `AlgEquiv` of `MvPolynomial (RepCoord d) k`
induced by the coordinate change, (ii) `vanishingIdeal (φ ∘ coord '' Z) = comap φ (vanishingIdeal
(coord '' Z))`, (iii) `(comap φ I).height = I.height` for `φ` a ring iso. None is cheap at this pin;
left to the `voigt` sub-expedition. Recorded in the `## codimRep faithfulness` docstring.

### ASSUMED (the single open obligation)
- `hVoigt : codimRep coord (orbitRankLocus M) = orbitLinearCodim M` — **Voigt's lemma**: the
  geometric codimension of the orbit (rank-)locus equals the tangent/expected codimension
  `orbitLinearCodim M = dim Ext¹(M,M)`. An explicit theorem HYPOTHESIS, NOT a global `axiom` (the
  module's `#print axioms` is `[propext, Classical.choice, Quot.sound]` only). To be discharged by a
  later AG-dimension-theory sub-expedition as a drop-in against this fixed interface.

### CITED (named, not proved here)
- Lehalleur–Rimányi 2024 **Thm 3.8**: for the equioriented type-`A` quiver the `G_d`-orbit closure
  of `M` is exactly the rank locus `orbitRankLocus M = {A | rankPattern A ≤ rankPattern M pointwise}`.
  Engine-verifiable (ties to `RankPattern` / orbit↔Kostant). Docstring'd on `orbitRankLocus`.
- Voigt / KMS codimension theory (the content `hVoigt` will discharge). Docstring'd on `codimRep` /
  the headline.

### Confidence check (numerical, prior to formalisation)
rankloc-probe (synthesis.md, sympy + Buch–Fulton/KMS + Codex): on `(2,2,2)` the orbit-closure
(rank-locus) codimensions equal dim Ext¹ EXACTLY — `(3, 4, 4, 8)` [KMS rectangle sum; locus
prime/normal/CM]. The `(1,1)`-orbit codim 3 and `{A=0}` codim 4 match the `orbitLinearCodim`
witnesses in `OrbitLinearCodim.lean`. So the conditional headline's equality is the correct claim;
`hVoigt` is true (the math is certain), pending the Lean AG-dimension build.

## Build status
- `lake build DLNFibre.Core.OrbitCodim` — green.
- `python3 scripts/sorries` — 0 sorry / 0 axiom / 0 native_decide / 0 #exit (whole lib).
- `#print axioms codimRep_orbitRankLocus_eq_multSum` = `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no new axiom). Same for the `finrank` restatement, `orbitRankLocus`, `codimRep`.

## For the controller
- Wire `import DLNFibre.Core.OrbitCodim` into the aggregator `DLNFibre.lean` (single-writer; I did
  not touch it).
- Module is `Core`-only (imports `OrbitLinearCodim`, `IntervalModule`, `RingTheory.Nullstellensatz`,
  `RingTheory.Ideal.Height`); never imports `DLN`.
