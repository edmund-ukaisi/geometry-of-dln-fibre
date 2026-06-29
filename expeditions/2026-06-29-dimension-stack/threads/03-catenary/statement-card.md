# Statement card — R2: polynomial-ring catenary library (`Core.Dimension.Catenary`)

## Module
- **Path:** `lean/DLNFibre/Core/Dimension/Catenary.lean`
- **Namespace:** `DLNFibre.Core.Dimension`
- **Mirrors:** `Mathlib.RingTheory.KrullDimension.Catenary` (no such module exists at the v4.29 pin —
  confirmed no duplication; Mathlib has only the `≤` half).
- **Builds on:** `Core.Dimension.Integral` (integral-extension dim invariance) +
  `Core.Dimension.Basic` (`dim k[x₁,…,xₙ] = n`, `dim (R⧸p) = coheight p`).

## Headline + exact signatures

**The catenary equality** (`@[stacks 00OS]`), three equivalent forms, `k : Type*` any field:

```
theorem height_add_ringKrullDim_quotient_eq
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p) = (n : WithBot ℕ∞)

theorem primeHeight_add_ringKrullDim_quotient_eq
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p) = (n : WithBot ℕ∞)

theorem height_add_coheight_eq (k : Type*) [Field k] (n : ℕ)
    (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (Order.height p : ℕ∞) + Order.coheight p = (n : ℕ∞)
```

Hypotheses: just `[Field k]` (+ `[p.IsPrime]` for the ideal forms). **No** `IsAlgClosed`, **no**
`CharZero`, **no** field-cardinality constraint. `n` is the number of variables.

**The monic-positioning crux** (`@[stacks 00OX]`), the flagged rung:

```
theorem exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit
    {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k) (fne : f ≠ 0) :
    ∃ ψ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      IsUnit (finSuccEquiv k n (ψ f)).leadingCoeff
```

Supporting public decls (all moved into this module): `height_add_coheight_le`,
`primeHeight_add_ringKrullDim_quotient_le` (the `≤` half), `height_eq_height_under_add_height_map_quotient`
(the `@[stacks 00ON]` one-variable tower brick, `A` any Noetherian ring), `exists_monic_mem_of_isUnit_leadingCoeff_mem`,
`ringKrullDim_quotient_eq_under_of_monic`, `one_le_height_map_quotient_of_monic`, `height_map_algEquiv`,
`ringKrullDim_quotient_map_algEquiv`, `nat_le_height_add_coheight`(_spectrum). Four non-vacuity `example`
witnesses (bottom prime of ℚ[x,y]; the height-1 case; `(x)` is prime).

## How the `private`-Mathlib substitution was handled (the crux)

**Re-derived in-repo by re-exposing the private machinery** — there is **no** public route.

- **Verified (grep over `.lake/packages/mathlib/`):** the needed consequence
  `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit` does **not** exist publicly. The whole Noether-
  normalization substitution `T : Xᵢ ↦ Xᵢ + X₀^(N^i)` (`i≠0`, `X₀↦X₀`, `N = 2 + f.totalDegree`) — the
  decls `T1`, `T`, `lt_up`, `sum_r_mul_ne`, `degreeOf_zero_t`, `degreeOf_t_ne_of_ne`,
  `leadingCoeff_finSuccEquiv_t`, `T_leadingcoeff_isUnit` — is `private` in
  `Mathlib/RingTheory/NoetherNormalization.lean`. The only public Noether-normalization API
  (`exists_integral_inj_algHom_of_quotient`) normalizes the **quotient** directly and does **not** hand
  back the one-variable positioning automorphism the catenary `≥`-induction needs (it forgets the tower
  structure used to peel variable 0). Codex (xhigh, decorrelated) independently reached the same verdict:
  no public route; re-exposing is correct; a transcendence-degree / affine-dimension-formula alternative
  would need more infrastructure, not less.
- **What was relied on:** the substitution + its degree bookkeeping are **copied verbatim** from Mathlib
  (`@[stacks 00OW]`, Brasca–Su–Lin–Su) into a `MonicPositioning` namespace; the **only** change is
  visibility (`private` → in-namespace). The provenance is documented in a dedicated docstring section
  (`§ Provenance of the monic-positioning substitution`).
- **Any-field generality, double-checked:** the substitution uses `X₀`-powers, not generic linear
  combinations or chosen `k`-points, so it is characteristic- and field-cardinality-free (finite fields,
  positive characteristic fine; no `Infinite k` / `IsAlgClosed`). Confirmed by Codex; the source L5 was
  already `(k : Type*) [Field k]`, preserved exactly.
- **NOT done (per brief):** no upstream de-privatise PR; no block on one.

## What moved / what stayed
- **Deleted:** `Core/NoetherMonicPositioning.lean` (392 lines) — fully subsumed (it was entirely catenary
  / positioning content).
- **Moved into `Catenary.lean`:** all of `NoetherMonicPositioning` + the three catenary decls from
  `PolynomialDimension` (`height_add_coheight_le`, `primeHeight_add_ringKrullDim_quotient_le`,
  `height_eq_height_under_add_height_map_quotient`). The tower brick (`A`-general) is kept in a
  `§ Polynomial tower` section inside `Catenary` (Codex-endorsed altitude: load-bearing catenary infra,
  not worth a separate module).
- **Stayed (residual `PolynomialDimension.lean`, 59 lines):** `ringKrullDim_quotient_eq_noetherRank`
  (L5.5, the Noether-*rank* dimension fact) + its witness — **not** catenary content, consumed only by the
  finite-type-domain trdeg bridge `AffineNoetherRank`. Docstring rewritten to scope it as the Noether-rank
  fact.
- **Stacks tags pinned by source lookup:** positioning `00OX`; tower brick `00ON` (going-down dim formula);
  headline equality `00OS` (equidimensionality of affine space — its proof *is* the height+coheight=n
  computation).

## Transitive-consumer sweep (L2)
Direct importers of the deleted/changed modules **plus** transitive unqualified consumers were swept by
grepping every moved identifier across all of `DLNFibre/`:
- **Import-swapped** `NoetherMonicPositioning → Dimension.Catenary`: `NullstellensatzCodim` (+ `open Dimension`
  added + docstring), `AffineDomainDimension` (also dropped now-unused `PolynomialDimension` import + docstring),
  `SmoothLocalRelativeDimension` (already had `open Dimension`).
- **Transitive `open Dimension` added** (used `height_map_algEquiv` / `ringKrullDim_quotient_map_algEquiv`
  **unqualified** in `namespace DLNFibre.Core`, reaching the decls transitively — exactly the L2 trap):
  `GraphIdealHeight`, `DeterminantalBasePresentation`, `OrbitTangentCotangent`, `FibreDimFibration`.
- **No change needed:** `AffineNoetherRank` (uses only the staying `ringKrullDim_quotient_eq_noetherRank`);
  `FibreDimFibrationProbe` (uses `affine_domain_…`, not a moved decl).
- **No name collisions:** grep confirmed no local decl named `height_map_algEquiv` /
  `ringKrullDim_quotient_map_algEquiv` anywhere; the only defs are in `Catenary.lean`.
- **Aggregator** `DLNFibre.lean`: removed `NoetherMonicPositioning` import; added `Dimension.Catenary` after
  the existing `Dimension.*` imports.

## Build / sorry / axiom status
- **Full aggregator build** `./scripts/lb DLNFibre`: GREEN (3819 jobs — identical job count to warm baseline,
  so the L2 sweep caught every transitive consumer; nothing dropped out of the build).
- **Non-aggregator tracked files** (`FibreDimFibration`, `FibreDimFibrationProbe`): GREEN (built explicitly).
- **`scripts/sorries`:** `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- **`#print axioms`** on `height_add_ringKrullDim_quotient_eq`, `primeHeight_add_ringKrullDim_quotient_eq`,
  `height_add_coheight_eq`, `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`:
  `[propext, Classical.choice, Quot.sound]` — axiom-clean.

## Holes / surprises (flag for review)
- **No mathematical hole.** The proofs are R1-banked code re-namespaced verbatim; the only logical change is
  the namespace move + the consumer re-points. The catenary equality and the positioning crux were already
  green before this thread.
- **Crux honesty:** the `Catenary` module *contains a verbatim copy of Mathlib's `private` substitution*
  (visibility-only change). This is the intended handling (brief item 2; Codex-endorsed), but a reviewer
  should confirm (a) the copy is faithful (no silent edit to the bookkeeping) and (b) the "any field"
  docstring claim is not overstated — the substitution genuinely chooses no `k`-point. Both checked here,
  but this is the flagged crux rung, so a decorrelated re-read is warranted.
- **Altitude judgement to sanity-check:** the `A`-general tower brick `height_eq_height_under_add_height_map_quotient`
  lives inside a module named `Catenary`. It is more general than the field theorem but is exactly the
  catenary infrastructure the peel step consumes (Codex agreed it is fine as a `§ Polynomial tower` section).
  Flag if the controller's taste prefers it elsewhere.
- **Codex artefact:** `expeditions/2026-06-29-dimension-stack/threads/03-catenary/codex/positioning-{prompt,answer}.md`.
