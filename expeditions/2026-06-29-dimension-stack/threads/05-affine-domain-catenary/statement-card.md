# Statement card — R3: finite-type-domain dimension formula (`Core.Dimension.AffineDomain`)

## Module
- **Path:** `lean/DLNFibre/Core/Dimension/AffineDomain.lean` (new file, 233 lines).
- **Namespace:** `DLNFibre.Core.Dimension`.
- **Mirrors:** the eventual Mathlib home for the dimension theory of finitely generated algebras —
  **distinct** from `Mathlib.RingTheory.KrullDimension.Catenary` (the polynomial-ring identity,
  `Core.Dimension.Catenary`).
- **Builds on:** `Core.Dimension.Catenary` (the polynomial-ring catenary equality
  `height_add_ringKrullDim_quotient_eq`, reused as a black box — **no** catenary re-induction),
  `Core.Dimension.Integral` (`ringKrullDim_eq_of_integral_injective`), `Core.Dimension.Basic`
  (`ringKrullDim_mvPolynomial_fin_field`).

## File-placement decision + why
**New file `Core/Dimension/AffineDomain.lean`** rather than extending `Catenary.lean`. Rationale:
1. **Distinct math layer / distinct Mathlib home.** The polynomial-ring catenary identity is
   `Mathlib.RingTheory.KrullDimension.Catenary`; the finite-type-domain *dimension formula /
   equidimensionality* is a separate result (Stacks 10.114.4, tag 00OS) that belongs in a separate
   finitely-generated-algebra dimension file. Namespace-mirror discipline (brief) wants one source
   file per eventual Mathlib home — a file-move extraction.
2. **Cohesion + weight.** `Catenary.lean` is already ~480 lines, dominated by the verbatim-copied
   `private` `MonicPositioning` substitution. The affine-domain layer is self-contained (one new
   general brick — integral *height* transport — plus a short Noether-normalization assembly), and
   reads cleanly on its own.

## Headline + exact signatures (hypotheses confirmed by the green build, not assumed)

**The dimension formula** (`@[stacks 00OS]`), `k : Type*` any field:
```
theorem affine_domain_height_add_ringKrullDim_quotient_eq
    (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (p : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (((MvPolynomial (Fin n) k) ⧸ I) ⧸ p)
      = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I)
```
Hypotheses: `[Field k]` + `[I.IsPrime]` (so `A = R ⧸ I` is a domain) + `[p.IsPrime]`. **No**
`IsAlgClosed`, **no** `CharZero`, **no** field-cardinality constraint — confirmed by the build.

**Closed-point corollaries** (`@[stacks 00OS]`):
```
theorem height_eq_ringKrullDim_of_isMaximal
    (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (m : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I)

theorem ringKrullDim_localizationAtPrime_isMaximal_eq
    (k : Type*) [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (m : Ideal ((MvPolynomial (Fin n) k) ⧸ I)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ I)
```

**The one new general brick** — integral *height* transport (no Stacks machine attribute; the
going-down half cites Stacks 00H8 in prose):
```
theorem height_under_eq_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDomain S] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height
```
`≤` is going-up (`strictMono_comap_of_isIntegral`); `≥` is going-down (`Algebra.HasGoingDown`,
present for integral extensions of an integrally closed domain). Minimal hypotheses — confirmed no
spurious field/closure/char hyps.

Plus the auxiliary `quotientMap_under_isIntegral_injective` (induced quotient map of a contracted
prime is integral injective) and **four** non-vacuity `example` witnesses (identity-transport on
`ℚ[x]`; the affine-domain formula at `⊥` of `ℚ[x] ⧸ ⊥`; the local↔global corollary; maximal-ideal
existence).

## name = content — the 00OS tagging (a correction over the source)
Stacks **00OS** (Lemma 10.114.4, verified against the Stacks project) is *exactly* the
equidimensionality of a finite-type domain over a field: `dim S = dim Sₘ` for every maximal `m`, every
maximal prime chain has length `dim S`. So 00OS is the **genuine verbatim match** for these
finite-type-domain corollaries — more so than for the polynomial-ring identity that `Catenary.lean`
carries 00OS on (R2 review flagged that as "defensible PASS-with-note"). Here 00OS is machine-tagged
on the headline formula (the dimension-formula restatement of 10.114.4) and the two closed-point
corollaries (the verbatim `dim S = dim Sₘ`), each with a docstring quote clarifying which sentence of
10.114.4 it instantiates. The integral-extension dimension equality used inside is `00OK` (tagged on
`ringKrullDim_eq_of_integral_injective` in `Core.Dimension.Integral`); the going-down half of the new
height brick is Stacks `00H8` (`Algebra.HasGoingDown`), prose-cited only.

## What moved / what stayed
- **Deleted:** `lean/DLNFibre/Core/AffineDomainDimension.lean` (215 lines) — it held **only**
  re-homed content (height-transport + affine-domain formula + corollaries + witnesses); no residual
  non-catenary content, so the whole file was removed (no stale duplicate).
- **Moved into `Core/Dimension/AffineDomain.lean`** (namespace `DLNFibre.Core` → `DLNFibre.Core.Dimension`):
  `height_under_eq_of_isIntegral`, `quotientMap_under_isIntegral_injective`,
  `affine_domain_height_add_ringKrullDim_quotient_eq`, `height_eq_ringKrullDim_of_isMaximal`,
  `ringKrullDim_localizationAtPrime_isMaximal_eq`, and the four witnesses. Proof bodies are the R2-banked
  proofs verbatim; the only changes are the namespace, expanded docstrings (the 00OS equidimensionality
  reading + placement rationale), and the `@[stacks 00OS]` machine tags.

## Transitive-consumer sweep (L2 applied)
Swept **every** moved identifier across all of `DLNFibre/` (not just direct importers). Three
consumers reference the moved decls (all unqualified, inside `namespace DLNFibre.Core` — reaching the
sub-namespace `Dimension`):
- `FibreDimFibration.lean` — import `AffineDomainDimension → Dimension.AffineDomain`; already had
  `open … Dimension` (no open change). Uses `affine_domain_height_add_ringKrullDim_quotient_eq`.
- `OrbitTangentCotangent.lean` — import swap; already had `open … Dimension`. Uses
  `height_eq_ringKrullDim_of_isMaximal`, `ringKrullDim_localizationAtPrime_isMaximal_eq`.
- `FibreDimFibrationProbe.lean` (un-aggregated throwaway probe) — import swap **+ `open Dimension`
  added** (it had `open Matrix MvPolynomial Ideal` only — the exact L2 trap: an unqualified consumer
  with no `open Dimension`). Built explicitly green (3026 jobs).
- **No change needed:** `FibreSmoothBlock.lean` — references only the `_fintype` wrappers
  (`height_eq_ringKrullDim_of_isMaximal_fintype` &c.), which are distinct decls in `namespace
  DLNFibre.Core` (defined in `OrbitTangentCotangent`/`FibreDimFibration`), **not** moved.
- **No name collisions:** grep confirmed no other local decl shares a moved name; the `_fintype`
  wrappers are name-distinct (suffix).
- **Aggregator** `DLNFibre.lean`: removed `import …AffineDomainDimension`; added
  `import …Dimension.AffineDomain` directly after `Dimension.Catenary` (single-writer tail discipline
  respected — placed among the existing `Dimension.*` block).
- **Post-sweep:** `rg "AffineDomainDimension"` over `DLNFibre/` + `DLNFibre.lean` returns **nothing**.

## Build / sorry / axiom status
- **Full aggregator** `./scripts/lb DLNFibre`: **GREEN, 3819 jobs** — identical job count to the warm
  baseline, so the L2 sweep caught every transitive consumer (nothing dropped out, nothing new broke).
- `AffineDomain` alone: green (2085 jobs); `FibreDimFibrationProbe` (un-aggregated): green (3026 jobs).
- **`scripts/sorries`:** `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- **`#print axioms`** on `affine_domain_height_add_ringKrullDim_quotient_eq`,
  `height_eq_ringKrullDim_of_isMaximal`, `ringKrullDim_localizationAtPrime_isMaximal_eq`,
  `height_under_eq_of_isIntegral`: all `[propext, Classical.choice, Quot.sound]` — axiom-clean.

## Rider cosmetics (both fixed)
- **(a) `Catenary.lean` top docstring** — the two dangling `§` cross-references corrected to resolve:
  `§ Monic positioning` → `§ Provenance of the monic-positioning substitution` (where the
  `MonicPositioning` machinery lives); `§ Polynomial tower` →
  `§ The catenary ≤ direction and the one-variable polynomial tower` (where the tower brick lives).
  (The third reference, `§ Provenance …`, already resolved — untouched.)
- **(b) R2 `threads/03-catenary/statement-card.md`** — corrected the three spots implying `00OX`/`00ON`
  are machine `@[stacks]` attributes; they are prose `[Stacks, Tag …]` mentions only. Only `00OS` is a
  machine attribute in the code. Card now matches the (more conservative) code.

## Holes / surprises
- **No mathematical hole.** Proof bodies are the R2-banked code, re-namespaced; the logical content is
  unchanged. The build re-verifies all four headline decls axiom-clean.
- **One name=content surprise (improvement, not a hole):** verifying Stacks 00OS against the source
  showed it is *precisely* the finite-type-domain equidimensionality — so the 00OS machine tags here
  are a tighter statement-match than the same tag on the polynomial-ring identity in `Catenary.lean`.
  Recorded above; no action needed on `Catenary.lean` (R2 signed off; its 00OS is the accepted
  PASS-with-note).
