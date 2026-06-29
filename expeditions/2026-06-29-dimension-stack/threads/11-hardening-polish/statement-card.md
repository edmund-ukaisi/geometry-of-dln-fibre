# Statement card — hardening-polish (rung 11)

**Function:** `formaliser` (hardening-polish). **Branch:** `expedition/dimension-stack`.
**Task source:** the hardener verdict (`threads/10-hardener/hardener.md`, SOLID-with-notes) — its
three in-reach pre-close completions + one optional tag-sharpen. **Method:** edit + per-module build
+ full-aggregator L2 sweep + axiom probe; no new math (re-home + witness + namespace fix).

## Gate status

- **Full aggregator build:** GREEN — `./scripts/lb DLNFibre` = `Build completed successfully (3819
  jobs).` (unchanged job count: the moved decls net out; one redundant import dropped).
- **Sorries:** clean — `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- **DLN payoff axioms UNCHANGED** (`= [propext, Classical.choice, Quot.sound]`):
  - `DLNFibre.DLN.rlct_lossDLN_eq_half_cCodim_add_shift` ✓
  - `DLNFibre.Core.codimRepCanonical_fibre_eq_cCodim_add_shift` ✓
- **Moved generalization axioms clean** (`= [propext, Classical.choice, Quot.sound]`):
  `height_add_ringKrullDim_quotient_eq_card_of_ne_top` + both bricks
  (`exists_minimalPrime_height_eq_height`, `exists_minimalPrime_ringKrullDim_quotient_ge`). No
  `sorryAx`, no cited/Aoyagi axiom — the standard logical trio only.
- **LoC delta:** ~net zero (decls relocated; one import line removed; docstrings updated). 5 files
  touched.

## Task 1 ★ — re-home the any-proper-ideal generalization

**Moved into `lean/DLNFibre/Core/Dimension/Codimension.lean`** (the codimension-bridge module, which
already proves the prime-form headline — the generalization sits directly alongside it):

- `exists_minimalPrime_height_eq_height {R} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  (hIne : I ≠ ⊤) : ∃ p ∈ I.minimalPrimes, p.height = I.height` — general Noetherian brick.
- `exists_minimalPrime_ringKrullDim_quotient_ge {R} [CommRing R] [IsNoetherianRing R]
  [FiniteRingKrullDim R] (I : Ideal R) (hIne : I ≠ ⊤) :
  ∃ p ∈ I.minimalPrimes, ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p)` — general
  Noetherian/`FiniteRingKrullDim` brick (top-dimensional component).
- `height_add_ringKrullDim_quotient_eq_card_of_ne_top {k} [Field k] {σ} [Finite σ]
  (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤) :
  (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞)` — the
  **headline**: the affine-space catenary at **any proper ideal** (no primality, no radicality),
  field-general, `Tuple`-free.

**Relation to the prime headline.** The prime-only form
`height_add_ringKrullDim_quotient_eq_card (p) [p.IsPrime]` is retained in the same module (the common
case) and is now exactly the special case `I = p` of the new headline — the docstring states this.
The any-proper-ideal proof is a direct `le_antisymm` minimal-prime / chain squeeze that *uses* the
prime form on a top component (upper bound) and a height-realizing minimal prime (lower bound).

**Closure-free path confirmed.** The new home `Codimension.lean` gained one import,
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`; it imports **no** `NullstellensatzCodim` /
`AlgebraicClosure`. The generalization's `#print axioms` is the clean trio.

**Old site cleaned.** The three decls are **deleted** from `RadicalCatenary.lean` (sweep confirms a
single declaration site — Codimension — for each; no stale duplicate). `RadicalCatenary.lean` now
carries only the `Tuple`-coupled DLN specialisation
(`codimRepCanonical_add_varietyDim_eq_card_of_nonempty`, `vanishingIdeal_ne_top_of_nonempty`, the
`AlgebraicClosure ℚ` witness); its module docstring rewritten to point at the new home; its
now-unused `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian` import removed.

**Consumers re-pointed (L2 transitive sweep).** Two consumers reference the moved decls *unqualified*
from `DLNFibre.Core` (not the long qualified path):
- `TopDimMinPrimesBridge.lean:69` — `height_add_ringKrullDim_quotient_eq_card_of_ne_top`;
- `FibreCodimFinal.lean:90` — `exists_minimalPrime_ringKrullDim_quotient_ge`.
Re-pointed by **adding all three moved names to the `export Dimension (...)` in
`NullstellensatzCodim.lean`** (the existing re-export mechanism that already lifts the prime headline
and `varietyDim` into the short `DLNFibre.Core` namespace). Both consumers and `RadicalCatenary`
(which `open Dimension`) build green unchanged. Reachability double-checked by `#check` at both the
qualified `Dimension.` path and the `Core.` export path.

## Task 2 — Regular.lean non-vacuity witness (bedrock 2.1)

Added an in-file `example` at the end of `Regular.lean` firing the capstone
`smooth_point_isRegularLocalRing (k := ℚ) (A := MvPolynomial (Fin 1) ℚ) m` on a maximal ideal `m` of
the affine line over `ℚ`: `IsRegularLocalRing (Localization.AtPrime m)`. `[PerfectField ℚ]` resolves
via `PerfectField.ofCharZero`; `[IsSmoothAt ℚ m]` is established (as in the Smooth-module witness)
from `smoothLocus_eq_univ`. This exhibits the full antecedent bundle
`[PerfectField k] [IsSmoothAt k m] [FiniteType k A]` satisfied on a concrete nonzero target — closing
the one Dimension module the hardener flagged as lacking an in-file witness. Compiles
(`./scripts/lb DLNFibre.Core.Dimension.Regular` green).

## Task 3 — nested-`Ideal.` namespace wart (Smooth.lean)

`theorem Ideal.height_eq_under_of_flat_quasiFiniteAt` / `…_of_etale` were declared inside
`namespace DLNFibre.Core.Dimension`, resolving to the nested
`DLNFibre.Core.Dimension.Ideal.height_eq_under_of_*` sub-namespace (a discoverability/collision wart
that *looks like* the global Mathlib `Ideal` namespace but is not). **Fixed by dropping the `Ideal.`
prefix** → plain `height_eq_under_of_flat_quasiFiniteAt` / `height_eq_under_of_etale` in
`DLNFibre.Core.Dimension`, consistent with their siblings (`fibre_height_eq_zero_of_quasiFiniteAt`,
`ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`); on the eventual Mathlib move they become the
true `Ideal.height_eq_under_of_*`. (Tried the `namespace _root_.Ideal` wrap first — the
*declarations* landed but the out-of-block references at the witness `example` and at
`ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` then failed to resolve `Ideal.height_eq_under_*`;
the plain-name option is robust and matches sibling style.)

**Sweep result:** the only references to these names are inside `Smooth.lean` itself (the étale
corollary's body, the witness `example`, and `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`);
**no external consumer** uses any qualification — confirming the hardener's read. All three internal
references re-pointed to the plain names; module-header docstring references updated; module builds
green.

## Task 4 (optional) — AffineDomain `@[stacks 00OS]` corollary tags

**Not done — deliberately skipped** (the task said skip if it risks the build / is lowest priority).
The three tags already carry honest disambiguating comment strings, and the module docstring (lines
33-40) openly discloses that 00OS Lemma 10.114.4 is the equidimensionality statement, that the two
closed-point corollaries are its *verbatim* `dim S = dim Sₘ` form, and that the arbitrary-prime form
is a *restatement* (with Codex's `00P2` noted as closest-but-"none displays it exactly"). Switching
`00OS → 00P2` would require independently verifying `00P2` is the right Stacks tag — which neither
the hardener nor Codex could confirm — so an unverified swap would *introduce* a fidelity risk, the
opposite of hardening. The closed-point corollaries (184, 200) are 00OS-proper (hardener-confirmed)
and need no change. The existing state is honest-with-co-located-caveat. Left as-is by design.

## Files touched (absolute paths)

- `/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/Core/Dimension/Codimension.lean` —
  new home of the 3 moved decls + import + docstring `## Contents` update.
- `/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/Core/RadicalCatenary.lean` — 3 decls
  deleted; docstring rewritten; unused minimal-prime import removed.
- `/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/Core/NullstellensatzCodim.lean` — 3
  names added to `export Dimension (...)`.
- `/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/Core/Dimension/Smooth.lean` — namespace
  fix (plain names) + 3 internal references + docstring updated.
- `/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/Core/Dimension/Regular.lean` —
  non-vacuity `example` witness added.

## Holes / surprises

None. No `sorry`/`axiom` introduced; DLN payoffs axiom-identical; the generalization is clean and
closure-free. The one surprise was the `namespace _root_.Ideal` reference-resolution failure for
out-of-block call sites (Task 3) — resolved by the plain-name option, which is also the cleaner
sibling-consistent home until upstream.
