# Statement card — E1: étale height-preservation + smooth-point local-dimension bridge

**Rung:** E1 (entry-2 rung 1). **Thread:** 07-etale-localdim. **Branch:** `expedition/dimension-stack`.

## Module

- **Path:** `lean/DLNFibre/Core/Dimension/Smooth.lean`
- **Namespace:** `DLNFibre.Core.Dimension`
- **Mathlib mirror chosen:** `Mathlib.RingTheory.Smooth.Regular` (the regular-local-ring
  consequence of smoothness — the natural home for the local-dimension bridge that feeds smooth ⟹
  regular). The standalone étale height-preservation brick's own natural Mathlib home would sit near
  `Mathlib.RingTheory.Etale.QuasiFinite` / a `Mathlib.RingTheory.Etale.Height`; it ships here because
  it is the non-circular route's height-preservation step and travels with the bridge. (No
  `Mathlib.RingTheory.Smooth.Regular` exists at the v4.29 pin — this is the mirror an eventual
  extraction would target.)
- **Re-homed from:** `Core/FlatQuasiFiniteHeight.lean` and `Core/SmoothLocalRelativeDimension.lean`
  (both deleted — all content re-homed, no residual left).

## Bridge headlines (delivered)

All in `DLNFibre.Core.Dimension`. Re-homed verbatim (proofs byte-faithful; only the namespace and
two docstring cross-references — "M1"→"the étale height-preservation brick", "(L5)"→"(entry 1,
`Core.Dimension.Catenary`)" — were adjusted).

### Étale (flat + quasi-finite) preserves height — `{R S} [CommRing R] [CommRing S] [Algebra R S]`

- `fibre_height_eq_zero_of_quasiFiniteAt (Q : Ideal S) [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :`
  `(Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).height = 0` — the image of `Q` in
  its fibre is minimal (quasi-finiteness), hence height 0.
- `Ideal.height_eq_under_of_flat_quasiFiniteAt [IsNoetherianRing R] [IsNoetherianRing S]`
  `[Module.Flat R S] (Q : Ideal S) [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :`
  `Q.height = (Q.under R).height` — flat + quasi-finite ⟹ height preserved (going-down + fibre 0).
- **`Ideal.height_eq_under_of_etale`** `[IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S]`
  `(Q : Ideal S) [Q.IsPrime] : Q.height = (Q.under R).height` — the headline brick (étale ⟹ flat and
  quasi-finite). **Full name now `DLNFibre.Core.Dimension.Ideal.height_eq_under_of_etale`** (was
  `DLNFibre.Core.Ideal.height_eq_under_of_etale`).

### Smooth-point local Krull-dimension bridge — `{k} [Field k] {A} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]`

- `rank_kaehler_eq_finrank` / `isStandardSmoothOfRelativeDimension_finrank` — a standard-smooth chart
  is standard smooth of relative dimension `finrank S Ω[S⁄k]` (the rank of Kähler differentials).
- `ringKrullDim_quotient_comap_etale_eq_zero` / `height_comap_etale_eq` — the closed-point fibre over
  affine space `k[x₁,…,xₙ]` is zero-dimensional (Zariski's lemma + entry-1 integral-extension dim
  invariance), so the contracted prime has height exactly `n` (entry-1 catenary).
- **`ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`** `(m : Ideal A) [hm : m.IsMaximal]`
  `[IsSmoothAt k m] : ∃ (n : ℕ) (f : A), f ∉ m ∧ IsStandardSmoothOfRelativeDimension n k (Localization.Away f)`
  `∧ Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal) ∧`
  `ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞)` — the headline. At a smooth maximal
  ideal, the local Krull dimension equals the relative dimension `n` of a basic-open standard-smooth
  chart. Full name unchanged save the namespace:
  `DLNFibre.Core.Dimension.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`.
- `smooth_mvPolynomial` (instance) + two non-vacuity `example`s (the hypothesis bundle is satisfiable;
  the bridge fires concretely on `MvPolynomial (Fin 1) ℚ`) — re-homed in-file, witness shown.

## Non-circularity preservation (the delicate part — preserved faithfully)

The local Krull dimension is computed via the **étale-over-affine-space route**, NOT the
cotangent/tangent identity:

1. the standard-smooth chart `S = A[1/f]` is étale over `B = k[x₁,…,xₙ]`
   (`exists_etale_mvPolynomial`);
2. étale preserves height — `Ideal.height_eq_under_of_etale` (the brick in this same file) gives
   `q.height = (q.under B).height`;
3. the contracted prime `q.under B = q.comap g` has `B/(q.comap g)` zero-dimensional (Zariski's lemma
   embeds it finitely into the residue field), so its height is `n` by the **entry-1** affine-space
   catenary equality `height_add_ringKrullDim_quotient_eq` (`Core.Dimension.Catenary`, reused as a
   black box — no catenary re-induction);
4. height transports down `A → A[1/f]` (`IsLocalization.height_map_of_disjoint`), and
   `ringKrullDim (AtPrime m) = m.height` (`IsLocalization.AtPrime.ringKrullDim_eq_height`).

No tangent-space / cotangent dimension input enters — so this bridge remains available to *prove*
smooth ⟹ regular (E2) without circularity. The re-home kept this route intact; the only
import-graph change is that the entry-1 lemmas are now imported via `Core.Dimension.{Integral,Catenary}`
(they already were in the source).

## `[IsAlgClosed] → [PerfectField]` — **deferred to E2 (and there was nothing to weaken at E1)**

The E1 source files (`FlatQuasiFiniteHeight`, `SmoothLocalRelativeDimension`) used **`[Field k]` only
— no `[IsAlgClosed]`, no `[PerfectField]`** (grep-confirmed). The bridge's docstring already states
"`k` need only be a field — algebraic closedness is not used" (closed-point maximality routes through
Zariski's lemma, not the residue-field-is-`k` Nullstellensatz). So **at E1 there is no closure
hypothesis to weaken** — the module is already at minimal hypotheses (`[Field k]`).

The `[IsAlgClosed] → [PerfectField]` generalisation lives entirely in **E2**
(`Core/SmoothPointRegular.lean`), which already carries `[PerfectField k]` on its headlines
(`smooth_point_isRegularLocalRing`, `finrank_cotangentSpace_*_of_isSmoothAt`) — the residue-field
formal-smoothness step. E1 imposes no closure on E2's path. **No closure hypothesis turned out
genuinely needed in E1.**

## Transitive-consumer sweep (L2)

Re-pointed importers + opens; full-aggregator build confirms transitive consumers:

- **Direct importers of the deleted source files** (3): aggregator `DLNFibre.lean`,
  `SmoothPointRegular.lean`, `FibreDimFibrationProbe.lean` — all re-pointed to
  `import DLNFibre.Core.Dimension.Smooth`.
- **Unqualified consumers of moved decls** (L2-style — the bite the lesson warns about): only
  `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` is referenced by name —
  - `SmoothPointRegular.lean:175` (in `namespace DLNFibre.Core`, unqualified) → added
    `open DLNFibre.Core.Dimension`;
  - `FibreSmoothBlock.lean:97` (transitive consumer via `SmoothPointRegular`, unqualified) → added
    `open DLNFibre.Core.Dimension` (this is exactly the L2 transitive-unqualified case — it imports
    `SmoothPointRegular`, never the source directly, and broke only under the moved namespace);
  - `FibreDimFibrationProbe.lean` already had `open … Dimension`; references the decls only via
    instances, no by-name use.
- **Prose-only reference** (not an import): `FibreCodimMinPrimes.lean:26` mentioned
  `SmoothLocalRelativeDimension` in a docstring → updated to `Core.Dimension.Smooth`.
- Full grep over `lean/`: **zero** stray references to the old module names remain.

## Rider — done

`DLNFibre.lean` longLine fixed. The controller-flagged anchor `DLNFibre.lean:430` (after the −1
import-block shift from collapsing two source imports into one, the line is the
`schurToDsigAt_comp_localizeSchur` comment in the `FibreProjectionCompat` block — the rider's prose
"`Dimension.Codimension` import/comment line" is imprecise; the line-number anchor is the binding
target). Wrapped the 5-line comment block (lines 427–431) so all are ≤100 chars. (Many other
pre-existing aggregator comment longLines remain — out of rider scope.)

## Build / sorry / axiom status

- **Build:** `./scripts/lb DLNFibre` (full aggregator) **green — 3819 jobs** (matches the entry-1
  re-gate baseline 3819/3820; the warm-from-scratch 8521 was the controller's initial main-repo
  warm-up). `Dimension.Smooth` builds standalone (2633 jobs); `SmoothPointRegular` (E2 consumer)
  green.
- **Sorries:** `scripts/sorries` = **0 sorry, 0 #exit, 0 native_decide, 0 axiom**.
- **`#print axioms`** on the headlines = **`[propext, Classical.choice, Quot.sound]`** for all of
  `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`, `Ideal.height_eq_under_of_etale`,
  `Ideal.height_eq_under_of_flat_quasiFiniteAt`.

## Holes / surprises

- **No mathematical hole** — verbatim re-home, build/sorry/axiom all clean.
- **Surprise (benign):** the brief's framing — "the source uses `[IsAlgClosed k]` only to get
  `[PerfectField k]`" — does **not** match the E1 source, which never had any closure hypothesis
  (`[Field k]` only). The `[IsAlgClosed]/[PerfectField]` interaction is wholly an E2 matter. Recorded
  above; nothing to do at E1.
- **Naming note (name=content):** the height brick is declared `Ideal.height_eq_under_of_etale`
  inside `namespace DLNFibre.Core.Dimension`, so its fully-qualified name is
  `DLNFibre.Core.Dimension.Ideal.height_eq_under_of_etale` (the `Ideal.` prefix is intentional —
  mirrors where Mathlib would dot-namespace it on `Ideal`). E2 / any future consumer accessing it
  unqualified must `open DLNFibre.Core.Dimension`.
