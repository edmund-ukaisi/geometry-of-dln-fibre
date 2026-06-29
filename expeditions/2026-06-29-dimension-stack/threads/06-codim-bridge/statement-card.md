# Statement card — R4: field-general codimension bridge (`Core.Dimension.Codimension`)

## Module
- **Path:** `lean/DLNFibre/Core/Dimension/Codimension.lean` (new file, 158 lines).
- **Namespace:** `DLNFibre.Core.Dimension`.
- **Mirrors:** the eventual Mathlib home for the codimension of affine algebraic sets
  (`Mathlib.AlgebraicGeometry.Codimension` once that lands — no such file exists at the v4.29 pin;
  the docstring names it as the target home, as `AffineDomain.lean` does for its layer).
- **Builds on:** `Core.Dimension.Catenary` (the polynomial-ring catenary equality
  `height_add_ringKrullDim_quotient_eq`, reused as a black box — **no** catenary re-induction), plus
  `Mathlib.RingTheory.{Nullstellensatz, Spectrum.Prime.Topology}` for the Zariski predicates.

## The R0 split, executed (field-general core extracted; `[IsAlgClosed]` layer + consumers stayed)

**Extracted to `Core/Dimension/Codimension.lean`** (the field-general core — exact minimal hyps
`[Field k] [Finite σ]`, confirmed by the build; **no** `[IsAlgClosed]`, **no** `[CharZero]`, **no**
field-cardinality):

```
def IsZariskiClosed (Z : Set (σ → k)) : Prop := Z = zeroLocus k (vanishingIdeal k Z)
def IsZariskiIrreducible (Z : Set (σ → k)) : Prop :=
  IsIrreducible (MvPolynomial.pointToPoint (k := k) (K := k) '' Z)

theorem vanishingIdeal_isRadical (Z : Set (σ → k)) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsRadical          -- [Field k] only

theorem isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z : Set (σ → k)) :
    IsZariskiIrreducible Z ↔ (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime

theorem ringKrullDim_mvPolynomial_finite [Finite σ] :
    ringKrullDim (MvPolynomial σ k) = (Nat.card σ : WithBot ℕ∞)

theorem height_add_ringKrullDim_quotient_eq_card [Finite σ] (p : Ideal (MvPolynomial σ k)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ p) = (Nat.card σ : WithBot ℕ∞)

noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
  (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0

theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}    -- HEADLINE
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞)

theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
    (hp : (vanishingIdeal k Z : Ideal (MvPolynomial σ k)).IsPrime) :
    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z
```
All decls share the section `variable {k : Type u} [Field k] {σ : Type*}`; `[Finite σ]` is added per
decl exactly where dimension finiteness is used. Proof bodies are the source bodies verbatim, only
re-namespaced + the `vanishingIdeal_isRadical` docstring fix + the `simpa`→`simp at` linter cleanup
(see below). Plus **one** non-vacuity `example`: at `⊥` of `MvPolynomial σ k` (prime, the polynomial
ring over a field is a domain) the catenary identity fires `height ⊥ + ringKrullDim (R ⧸ ⊥) = Nat.card
σ` for **any** field and finite index — the strongest field-general witness (holds for finite /
non-algebraically-closed fields, no infinitude needed).

**Field-general core compiles at `[Field k] [Finite σ]` (no closure) — confirmed.** The standalone
`Codimension` build is green (2123 jobs) with **no** `[IsAlgClosed]`/`[CharZero]`/`[Infinite]` anywhere
in the core; `#print axioms` on the headline = `[propext, Classical.choice, Quot.sound]`. Nothing
forced closure back in — the split is genuinely clean (the geometric band feeds no core theorem, as
R0 predicted).

## What stayed in `NullstellensatzCodim.lean` (re-pointed to import the new core)
The two pieces that genuinely use more, plus the DLN consumers:
- **`[IsAlgClosed]` / non-vacuity layer:** `nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal`
  (`[IsAlgClosed k] [Finite σ]`, weak Nullstellensatz via `vanishingIdeal_zeroLocus_eq_radical`);
  `vanishingIdeal_univ_eq_bot` (**weakened**, see below); the non-vacuity `example` at `Set.univ`
  (`[IsAlgClosed k] [Finite σ]`).
- **DLN `codimRep` consumers** (over `Tuple`/`RepCoord d`): `codimRep_add_varietyDim_eq_card`,
  `codimRep_eq_card_sub_varietyDim`, `codimRepCanonical_eq_card_sub_varietyDim`. **Their hypotheses
  are unchanged** (the brief said do not touch them here — dropping their dead-weight `[IsAlgClosed]`
  is the later RF rung).

## `vanishingIdeal_isRadical` docstring fix (name = content)
The stale source docstring claimed the radical-ness rides on "strong Nullstellensatz / algebraically
closed field". The proof is the **no-nilpotents argument over a field** (if `pⁿ` vanishes on `Z` then
`(p x)ⁿ = 0`, so `p x = 0` in the field `k`). The new docstring states exactly that and flags
explicitly: "**not** the strong Nullstellensatz, so `[IsAlgClosed k]` is not needed." The module
docstring repeats the field-general claim with the `ZMod 2`-style non-closure point.

## `vanishingIdeal_univ_eq_bot` — weakened to `[Infinite k]` (optional clean win, taken)
R0 found its true need is `[Infinite k]`, not `[IsAlgClosed k]`. Verified: the proof routes through
`MvPolynomial.funext`, whose section needs `[CommRing R] [IsDomain R]` + `Set.infinite_univ` (i.e.
`[Infinite R]`). A field is a domain; `[Infinite k]` is exactly the residual need. Weakened the
hypothesis from `[IsAlgClosed k]` to `[Infinite k]`; the downstream `example` (which carries
`[IsAlgClosed k]`) still resolves `[Infinite k]` by instance (`IsAlgClosed → Infinite`). Stays green,
axiom-clean. **(This is a `vanishingIdeal_univ_eq_bot` weakening only — NOT the genuine zeroLocus↔radical
`[IsAlgClosed]` in `nonempty_…`, which R0/L1 confirmed does not weaken.)**

## Re-export strategy (the L2 / re-pointing decision)
The moved decls left namespace `DLNFibre.Core` for `DLNFibre.Core.Dimension`. **22 files** consume
`varietyDim` alone (plus the other moved names), the vast majority referencing it **unqualified**
inside `namespace DLNFibre.Core` and **not** opening `Dimension`. Rather than add `open Dimension` to
~17 files (large, fragile diff), the re-pointed `NullstellensatzCodim.lean` carries a single
```
export Dimension (IsZariskiClosed IsZariskiIrreducible vanishingIdeal_isRadical
  isZariskiIrreducible_iff_isPrime_vanishingIdeal ringKrullDim_mvPolynomial_finite
  height_add_ringKrullDim_quotient_eq_card varietyDim height_vanishingIdeal_add_varietyDim_eq_card
  height_vanishingIdeal_eq_card_sub_varietyDim)
```
This re-aliases the short names into `DLNFibre.Core`, so every file transitively importing
`NullstellensatzCodim` (which is **all** current consumers — `varietyDim` is defined nowhere else, so
they already reach it) resolves the names unchanged. The decls genuinely live in `Core.Dimension`
(**name = content** honored); the export is a re-pointing, not a second definition. Verified no name
collisions (each of the 9 moved names is defined exactly once, in the source).

## Transitive-consumer sweep (L2 applied)
- Swept all 9 moved identifiers + `varietyDim` across **all** of `DLNFibre/`. Direct-importer set: 12
  files import `NullstellensatzCodim`; `varietyDim` reaches 22 files (most transitively, via
  `OrbitCodim`/`VarietyDimRadical`/`RadicalCatenary`). The `export` covers every one (full-build
  proof).
- **No stale fully-qualified refs:** `rg "DLNFibre\.Core\.(<moved name>)"` returns **nothing** — no
  file used the old `DLNFibre.Core.X` path that the move would have broken.
- **Aggregator** `DLNFibre.lean`: added `import DLNFibre.Core.Dimension.Codimension` directly after
  `Dimension.AffineDomain` (cohesive `Dimension.*` block, matching R3's placement), before
  `NullstellensatzCodim` (which imports it). Insertion only — no existing import reordered.

## Build / sorry / axiom status
- **Standalone `Codimension`:** green, 2123 jobs, **zero warnings** (longLine + unnecessarySimpa both
  cleaned).
- **Re-pointed `NullstellensatzCodim`:** green (warnings only in pre-existing other files —
  `OrbitCodim`, `RankPattern`, `DeformationExt` — not touched here).
- **Full aggregator** `./scripts/lb DLNFibre`: **GREEN, 3820 jobs** (= 3819 baseline + 1 new module).
  The L2 sweep caught every transitive consumer — nothing dropped, nothing broke.
- **`scripts/sorries`:** `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- **`#print axioms`** on `height_vanishingIdeal_add_varietyDim_eq_card` (bridge headline) =
  `[propext, Classical.choice, Quot.sound]`. Same for the weakened `vanishingIdeal_univ_eq_bot` and
  the DLN consumer `codimRepCanonical_eq_card_sub_varietyDim` (resolving through the export).

## R3 riders cleared (the bundled R3+R4 re-gate)
- **(a) 00OS/00P2 softening** in `Core/Dimension/AffineDomain.lean`: the headline docstring of
  `affine_domain_height_add_ringKrullDim_quotient_eq` now says the arbitrary-prime form is a
  **restatement** of 00OS (the verbatim displayed form is the maximal-ideal/equidimensionality
  corollary), with Codex's 00P2-as-closest-literal-tag note inline ("though none displays it
  exactly"). The `@[stacks 00OS]` **tag kept** (true and on-point), its quote shortened to
  `"restatement of equidimensionality as height p + dim (A ⧸ p) = dim A"`. The module docstring carries
  the same softening. Mirrored in `threads/05-affine-domain-catenary/statement-card.md` (its prose
  already matched; added an R4-follow-up note recording the docstring change).
- **(b) `longLine` warnings** in `AffineDomain.lean`: re-measured at the R4 re-gate — **zero** lines
  over 100 chars (R3's `f3670561` already reflowed them; the fresh `Codimension` build confirmed the
  `longLine` linter is genuinely active, so the clean measurement is not a cache artifact). No further
  reflow needed.

## Holes / surprises
- **No mathematical hole.** The core proof bodies are the source verbatim; the only logical change is
  the `vanishingIdeal_univ_eq_bot` hypothesis weakening (`[IsAlgClosed]`→`[Infinite]`, strictly more
  general, re-verified). The split is clean: the field-general core is free of `[IsAlgClosed]`
  (build-confirmed); nothing forced closure back in.
- **Surprise (minor, out of scope):** `DeepChartRing.lean`'s docstring (line 138) still says
  `vanishingIdeal_isRadical` is "over `[IsAlgClosed k]`" — a stale consumer-side echo of the same name=
  content slip the core just fixed. It is a **consumer** docstring (the brief said don't touch consumer
  hypotheses here; this is even lighter — just prose), so left for the RF rung when consumers are
  retrofitted. Flagged for RF.
- **`longLine` linter behavior:** the linter only fires on a **fresh elaboration**, not a cache
  replay — so a "clean" targeted rebuild of an already-built file can hide a longLine. The R4
  `Codimension` build (fresh) surfaced 4 longLines + 1 `unnecessarySimpa`, all fixed before wiring;
  the AffineDomain re-measure (manual codepoint count + the confirmed-active linter) is therefore
  trustworthy.
