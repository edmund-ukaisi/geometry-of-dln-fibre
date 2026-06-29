# Hardener — final cross-cutting sweep on the assembled dimension stack

**Function:** `hardener` (bedrock principles/taste, decorrelated). **Target:** the 7-module
`DLNFibre.Core.Dimension.*` library + its DLN retrofit, at `a0cbcf74` (+ doc) on
`expedition/dimension-stack`. **Method:** read-only (no build — re-gated green 3819, axiom-clean);
own-taste-first read of all 7 modules + consumer spot-checks + one decorrelated Codex (gpt-5.1-codex-max,
xhigh) consult on the assembled API. Per-rung fidelity/Codex reviews already PASSED; this is the
cross-cutting layer they structurally miss.

## Overall verdict: **SOLID-with-notes**

The stack is bedrock. The factoring is a clean acyclic 7-module DAG mirroring distinct Mathlib homes;
hypotheses on the library decls are minimal (no decorative `[IsAlgClosed]`/`[CharZero]`/`[Finite]`/
`[Fintype]`/`[DecidableEq]` binder anywhere — every such string is prose); the `@[stacks]` provenance
tags read honestly *together* with disclosed caveats; names denote content; the `[PerfectField]`
"clean-sufficient" framing is honest. The DLN consumers genuinely tag to the core (`varietyDim` used and
`unfold`ed, not duplicated; `codimRep_*` now `[Field k]`-only). **No blocking issue.** Findings below are
non-blocking polish + one structural "right extension" worth doing now.

---

## Area 1 — Overclaim / name = content (brief #1)

**SOLID-with-notes.**

- **`@[stacks 00OS]` appears on FIVE theorems** (Catenary: order/ideal/primeHeight forms of the
  polynomial-ring equality, lines 420/430/442; AffineDomain: three f.g.-domain restatements/corollaries,
  lines 137/184/200). The two bare-tagged Catenary forms (430, 442) **are** 00OS proper (polynomial-ring
  catenary) — correct. The three AffineDomain ones carry **disambiguating comment strings** and the
  module docstring (lines 33-41, 128-137) **openly discloses** that 00OS Lemma 10.114.4 states
  equidimensionality, that the arbitrary-prime headline is a *restatement*, and that "Codex notes 00P2 as
  the closest literal tag... though none displays it exactly." The Mathlib `@[stacks TAG "comment"]`
  attribute is built for exactly this disambiguation. **Verdict:** honest-with-co-located-caveat, the
  caveat sits next to the claim — *non-blocking*. Decorrelated Codex independently flagged this as
  "overstates provenance; the corollaries should cite a derived-corollary tag or drop it." I rate it
  *defensible-but-worth-polish*: a future Mathlib reviewer may prefer `00P2` on the arbitrary-prime form
  and a corollary tag (or bare `00OS` + "corollary" string) on the maximal-ideal ones. The docstring
  already self-documents the choice, so it is not a hole — **non-blocking polish.**
- **`00TV` forward-only** (Regular:196): tag string `"the smooth ⟹ regular direction (perfect base
  field gives separable residue fields)"` — names the exact direction of the iff and the role of
  perfectness. Co-located in the headline docstring. **Honest.**
- **`[PerfectField]` "weakest that compiles" framing: HONEST.** Confirmed via the 08 capstone audit's
  per-lemma trace (the lone field-theoretic input is `FormallySmooth.of_perfectField`, `[PerfectField]`
  + ess-finite-type, no `[IsAlgClosed]`) and the Regular.lean docstring (lines 50-58), which states
  `[PerfectField]` is *clean-sufficient* (per-residue-field separability is the true pointwise minimum)
  and does **not** claim an absolute theorem-minimum. Card does not overclaim.
- Names throughout denote content (`…isRegularLocalRing` not `…rlct…`; `…_le`/`…_eq` halves named
  separately; `injective_cotangent_cast` = `subst; exact`). No aspirational naming found.

## Area 2 — Vacuity / non-inhabitation (brief #2)

**SOLID-with-one-note.** Six of seven modules commit in-file `example` witnesses that the load-bearing
antecedents are satisfiable and the headline fires on a concrete nonzero target (Basic 1, Integral 1,
Catenary 4 — including the height-1 prime `(x)` exercising the non-degenerate case, AffineDomain 4,
Codimension 1 over `ZMod 2`-general, Smooth 3 — including `IsSmoothAt ℚ m` satisfiability + the bridge
firing).

- **`Regular.lean` has ZERO in-file witnesses** (the capstone module). The antecedent bundle
  `[PerfectField k] [IsSmoothAt k m] [FiniteType k A]` is inhabitable and cheaply: ℚ is `PerfectField`
  (`PerfectField.ofCharZero`), affine space `MvPolynomial (Fin d) ℚ` is finite-type and smooth
  everywhere, and `Smooth.lean` *already proves* `IsSmoothAt ℚ m` is satisfiable. Bedrock 2.1 wants the
  witness *shown in-file* for each new antecedent — an `example` exhibiting
  `IsRegularLocalRing (Localization.AtPrime m)` firing on a maximal ideal of `MvPolynomial (Fin 1) ℚ`
  would close it. **Non-blocking polish** (within reach — recommend doing now, ~6 lines).

## Area 3 — Factoring & namespace coherence (brief #3)

**SOLID-with-one-wart.** The 7 files form a clean acyclic DAG, one source file per eventual Mathlib home:

```
Basic, Integral        (roots)
Catenary  <- Integral, Basic
AffineDomain <- Integral, Basic, Catenary
Codimension <- Catenary
Smooth   <- Integral, Catenary
Regular  <- Smooth
```

No duplication across modules; no decl in the wrong module; AffineDomain's split from Catenary (distinct
f.g.-algebra home vs polynomial-ring home) is correct. Codex concurs ("maps cleanly to mathlib folders;
no merge pressure").

- **WART — nested `Ideal.` namespace.** `Smooth.lean:120,130` declare
  `theorem Ideal.height_eq_under_of_flat_quasiFiniteAt` and `theorem Ideal.height_eq_under_of_etale`
  *while inside* `namespace DLNFibre.Core.Dimension`, so the resolved full names are
  `DLNFibre.Core.Dimension.Ideal.height_eq_under_of_etale` — a nested `Ideal` sub-namespace under the
  project prefix that *looks like* it extends Mathlib's global `Ideal` namespace but does not. Other
  decls in the same file are plain (`fibre_height_eq_zero_of_quasiFiniteAt`,
  `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`). For the eventual file-move the **final** name
  `Ideal.height_eq_under_of_etale` is correct, but as it stands the hybrid is a discoverability/collision
  wart a Mathlib reviewer would query. Codex independently flagged it. Two honest options: (a) drop the
  `Ideal.` prefix → plain `height_eq_under_of_etale` in `DLNFibre.Core.Dimension` (consistent with its
  siblings), or (b) wrap in an explicit `namespace Ideal` block to make the intent legible. **Non-blocking
  polish.** (No consumer references the qualified path — safe to rename.)

## Area 4 — Minimal hypotheses on the Dimension decls (brief #4)

**SOLID.** No decorative typeclass on any library decl (grep-confirmed: all `IsAlgClosed`/`CharZero`/
`Infinite`/`Fintype`/`DecidableEq` strings are docstring prose). `[Finite σ]` (Codimension) is genuinely
used (`Fintype.ofFinite` + `Nat.card`). `[IsNoetherianRing R]` / `[IsDomain]` carried only where consumed.

- **Checked and REJECTED Codex's flag** that `height_under_eq_of_isIntegral` (AffineDomain:79-83)
  carries an unnecessary `[IsIntegrallyClosed R]`. It is **load-bearing**: the `≥` half is going-down,
  and Mathlib's `Algebra.HasGoingDown` instance for integral extensions
  (`IntegralClosure/GoingDown.lean:48`) requires `[IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S]
  [IsIntegrallyClosed R]` — going-down for integral extensions classically *needs* the base integrally
  closed (Stacks 00H8). Dropping it breaks the theorem. The hypothesis is minimal. (Codex's other
  generalization musings — "could generalize to any Noetherian catenary equidimensional base" — are
  genuine future-Mathlib scope, not holes in the stated polynomial-base theorems.)

## Area 5 — The right object / beauty + the right extension (brief #5)

**SOLID, with one structural extension worth doing now.**

- **`varietyDim` totalization (name = content nuance).** `Codimension.lean:127`,
  `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`, is **total** (defined for all `Z`),
  but every theorem about it requires `(vanishingIdeal Z).IsPrime`. On a reducible/empty `Z` the
  `.unbotD 0` fallback yields a value that *looks* dimension-theoretic but carries no proven meaning. The
  docstring (lines 123-126) does disclose the `⊥`-defaults-to-0 fallback. Codex flagged the
  totalization-vs-usage mismatch. This is a *mild* name=content nuance, **non-blocking** (the fallback is
  documented; a future Mathlib version might prefer a `WithBot ℕ∞`-valued def or an irreducibility-carrying
  argument). Note: the DLN consumer `RadicalCatenary` actually *does* handle reducible loci correctly via
  a separate general theorem (next bullet) — so the gap is cosmetic, not a downstream hazard.

- **★ RIGHT EXTENSION (recommend pulling in now).** `DLNFibre.Core.RadicalCatenary` (engine layer)
  contains `height_add_ringKrullDim_quotient_eq_card_of_ne_top [Finite σ] (I : Ideal (MvPolynomial σ k))
  (hIne : I ≠ ⊤) : I.height + ringKrullDim (R ⧸ I) = Nat.card σ` — the affine-space catenary identity for
  an **arbitrary proper ideal** (no primality, no radicality), **field-general**, fully **Tuple-free**. It
  is a strict, clean generalization of the Codimension module's prime-only
  `height_add_ringKrullDim_quotient_eq_card`, proved by a direct minimal-prime / chain squeeze on the new
  `Core.Dimension` catenary. This is exactly the reusable, network-free dimension fact the brief scopes as
  the deliverable, yet it sits *outside* `Core.Dimension`, one generalization step beyond the shipped
  headline. The *general* theorem needs neither `NullstellensatzCodim` nor `IsAlgClosed.AlgebraicClosure`
  (only the file's DLN-specialisation `codimRepCanonical_*` at the bottom does). **Recommendation:** re-home
  `height_add_ringKrullDim_quotient_eq_card_of_ne_top` (+ its two supporting bricks
  `exists_minimalPrime_height_eq_height`, `exists_minimalPrime_ringKrullDim_quotient_ge`, which are
  general Noetherian/`FiniteRingKrullDim` facts) into `Core.Dimension.Catenary` or `Codimension`, leaving
  the Tuple-coupled specialisation behind in `RadicalCatenary`. This (a) fills the "any proper ideal"
  generality the dimension headline already half-promises, (b) strips the closure import off the general
  theorem's path, (c) is the more beautiful object (drops the primality hypothesis the geometry never
  needed). *In-reach hardening — propose to do this in the close, not roadmap it.* (Caveat: confirm no
  import cycle — `Catenary` must not gain a `NullstellensatzCodim` dep; the general theorem's bricks are
  closure-free, so the re-home is clean.)

## Area 6 — Consumers genuinely tag to the core (brief #6)

**SOLID.** Spot-checked the retrofit:
- `NullstellensatzCodim` re-`export`s the field-general core (`varietyDim`, `IsZariskiClosed`,
  `vanishingIdeal_isRadical`, the catenary transport, the bridge) from `Core.Dimension` and keeps only
  the genuinely-`[IsAlgClosed]` non-vacuity layer + the `Tuple`-coupled `codimRep_*` specialisations. The
  `codimRep_add_varietyDim_eq_card` / `…_eq_card_sub_…` headlines now carry **`[Field k]` only** — the
  dead-weight `[IsAlgClosed]` shed (R4/RF).
- `VarietyDimRadical` / `VarietyDimBaseChange` use the core `varietyDim` directly (`unfold varietyDim`),
  not a bespoke duplicate.
- The old bespoke source modules are deleted/re-homed (`IntegralDimension`, `NoetherMonicPositioning`,
  `AffineDomainDimension`, `FlatQuasiFiniteHeight`, `SmoothLocalRelativeDimension`, `SmoothPointRegular`
  all gone). The surviving `PolynomialDimension` correctly retains only its **non-catenary** Noether-rank
  fact (`ringKrullDim_quotient_eq_noetherRank`) and tags to `Core.Dimension.{Integral,Basic}`.
- The remaining `[IsAlgClosed]`/`[CharZero]` on the DLN payoff (`RlctPayoff.lean`: orbit-ideal primality,
  cCodim bridge) are application-side and genuinely needed — out of scope for the Dimension sweep, not a
  stale duplicate.

---

## Blocking vs non-blocking summary

**Blocking the PR: NONE.**

**Non-blocking polish (recommend in the close):**
1. **★ Re-home `height_add_ringKrullDim_quotient_eq_card_of_ne_top` (+ 2 bricks) from `RadicalCatenary`
   into `Core.Dimension`** — the any-proper-ideal catenary, the right (more general, closure-free) object.
   *In-reach hardening; do it now.* (Area 5)
2. **Add a Regular.lean non-vacuity witness** — `example` exercising `smooth_point_isRegularLocalRing` on
   `MvPolynomial (Fin 1) ℚ` (bedrock 2.1; ~6 lines, antecedent already proven satisfiable in Smooth).
   (Area 2)
3. **Resolve the nested `Ideal.` namespace** in Smooth.lean (drop the prefix or wrap in `namespace Ideal`)
   for upstream discoverability. (Area 3)
4. **Optional, defer-able:** sharpen the AffineDomain corollary `@[stacks 00OS]` tags (00P2 / corollary
   string) — already self-documented, lowest priority. (Area 1)
5. **Optional:** `varietyDim` totalization — document or restrict; cosmetic given RadicalCatenary handles
   reducible loci. (Area 5)
