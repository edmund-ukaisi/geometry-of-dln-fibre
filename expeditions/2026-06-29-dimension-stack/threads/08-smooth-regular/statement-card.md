# Statement card — E2: smooth point ⟹ regular local ring (entry-2 capstone)

**Rung:** E2 (entry-2 capstone). **Thread:** 08-smooth-regular. **Branch:** `expedition/dimension-stack`.

## Module + Mathlib-mirror choice

- **Path:** `lean/DLNFibre/Core/Dimension/Regular.lean` (new file).
- **Namespace:** `DLNFibre.Core.Dimension`.
- **Mathlib mirror chosen:** `Mathlib.RingTheory.Smooth.Regular` / the regular-local-ring namespace
  `Mathlib.RingTheory.RegularLocalRing.*`. A **new file** (mirroring the prior-art choice E1 made for
  distinct Mathlib homes), not an extension of `Smooth.lean`, because the cohesive separation is real:
  `Smooth.lean` is the *dimension computation* (the non-circular local Krull-dim bridge, the étale
  height-preservation brick) whose Mathlib home is near `Etale/Smooth.Locus`; `Regular.lean` is the
  *regularity conclusion* built on it, whose Mathlib home is `RegularLocalRing`/`Smooth.Regular`. The
  capstone `smooth_point_isRegularLocalRing` carries the `@[stacks 00TV]` tag (the smooth ⟹ regular
  direction of the Stacks iff; the perfect-base-field hypothesis supplies the separable-residue-field
  condition the iff needs).
- **Re-homed from:** `Core/SmoothPointRegular.lean` (deleted — all content re-homed verbatim; git
  records it as a rename R, proofs byte-faithful, only namespace + docstrings + import set changed).

## Capstone headline (delivered)

All in `DLNFibre.Core.Dimension`.

- **`smooth_point_isRegularLocalRing`** `[PerfectField k]` `{k} [Field k] {A} [CommRing A] [Algebra k A]`
  `[Algebra.FiniteType k A]` `(m : Ideal A) [hm : m.IsMaximal] [IsSmoothAt k m] :`
  `IsRegularLocalRing (Localization.AtPrime m)` — `@[stacks 00TV]`. For `A` finite type over a perfect
  field `k` and `m` maximal at which `A` is smooth, the local ring `Aₘ` is a regular local ring.
- **`finrank_cotangentSpace_eq_of_isSmoothAt`** `[PerfectField k]` `(m) [m.IsMaximal] [IsSmoothAt k m]`
  `{n : ℕ} (hdim : ringKrullDim (AtPrime m) = n) : finrank κ(m) (CotangentSpace (AtPrime m)) = n` — the
  companion equality (cotangent finrank = local Krull dimension at a smooth closed point).

Supports (also re-homed, all `DLNFibre.Core.Dimension`):
- `injective_cotangent_cast` — conormal-map injectivity transports along an ideal equality.
- `finrank_kaehler_chart_eq` — on a standard-smooth chart, `finrank Ω[S⁄k] = n`.
- `finrank_cotangentSpace_le_of_isSmoothAt` `[PerfectField k]` — the cotangent comparison (the `≤`).
- `finrank_kaehler_localizationAtPrime_eq` — Kähler-rank transport chart → local ring (consumed by
  `FibreSmoothBlock.lean`).

## THE FLAGGED CRUX — `[IsAlgClosed] → [PerfectField]`: **`[PerfectField]` CONFIRMED**

**Surprise (benign), recorded honestly:** the brief's framing ("the source uses `[IsAlgClosed k]` only
to obtain `[PerfectField k]` … weaken the hypothesis") did **not** match the source state. The source
`Core/SmoothPointRegular.lean` was **already at `[PerfectField k]`** on all three headlines — the
`[IsAlgClosed]→[PerfectField]` weakening had been landed in a prior thread (commit `0084b645`,
rlct-bridge: "relax orbit-dim squeeze [IsAlgClosed]→[PerfectField], green over ℝ"); E1 re-homed the
*bridge* leaving the regular capstone in `SmoothPointRegular`. So E2's crux work was **verification**
that `[PerfectField k]` genuinely suffices (no step silently re-needs algebraic closure) + a name=content
cleanup, not a fresh weakening.

**Final hypothesis: `[PerfectField k]`** (alongside `[Field k]`, `[Algebra.FiniteType k A]`). Confirmed
**three ways**: (i) the file carried it; (ii) the **per-lemma trace** below shows exactly one
field-theoretic input, needing only perfectness; (iii) the green standalone build (2645 jobs) +
full-aggregator build (3819 jobs) with the **vestigial `import Mathlib.FieldTheory.IsAlgClosed.Basic`
dropped** (it was imported but no `IsAlgClosed`/`algClosure` symbol appeared in the body — confirmed by
grep, then by the build succeeding without it). name=content: the final hypothesis is the weakest that
compiles.

### Per-lemma trace (L1 — verified per-lemma, NO step re-needs `[IsAlgClosed]`)

| step | lemma in chain | field requirement |
|------|----------------|-------------------|
| 1 | `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` (E1) | `[Field k]` only — closed-point maximality via Zariski's lemma, **not** the residue-field-is-`k` Nullstellensatz (E1-confirmed) |
| 2 | `IsLocalization.isMaximal_of_isMaximal_disjoint`, `nontrivial_of_ne` | none (pure CA) |
| 3 | `finrank_kaehler_localizationAtPrime_eq` → `finrank_kaehler_chart_eq` | `[Field k]` (Kähler finiteness + localization transport) |
| 4 | `finrank_cotangentSpace_le_of_isSmoothAt` — the cotangent comparison | **`[PerfectField k]`** — the *single* field-theoretic input: `Algebra.FormallySmooth k (ResidueField R)` resolved by `inferInstance` → `Algebra.FormallySmooth.of_perfectField`, whose hypotheses are `[PerfectField K]` + `[EssFiniteType K L]` (both set up in-proof). `FormallySmooth.projective_kaehlerDifferential`, `kerCotangentToTensor_injective_iff`, `subsingleton_h1Cotangent` need no field beyond `FormallySmooth`. |
| 5 | `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`, `spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`, `iff_finrank_cotangentSpace` | none (pure local-ring theory) |

The base-field hypothesis enters at exactly **one** point (step 4, the residue field's formal smoothness
over `k`), and `Algebra.FormallySmooth.of_perfectField` (`Mathlib/RingTheory/Smooth/Field.lean:55`) needs
only `[PerfectField k]`. The smoothness *hypothesis* `[IsSmoothAt k m] = Algebra.FormallySmooth k (AtPrime m)`
(`Smooth/Locus.lean:46`, no field hypothesis) is **consumed, not produced** — so the smooth-locus density
`dense_smoothLocus_of_perfectField` (which callers use to *establish* `[IsSmoothAt]`) never enters this
chain.

**Conclusion: `[PerfectField k]` is exactly sufficient; `[IsAlgClosed]` is NOT re-needed by any step.**
Verified by trace AND by the green build with `IsAlgClosed.Basic` removed.

## Non-circularity reliance on E1 (preserved)

The local Krull dimension `dim Aₘ = n` is supplied entirely by E1's
`ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` (`Core.Dimension.Smooth`), computed via the
**étale-over-affine-space** route — **not** the cotangent/tangent identity. The capstone then squeezes the
cotangent finrank against that independently-computed `n` (the universal Krull bound `dim ≤ spanFinrank =
finrank cotangent`, plus the conormal injection giving `finrank cotangent ≤ n`). No circularity: the
dimension is an *input* from a route that never reads the cotangent space. `Regular.lean`'s only
`DLNFibre` import is `Core.Dimension.Smooth`, which is `[Field k]`-only (no closure), so the capstone's
dependency cone carries no `[IsAlgClosed]`.

## Transitive-consumer sweep (L2)

Re-pointed importers + verified all unqualified consumers `open … Dimension`; full-aggregator build is
the final arbiter (green, see below).

- **Direct importers of the deleted `SmoothPointRegular`** (3): aggregator `DLNFibre.lean` (line 33 →
  re-pointed to `import DLNFibre.Core.Dimension.Regular`, regrouped with its `Dimension.*` siblings after
  `Dimension.Smooth`), `OrbitTangentCotangent.lean` (line 5), `FibreSmoothBlock.lean` (line 4) — all
  re-pointed to `Dimension.Regular`.
- **Unqualified consumers of the re-homed decls** (L2 — the exact bite the lesson warns about):
  - `OrbitTangentCotangent.lean:629` uses `finrank_cotangentSpace_eq_of_isSmoothAt` unqualified → already
    has `open … Dimension` (line 34); resolves.
  - `FibreSmoothBlock.lean:109` uses `finrank_kaehler_localizationAtPrime_eq` unqualified → already has
    `open DLNFibre.Core.Dimension` (line 51); resolves.
  - No third unqualified consumer (full grep over the 5 re-homed identifiers: only these two files +
    `Regular.lean` itself).
- **Prose-only references** (not imports): `Smooth.lean:24` docstring said "lives in
  `DLNFibre.Core.SmoothPointRegular`, the entry-2 consumer" → updated to
  `DLNFibre.Core.Dimension.Regular`, the entry-2 capstone".
- **Full grep over all of `lean/`** (incl. comments/configs, excl. `.lake/`): **zero** stray references
  to the old module name `SmoothPointRegular` remain.

## Build / sorry / axiom status

- **Build:** `./scripts/lb DLNFibre` (full aggregator) **green — 3819 jobs** (job-count-neutral vs the E1
  baseline 3819 — a re-home, not new content). `Dimension.Regular` builds standalone (2645 jobs).
- **Sorries:** `scripts/sorries` = **0 sorry, 0 #exit, 0 native_decide, 0 axiom**.
- **`#print axioms`** = **`[propext, Classical.choice, Quot.sound]`** for both
  `smooth_point_isRegularLocalRing` and `finrank_cotangentSpace_eq_of_isSmoothAt`.

## Holes / surprises / flags for decorrelated review

- **No mathematical hole** — verbatim re-home, all gates clean.
- **Surprise (benign, central):** the crux weakening was *already landed upstream of E2* (prior
  rlct-bridge thread); E2's value is the verification + name=content cleanup + the upstream-grade re-home,
  not a fresh weakening. The brief's framing assumed the source still carried `[IsAlgClosed]`; it did not.
  The conclusion (`[PerfectField]` suffices, `[IsAlgClosed]` not re-needed) is unchanged and now
  independently re-verified by the per-lemma trace + the green build with the vestigial closure import
  dropped.
- **Flag for review (low-confidence, routing suggestion):** the `@[stacks 00TV]` tag is for the Stacks
  *iff* (smooth at q ⟺ Sq regular, under residue-field separability). Our theorem proves the **forward**
  direction (smooth ⟹ regular) only, with `[PerfectField k]` supplying separability. The tag + its string
  description ("the smooth ⟹ regular direction") name exactly the direction proved — but a reviewer should
  confirm the harness's `@[stacks]` convention is comfortable tagging a one-direction theorem with an
  iff-tag (Mathlib does this routinely; flagged for completeness).
- **`[IsAlgClosed]` downstream (NOT in scope, NOT a hole):** `FibreSmoothBlock.lean` retains
  `[IsAlgClosed]` on `fibre_smoothBlock_certificate` / `exists_isSmoothAt_isMaximal_component` etc. —
  these are *consumers* of the capstone (DLN application), not dependencies, and their `[IsAlgClosed]` is
  genuine geometric/Nullstellensatz use, properly RF (retrofit) territory per the priorities ledger, not
  E2.
