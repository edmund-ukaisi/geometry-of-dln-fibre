# Resolution-atlas statement card — `IsResolutionAtlas` + `resolution_value_of_atlas` (R1.6 obligation + value)

- **Seat:** `cover` (R1 cover lane). Task #21 — the #133 obligation card formalised: the R1.6
  cover-exhaustiveness pinned as a Lean structure + the value consequence proven over it.
- **Module:** `lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean` (206 LoC, imports only `Skeleton`).
  Branch `cover/resolution-atlas-scaffold` (off `origin/fm/r1-cover @26eccac`). NOT wired into
  `DLNFibre.lean` — controller wires.
- **Status.** sorry-free; `resolution_value_of_atlas` is **clean-three / S2-free** (`#print axioms` =
  `[propext, Classical.choice, Quot.sound]` — no `monomial_rlct`); the structure is non-vacuous (a
  concrete `M = ![1,1]` atlas exhibited in-file).
- **Source:** pp2's `g133-resolution-atlas-obligation-CARD.md` (consumed verbatim; the SURJECTION-not-
  bijection fidelity correction respected).

---

## The obligation

> **Claim (R1.6 atlas obligation, #133).** The (C2) resolution's chart-tree data `(d, k, h)` over its
> root-to-leaf paths `ι`, plus a `stratum` tag (each path's binding min-codim rank stratum), satisfies:
> (A) every binding center is an admissible rank stratum; (S) every admissible stratum is reached by
> some path (exhaustiveness); (K) `k_E = 1` on every exceptional divisor; (C) per-path threshold
> `= ½·(binding stratum's codim)`.

- **Lean:** `IsResolutionAtlas (M) (ι) [Fintype ι] (d) (k h) (stratum) : Prop` — 4 conjuncts
  `stratum_admissible` / `stratum_surjective` / `mult_one` / `threshold_eq`.
- **Gloss.** The data witnessing that the resolution's pivot-tree charts (i) all sit over admissible
  rank strata, (ii) collectively reach every stratum, (iii) are multiplicity-1 regular-sequence
  divisors, (iv) each have monomial threshold equal to half their binding stratum's codimension.
- **Proved.** The structure type-checks and is **non-vacuous** — an `example` builds it for
  `M = ![1,1]` (`Adm = {0}` by `decide`, `Mval 0 = 1`, the one-path `d=1,k=![1],h=![0]` atlas),
  so the four conjuncts are jointly satisfiable and `resolution_value_of_atlas` then returns `½`.
- **Cited.** `monomial_rlct` (S2) — only inside the (C) `threshold_eq` field and the non-vacuity
  `example`'s threshold computation; NOT in the value lemma's own proof.
- **Deferred (the single open obligation):** **(S) `stratum_surjective`** — the cover-exhaustiveness.
  Carried as an explicit `Prop` field (NOT a buried sorry), so any concrete atlas must discharge it.
  Being adjudicated (pp2 witness / pp3 obstruction over `Core.RankPattern`/Gabriel); formalises after
  they reconcile. (A)/(K) are structural/#132-certified; (C) rests on #131 Schur codim +
  `axisRatio_regularSeq` (green) + S2.

---

## The value consequence

> **Claim.** Given a resolution atlas, `⨅ monomialThreshold = ofReal(lambdaCore M)`.

- **Lean:** `resolution_value_of_atlas (M ι [Fintype ι] d k h stratum)
  (hatlas : IsResolutionAtlas …) : ⨅ i, monomialThreshold (d i)(k i)(h i) = ENNReal.ofReal (lambdaCore M)`.
- **Gloss.** The image of `stratum` is exactly `Adm M` (A: ⊆, S: ⊇), so the `⨅`-over-paths of
  `½·Mval(stratum)` is `½·min_{T∈Adm} Mval = lambdaCore M`. The `le_antisymm` rearrangement: `≤` from
  the achiever path (the `inf'` minimiser reached by S), `≥` from every center being admissible (A).
- **Proved.** SORRY-FREE and S2-FREE (clean-three). S2 enters only through `hatlas.threshold_eq`,
  the cover-supplied hypothesis — the value lemma's own logic is pure `⨅`/`Finset.inf'` arithmetic.
- **Why S is load-bearing.** The `≤` direction needs the minimiser stratum reached; without (S) the
  `⨅`-image could miss it and over-estimate (the incomplete-cover failure). This is exactly where
  surjectivity bites.

### Supporting lemmas (in-file, sorry-free)
- `Mval_nonneg_adm` — `0 ≤ Mval M T` on `Adm M` (local re-proof; the Skeleton facts are `private`).
- `ofReal_lambdaCore_eq_half_inf` — `ofReal(lambdaCore M) = ½·((Adm M).inf' Mval).toNat` (the
  definitional bridge; uses `inf' ≥ 0` so `.toNat` round-trips).

---

## Scope (CLAUDE.md precision)

**Core-only:** `rlctAtOn(dlnLoss M 0) 0`, `M = H − r` the reduced widths. The regular
`[−r²+r(H⁰+Hᴸ)]/2` shift is L2/Fubini (`product_reduction`), NOT here — `IsResolutionAtlas` carries no
`nReg`.

## Wiring (controller)

`resolution_value_of_atlas` + `GeneralR1Value.core_rlct_eq_lambdaCore_of_resolution` (the value seam,
already on `fm/r1-cover`) are the two halves: the latter takes `hres = ⨅ monomialThreshold` (=
`resolution_charts`'s conclusion) and the g35 bracket; this lemma DERIVES `⨅ monomialThreshold =
ofReal(lambdaCore)` from an atlas. So an atlas instance + `resolution_value_of_atlas` discharges
`resolution_charts` directly (modulo the still-open (S)). The remaining geometric work is producing
the atlas INSTANCE (the chart-tree construction + the (S) surjectivity proof).
