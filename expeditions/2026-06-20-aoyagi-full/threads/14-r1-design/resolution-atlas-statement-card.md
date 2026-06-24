# Resolution-atlas statement card — `IsResolutionAtlas` + `resolution_value_of_atlas` (R1.6 obligation + value)

- **Seat:** `cover` (R1 cover lane). Task #21 + #34 — the #133 obligation card formalised, then
  SHARPENED to the #134 (S-min) form: the R1.6 cover-exhaustiveness pinned as a Lean structure + the
  value consequence proven over it.
- **Module:** `lean/DLNFibre/DLN/RLCT/Validate/ResolutionAtlas.lean` (244 LoC, imports only `Skeleton`).
  Branch `cover/resolution-atlas-value`. NOT wired into `DLNFibre.lean` — controller wires.
- **Status.** sorry-free. `resolution_value_of_atlas` is **clean-three / S2-free** (`#print axioms` =
  `[propext, Classical.choice, Quot.sound]` — no `monomial_rlct`); the structure is non-vacuous (a
  concrete `M = ![1,1]` atlas, `isResolutionAtlas_M11`, exhibited in-file). (The #133 4-conjunct form
  was fidelity-reviewed 6/6 PASS + Codex sound-conditional; the #134 S-min restatement below is a
  strictly cleaner equivalent — re-review pending.)
- **Source:** pp2's `g133-resolution-atlas-obligation-CARD.md` + the `g134-surjectivity-witness-SKETCH.md`
  (S-min sharpening: SURJECTION-not-bijection, and only the MINIMISER need be reached).

---

## The obligation (S-min form, #134)

> **Claim (R1.6 atlas obligation, S-min).** The resolution's chart-tree data `(d, k, h)` over its paths
> `ι` satisfies the two clauses `le_antisymm` consumes, both keyed to `m₀ = min_{T∈Adm} Mval(T)`:
> (C≥) every path's monomial threshold is `≥ ½·m₀`; (C=∃) some path realises `= ½·m₀`.

- **Lean:** `IsResolutionAtlas (M) (ι) [Fintype ι] (d) (k h) : Prop` — two clauses `threshold_ge`
  (`∀ i, (m₀.toNat)/2 ≤ monomialThreshold (d i)(k i)(h i)`) and `achiever`
  (`∃ i, monomialThreshold (d i)(k i)(h i) = (m₀.toNat)/2`), with `m₀ = (Adm M).inf' Mval`.
- **Gloss.** Every chart's RLCT is at least half the minimal codimension (no undershoot), and one chart
  realises it exactly (no over-estimate) — so the `⨅` over charts is exactly `½·m₀ = lambdaCore M`.
- **Constructor.** `IsResolutionAtlas.of_mult_and_achiever` builds the atlas from the underlying
  certified geometry: a uniform multiplicity bound `m₀·(k i j) ≤ h i j + 1` (K `k=1` + A admissibility
  ⟹ C≥ via `monomialThreshold_ge_of_mult'`) + one achiever path with a binding divisor
  `(k i₀ j₀, h i₀ j₀) = (1, m₀−1)` (⟹ C=∃ via `monomialThreshold_le_regularSeq`). Shows the two clauses
  are honestly DERIVED, not assumed.
- **Proved.** The structure + constructor type-check and are **non-vacuous** — `isResolutionAtlas_M11`
  builds the atlas for `M = ![1,1]` (`m₀ = (inf' Mval).toNat = 1` by `decide`; one chart
  `d=1,k=![1],h=![0]`, `monomialThreshold = ½`), and `resolution_value_of_atlas` then returns
  `ofReal(lambdaCore ![1,1]) = ofReal(½)` end-to-end (shown in-file).
- **Cited.** `monomial_rlct` (S2) — only inside the per-chart bracket lemmas (`monomialThreshold_ge_of_mult'`,
  `monomialThreshold_eq_half_of_binding`) the constructor + non-vacuity witness invoke; NOT in the value
  lemma's own proof.
- **Deferred (the single open obligation):** **(C=∃) `achiever`** = (S-min): SOME path realises `½·m₀`,
  i.e. the binding branch through a MINIMISING stratum exists. Strictly WEAKER than full surjectivity
  onto `Adm M` (only the minimiser need be reached — pp2 #134). Carried as an explicit `Prop` field /
  constructor hypothesis (NOT a buried sorry). The minimiser is the top-dimensional (min-codim) stratum,
  reached at DEPTH (e.g. (2,2,2): the rank-1 incidence stratum codim-3 at depth 2, not the trivial first
  chart). Formalises after pp2's general construction design lands; carrier `Core.OrbitKostant`
  (`baseChange_normalForm`) + the DLN chart construction's binding branch.

---

## The value consequence

> **Claim.** Given a resolution atlas, `⨅ monomialThreshold = ofReal(lambdaCore M)`.

- **Lean:** `resolution_value_of_atlas (M ι [Fintype ι] d k h)
  (hatlas : IsResolutionAtlas …) : ⨅ i, monomialThreshold (d i)(k i)(h i) = ENNReal.ofReal (lambdaCore M)`.
- **Gloss.** Pure `le_antisymm`: (C≥) `threshold_ge` ⟹ `⨅ ≥ ½·m₀` (`le_iInf`); (C=∃) `achiever` ⟹
  `⨅ ≤ ½·m₀` (`iInf_le`); then `½·m₀ = ofReal(lambdaCore M)` definitionally
  (`ofReal_lambdaCore_eq_half_inf`, since `lambdaCore := ½·inf' Mval`).
- **Proved.** SORRY-FREE and S2-FREE (clean-three, `#print axioms` verified). S2 enters only through the
  atlas's clauses (`threshold_ge`/`achiever`, cover-supplied) — the value lemma's own logic is a
  three-line `le_antisymm` + the definitional `lambdaCore` bridge.
- **Why the achiever is load-bearing.** The `≤` direction needs SOME path realising `½·m₀` — i.e. the
  minimiser reached. Without it the `⨅` could exceed `½·m₀` and over-estimate (incomplete-cover failure).
  This is exactly the (S-min) content; full surjectivity is more than the value needs.

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
on `fm/r1-cover`) are the two halves: the latter takes `hres = ⨅ monomialThreshold` (=
`resolution_charts`'s conclusion); this lemma DERIVES `⨅ monomialThreshold = ofReal(lambdaCore)` from an
atlas. So an atlas instance + `resolution_value_of_atlas` discharges `resolution_charts` directly (modulo
the still-open `achiever`/(S-min)). The remaining geometric work is producing the atlas INSTANCE (the
chart-tree construction + the (S-min) achiever-path proof).

**Branch note:** this lane is on `cover/resolution-atlas-value` (the value-seam-parented
`cover/resolution-atlas-scaffold` was clobbered by a name collision with fm2's per-node lane — see the
controller-flagged collision; this branch is parented on `g129-r1-squeeze-verdict @5dd5231`, so the
`GeneralR1Value` lemmas are RE-INLINED here as `monomialThreshold_ge_of_mult'` /
`monomialThreshold_eq_half_of_binding` to keep the module self-contained on `Skeleton`).
