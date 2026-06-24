# Design certificate — #135 general-M cover/completeness for the `routeStep` dispatcher

**Seat:** `pen-and-paper` (CONSTRUCT, design-before-lines). **Date:** 2026-06-24.
**Gate:** the R1.6 mountain — the general-M rank-pattern READ producer (`RouteMBranchRead M₀ M` for
arbitrary non-leaf `M`) + the cover/completeness proof that the chart family folds to `½·minAdm` without
over- or under-estimating the RLCT (the LOWER bound, where the headline equality's `≥`-leg lives).
**Method:** assessment of the banked Lean cover→value chain; exact integer enumeration of the branch
lattice (no float); one decorrelated `local-codex-consult` (gpt-5-codex, xhigh, conclusion withheld).
**Artefacts:** `/tmp/check_telescope.py` (Adm/minAdm enumeration), `/tmp/check_branching.py` (the
paths↔Adm bijection + codim=Mval certificate), `/tmp/check_increment.py` (the single-peel vs block-codim
check). Codex: `/tmp/codex_135_prompt.md`, `/tmp/codex_135_answer.md`.

---

## VERDICT: completeness is REACHABLE; the cover's two legs are ASYMMETRIC — the hard half is banked

The #135 gap is **not** a symmetric "prove the chart family covers a neighbourhood of the origin"
surjectivity statement. The Lean architecture has already split it so that:

- the **lower bound** `(C≥)` (no missed *smaller* / worse divisor) is **automatic** from the
  `PivotWitness M₀` field via `minAdm_le_Mval_toNat` — proven, no surjectivity needed;
- the **upper bound** `(C=∃)` (the achiever binds) needs only the **minimiser** reached (the S-min
  sharpening), and that realizability tie `rankFn (cascadeTuple M₀ T*) = achieverRankPattern M₀ T*`
  is **already proven on-branch** (`CascadeAchiever.lean:145`).

What genuinely remains open in `routeStep` (`RouteMRecursion.lean:223`) is purely the **constructive
rank-pattern READ**: emitting, for arbitrary non-leaf `M`, the finite cell family + per-cell
`PivotWitness M₀`. The completeness *proof obligations* are banked; the read is *construction*, not a
new theorem. So: **not walled** — a precise, transcribable spec follows.

---

## 1. The banked cover→value chain (assessment — PROVEN GIVEN an atlas)

The chain `read → ⨅ monomialThreshold = ½·minAdm = lambdaCore` and `rlctAtOn(core) = ⨅ monomialThreshold`
is **proven, conditional only on the read**:

| link | file:thm | status |
|---|---|---|
| `IsResolutionAtlas ⟹ ⨅ = ofReal(lambdaCore)` | `ResolutionAtlas.lean:197` `resolution_value_of_atlas` | PROVEN, S2-free |
| `IsRouteMCover ⟹ rlctAtOn F 0 = ⨅ monomialThreshold` | `RouteMBridge.lean:79` `routeM_rlctAtOn_eq_iInf` | PROVEN (abstract cover) |
| `PivotWitness-family + achiever ⟹ ⨅ = ½·minAdm` | `RouteMState.lean:356` `foldFamily_iInf_eq_half_minAdm` | PROVEN |
| value-fold over `routeMIota` | `RouteMValue.lean:42` `routeM_value_eq` → `RouteMGeneralAssembly.lean:35` | PROVEN (conditional on read's hyps) |
| flat-coord extraction (the `F`/`U`/`N` the bridge needs) | `RouteMExtraction.lean` | PROVEN |
| per-node descent split `rlct = nReg/2 + rlct(reduced)` | `GeneralR1Recursion.lean:368` `schur_recursion_step_squeeze` | PROVEN (two-sided squeeze, no chart) |
| the realizability tie (the `(C=∃)` discharge) | `CascadeAchiever.lean:145` `rankFn_cascadeTuple_eq_achieverRankPattern` | PROVEN, non-vacuous on `(1,1,1,2,1)` |

**The ONLY load-bearing `sorry` in the whole chain** is `routeStep`'s branch arm
(`RouteMRecursion.lean:223`). `ResolutionAtlas` / `GeneralR1Recursion` / `RouteMGeneralAssembly` have
**zero** real sorries (their `grep 'sorry'` hits are doc-text). `RouteMGeneralAssembly.routeMGeneralValue`
carries only *inherited* `sorryAx` transitively (its statement is over `routeMIota`, which reduces through
`routeAtlas → routeStep`); it clears the moment the branch arm is filled.

The concrete `(2,2,2)` cover atoms (`Case222RouteMCover.lean`) are fully proven — the worked template the
general-M `cover_le`/`cover_ge_div` generalize, via `RouteMCoverLemmas` (finiteness atom + box-divergence
atom).

---

## 2. The read producer — explicit cell enumeration + per-cell witness

**The branching mechanism (load-bearing, exact-certified).** At a non-leaf node `M`, branch on the rank
`t₁ ∈ {0, 1, …, min(M₀,M₁)}` the **leading pivot drops to at the first edge** (Aoyagi Case 1 partial-block
vs Case 2 full-block). Recurse with the *surviving rank* `t₁` as the incoming width feeding edge 2; the
next branch chooses `t₂ ≤ min(t₁, M₂)`, etc. (weakly-decreasing automatically).

I verified by **exact integer enumeration** (`/tmp/check_branching.py`, six cases incl. the
intermediate-pinch `(5,1,3,1)`):

- **root-to-leaf paths biject with `Adm(M)`** (bijection `True` on all 6 cases), and
- **accumulated codim down a path = `Mval(M, T)`** for the assembled `T` (`True` on all 6),

| `M` | `minAdm` | argmin `T*` | `\|Adm\|=\|paths\|` | codims over `Adm` |
|---|---|---|---|---|
| `(2,2,2)` | 3 | `(1,0)` | 3 | `{3,4}` |
| `(3,2,3)` | 5 | `(1,0)` | 3 | `{5,6}` |
| `(3,3,4)` | 8 | `(1,0)` | 4 | `{8,9,12}` |
| `(4,4,2,2)` | 4 | `(4,2,0)` | 12 | `{4,5,7,8,11,16}` |
| `(2,2,4)` | 4 | `(0,0)` | 3 | `{4,5,8}` |
| `(5,1,3,1)` | — | — | 3 | (bijection holds incl. intermediate pinch) |

So the cell family is indexed by `Adm(M)`, and the per-cell codim is the genuine geometric `Mval(M,T)`.

### The per-cell construction for `RouteMBranchRead M₀ M`

- `cells` := the admissible leading-pivot ranks `t₁ ∈ {0,…,min(M₀,M₁)}` (a `Fin`-indexed finite set,
  nonempty: `t₁=0` always admissible).
- `codim t` := **the edge-1 Case-2 block exponent** `(M₀ − t)(M₁ − t)` — read DIRECTLY off the blow-up
  centre, NOT iterated from single peels (the subtlety in §3).
- `split t` := `schurState M …` — the **width carrier** (the single-pivot peel `(M₀−1, M₁−1, M₂,…)`);
  the recursion descends `chainRel` on `split.red` via `redM_chainRel`. (See §3 — `schurState` is the
  *unit* width-reduction step; the branch `t₁=t` is reached by `t` such steps + one Case-2 collapse, but
  the **codim is the block exponent**, not the step count.)
- `witness t : PivotWitness M₀ (codim t)` := `⟨T*, hAdm, hCodim⟩` with `T*` the admissible vector
  assembled along the path (`T*₁ = t`, recurse); `hAdm : T* ∈ Adm M₀` (**root-anchored** — load-bearing,
  prevents the reduced-state minAdm undershoot, `RouteMValue.lean` §root-anchoring); `hCodim : codim =
  (Mval M₀ T*).toNat`.

---

## 3. Completeness / the cover — the LOWER bound, where it lives (the asymmetric split)

Codex (decorrelated) framed completeness as a single symmetric surjectivity ("every valuation dominating
the origin factors through one of the enumerated charts"). For THIS architecture it splits
**asymmetrically**; that split is the correction that makes #135 reachable.

### `(C≥)` — no-undershoot (no missed *smaller* divisor): PROVEN, automatic

`minAdm M₀ = inf_{T∈Adm M₀} Mval M₀ T`, so EVERY `PivotWitness`-certified cell has
`codim = Mval M₀ T ≥ minAdm` by `Finset.inf'_le` (`minAdm_le_Mval_toNat`, `PivotWitness.minAdm_le`). A
wrong dispatcher CANNOT undershoot the binding value — it can only over-emit non-binding cells (caught by
the cover `≤`-leg). **This is the half Codex feared needs a coverage/surjectivity statement; it does
not** — because every emitted cell is *constructively* an admissible `Mval`, the `⨅` over the family is
bounded below by `minAdm` by the inf-property alone. No "every point is in some chart" statement enters
the `≥`-leg. The per-divisor multiplicity-1 propagation is `monomialThreshold_appendDivisor_ge` (each
axis `(k,h)=(1,codim−1)`, regular sequence, `axisRatio = codim/2 ≥ ½·minAdm`).

### `(C=∃)` — achiever (no over-estimate): the genuine completeness content, S-min, PROVEN tie

The `⨅` does not OVERESTIMATE iff SOME leaf realizes `= ½·minAdm`. Only the **minimiser** `T*` (argmin of
`Mval M₀`) need be reached — strictly weaker than full surjectivity onto `Adm(M)`. The geometric "this
chart path is genuinely reached, not vacuously satisfied" is exactly
`rankFn (cascadeTuple M₀ T*) = achieverRankPattern M₀ T*`, **proven** (the H1/H2/H3 monotonicity collapse,
`CascadeAchiever.lean`; non-vacuous on the property-breaker `(1,1,1,2,1)`). The achiever leaf `i₀` with
`minAdm ∈ codimsOf i₀` is supplied by `RealizesAchiever.ofAdm` (`RouteMAchieverForce.lean`).

### Q3 (multiplicity-1 per divisor): discharged by the proven per-node squeeze, by induction

The per-node squeeze identity `rlct = nReg/2 + rlct(reduced)` (`schur_recursion_step_squeeze`, PROVEN — a
two-sided `c₁·Φ ≤ F ≤ c₂·Φ`, NO chart/Jacobian) gives the EXACT contribution per node; the centre is the
regular block the squeeze certifies. Composed down a path it IS the multiplicity control over the complete
resolution Codex asked for — no gap, because each node's centre is a regular sequence by construction
(`appendDivisor` sets every pivot axis to `(1, codim−1)`). The disjoint-variable additivity
(`rlct(reg block) + rlct(reduced)`) is the standard Watanabe product rule, used soundly.

### Where completeness GENUINELY walls (the honest scope)

Completeness is reachable for the **combinatorial `½·minAdm` headline** because the achiever leg needs
only the minimiser and the tie is proven. It would wall if one demanded the **full geometric reading**
(every interior stratum's codim = its Ext-codim) for general non-width-monotone `M` — there the
`achieverRankPattern` (column-constant completion `ρ_j`) differs from the `Mval`/multSum pattern
`ρ_j + (M_i − ρ_i)` at interior cells (flagged in `RouteMNodeDescent.lean`'s naming caveat,
pp-rstar #136). That is a **scoped, deferred extension (width-monotone `M`)**, NOT what the binding
headline needs. **Keep the levels separate:** the cover proves `rlctAtOn(core) = ½·minAdm`; the
`rlct = ½·codim` *geometric* reading rides the cited Aoyagi/Watanabe analytic bound, unchanged.

---

## 4. The fold — already PROVEN given the read

`foldFamily_iInf_eq_half_minAdm` (`RouteMState.lean:356`) consumes exactly: `hwit` (per-cell
`PivotWitness`, the `(C≥)` discharge), `i₀`/`hbind₀` (the achiever, the `(C=∃)` discharge), `hdata` (the
`appendDivisor` accumulation the recursion threads). `le_antisymm` of the `(C≥)` lower bound (`le_iInf` of
`foldFamily_threshold_ge_of_pivotWitness`) and the achiever upper bound (`iInf_le` at `i₀`,
`foldFamily_achiever`). The bridge `routeM_rlctAtOn_eq_iInf` lands `rlctAtOn(core) = ⨅ = ½·minAdm =
lambdaCore`.

---

## 5. Caveats next to claims, scope, the one thing most likely to break it

- **Proved vs exact-certified vs banked vs inferred.**
  - *Banked (Lean, sorry-free given an atlas):* the entire cover→value chain (§1 table).
  - *Exact-certified (integer enumeration, 6/6):* the branch lattice bijects with `Adm(M)`,
    accumulated codim `= Mval(M,T)` (`/tmp/check_branching.py`); `minAdm`/argmins (`/tmp/check_telescope.py`).
  - *Proved (Lean):* the per-node squeeze (Q3), the realizability tie (`(C=∃)`), the no-undershoot
    discharge (`(C≥)`).
  - *Decorrelated-confirmed:* Codex (conclusion withheld) independently reached the
    surjectivity-vs-S-min structure (it framed it symmetrically; the asymmetric split above is the
    architecture-specific refinement). It also confirmed the single-path squeeze descent alone does NOT
    give the lower bound (Q4) — the branching/min-over-Adm is necessary.
- **The single-peel vs block-codim subtlety (most likely thing to break the transcription).**
  `schurState M = (M₀−1, M₁−1, M₂,…)` peels ONE rank per step; the branch `t₁=t` corresponds to `t`
  peels + one Case-2 collapse. The dispatcher must emit `codim = (M₀−t)(M₁−t)` (the **block exponent**)
  per cell — a per-peel codim count would undershoot (`/tmp/check_increment.py`: `(2,2)` edge-1 codims by
  `t₁` are `[4,1,0]`, NOT `[2,1,0]`). The `t₁=min(M₀,M₁)` cell has edge-1 codim `0` (clean full-rank
  pass-through, NO divisor — appends nothing, recurses on the surviving rank). This is the SAME
  conflation class the certified `verify-r1-diagb-334.md` obstruction identified (a per-row multiplicity
  loses the sharing identity, computing the wrong RLCT) — defused here because `codim = Mval M₀ T` is
  encoded once, globally, root-anchored, never re-derived per-row.
- **Levels kept separate.** This certificate is about the **cover/read mechanism + the combinatorial
  core value `½·minAdm`**. The geometric `rlct = ½·codim` reading is unchanged (cited bound).

---

## 6. Close — for the formaliser hand-off

- **Firmest result:** the general-M cover is complete and reachable. Cell family (branch on leading-pivot
  rank drop) bijects with `Adm(M)`, per-path codim `= Mval(M,T)` (exact, 6/6). The two completeness legs
  are asymmetric: `(C≥)` automatic from `PivotWitness`+`inf'_le`; `(C=∃)` needs only the minimiser,
  proven by the on-branch tie. The remaining `routeStep` `sorry` is the constructive READ, not an open
  theorem.
- **Most likely to break it:** the `schurState` single-peel vs Case-2 block-codim mismatch — emit
  `codim = (M₀−t)(M₁−t)` per cell, thread the achiever's root-anchored `T*` so `hCodim` matches at depth.
- **Next construction (the formaliser's leaf):** implement `cells := admissible t₁` + the path-assembled
  `T*` constructor in `RouteMBranchRead`; prove the bijection `paths ↔ Adm(M)` and `accumulated codim =
  Mval M₀ T*` in Lean (the exact-certified combinatorial lemma `/tmp/check_branching.py` is the
  spec). The geometric `cover_le`/`cover_ge_div` for general `M` generalizes the `Case222RouteMCover`
  atoms via the proven per-node squeeze descent — the next formalisation lane, NOT a pen-and-paper wall.
