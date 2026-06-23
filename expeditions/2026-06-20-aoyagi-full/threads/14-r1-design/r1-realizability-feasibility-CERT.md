# R1 §4 stratum-coverage realizability — feasibility ADJUDICATION (pp, decorrelated, 2026-06-23)

- **Seat:** `pen-and-paper` (decorrelated). **Direction:** obstruction (scope the no-go / minimal-gap)
  + witness (the in-reach lemma chain where it holds). NO Lean edits.
- **Question gated:** is general-M §4 realizability (the `routeStep` dispatcher honestly producing, per
  branch cell, a `PivotWitness M₀ (codim c)` GENUINELY reached by a legal chart path) provable from
  EXISTING machinery, or does it need new theory — and if so, exactly what and how large?
- **Decorrelation:** my exact-algebra checks (`/tmp/check_codim_compose.py`, `check_path_codim.py`,
  `check_branch_needed.py`, `check_codim_additivity.py`) + a hypothesis-withheld Codex consult
  (`codex/r1-realizability-feasibility-{prompt,answer}.md`, VERDICT: IN-REACH achiever-only). Converged.

## VERDICT (one line)

**IN-REACH for the VALUE/headline (achiever-only), via `foldFamily_iInf_eq_half_minAdm` — NOT via
`IsResolutionAtlas`. The single residual is a DLN-chart-combinatorics gap (formaliser-scale, gated on
ONE analytic interface), NOT new Core orbit-Kostant theory.** The honest deliverable shape this implies
is below in §6.

## 1. The brief's decl-survey claim is WRONG — Core HAS the orbit-Kostant layer (re-grade)

The brief asserts `git grep "OrbitKostant\|baseChange_normalForm" fm3/routem -- lean/DLNFibre/Core/`
returns nothing. That is a grep-quoting artefact. Decl-first, on `fm3/routem`:
- `Core/OrbitKostant.lean`: `orbitKostantEquiv`, `orbitKostantPartitionEquiv`, `realizer`,
  `kostantArrayOfRank_rankFn_realizer`, `cMPlus_iff_mem_image` (full realizability ↔ CMPlus).
- `Core/Orbit.lean:340`: `baseChange_normalForm` (Gabriel normal form, cast-free).
- `Core/OrbitClosure.lean`: the Abeasis–Del Fra orbit-CLOSURE order (`boxMoveChain_repClosure_subset`,
  `canonicalCoord_mem_repClosure_orbitSet`).
- `Core/OrbitCodim.lean:195`: **`codimRepCanonical_orbitRankLocus_eq_multSum`** — the LR Cor 3.5
  geometric-codim = the paper's quadratic `multSum`, with Voigt DISCHARGED
  (`VoigtDischarge.…_unconditional`).

So the geometric orbit-codim theory is PRESENT and proven. **But** these decls live over
`Core.Tuple`/`RepCoord` and the **Kostant multiplicity array** `multSum`. The RLCT layer's
`Adm`/`Mval`/`PivotWitness` live over the **combinatorial exponent vector** `T : Fin L → ℕ`
(`DLN/RLCT/Foundations/Lambda.lean:62`), with NO import-level dependence on Core's orbit objects, and
there is **NO** `multSum ↔ Mval` bridge anywhere (`git grep multSum -- lean/DLNFibre/DLN/` is empty).
This separation is the crux of the scale question (§3).

## 2. The value route is achiever-only — full surjectivity is strictly stronger than needed [FACT]

`routeM_rlctAtOn_eq_iInf` (`fm2/route-m-atlas:RouteMBridge.lean`, PROVEN) gives
`rlctAtOn F 0 = ⨅_i monomialThreshold (dᵢ kᵢ hᵢ)` from `IsRouteMCover F U ι d k h` + `[Nonempty ι]`.
The value `⨅ = ½·minAdm` has TWO proven landing lemmas:

- **`foldFamily_iInf_eq_half_minAdm`** (`RouteMState.lean:321`, PROVEN, driver-agnostic) needs exactly:
  (C≥) a `PivotWitness M c` for every codim `c` on every leaf [⟹ every leaf threshold ≥ ½·minAdm], PLUS
  (C=∃) **ONE** achiever leaf `i₀` with `minAdm ∈ codimsOf i₀`. A single leaf — NOT coverage.
- **`resolution_value_of_atlas`** (`ResolutionAtlas.lean`, PROVEN) needs the STRONGER `IsResolutionAtlas`
  with `stratum_surjective : ∀ T ∈ Adm M, ∃ i, stratum i = T`.

An `⨅`-equality by `le_antisymm` logically requires only a per-leaf lower bound + ONE attaining leaf.
**Full `∀ T ∈ Adm` surjectivity is strictly stronger than the value needs** [FACT — forced by the
`le_antisymm` shape; Codex Q1 concurs, hypothesis withheld]. The controller's own re-scope already
recorded this (`r1-rescope-statement.md:28` "NOT a chart↔Adm bijection — charts outnumber strata";
g138 §2 "full `stratum_surjective` becomes the conceptual statement, `(S-min)` the load-bearing
minimum"). The `IsResolutionAtlas.stratum_surjective` field is the conceptual over-statement; the
load-bearing obligation is the weaker (C≥)+(C=∃). The (2,2,2) instance confirms this — it closes
end-to-end through a single `Fin 1`/`Unit` binding leaf (`Case222RouteMCover`), NOT through
`IsResolutionAtlas`.

## 3. (C≥) — codim bookkeeping vs geometric identification (the scale-deciding split)

The `RouteStep.branch` field `witness : (c) → PivotWitness M₀ (codim c)` demands, per cell, a
`T ∈ Adm M₀` with `codim c = (Mval M₀ T).toNat`. Two honest ways to discharge it, with DIFFERENT scale:

- **(a) combinatorial-by-construction.** Define each cell's `codim` AS `Mval M₀ T` for a `T` the
  dispatcher picks from the rank-drop profile of the cell's `ChainDimSplit`. Then `PivotWitness` is
  immediate. The geometric content (that this `codim` is the REAL exceptional-divisor codim feeding the
  descent) is NOT in `PivotWitness` — it migrates into the per-step Schur presentation `hnode` consumed
  by `schur_straighten_squeeze_exists` (`GeneralR1Recursion.lean:610`, PROVEN given `hnode`). This is
  **DLN-combinatorics + the analytic `hnode` interface** — formaliser-scale [INFERENCE, strong].
- **(b) geometric-then-prove.** Read the actual blow-up center's codim and prove `= Mval M₀ T` via
  `codimRepCanonical_orbitRankLocus_eq_multSum` + a NEW `multSum = Mval` bridge over `Adm`. This is
  Core-orbit-codim scale + the unbuilt bridge — strictly larger, and NOT required by the value logic.

Route (a) is the one the architecture already commits to: the `codim` field is a bare `ℕ` chosen by the
dispatcher, paired with `PivotWitness`; `redCore_eq` carries the analytic descent SEPARATELY. **(C≥) is
therefore a finite induction over the `ChainDimSplit` width-drop, NOT new Core theory** [INFERENCE;
Codex Q2 concurs: "C≥ does not logically require Core orbit theory unless the chart construction's
definition of cells is geometric rather than combinatorial"]. The honest residual inside (a) is that
`hnode` must be PRODUCED uniformly for general M — see §5.

## 4. The achiever leg (C=∃) needs a NON-uniform branch — the precise (2,2,2)→general obstruction

This is the sharp finding, exact-algebra-verified. The brief's option (b) (root-anchoring) and option
(c) (global surjectivity) are both PARTIAL diagnoses; the real obstruction is option (a)-shaped but
sharper:

- **The achiever stratum is NEVER the origin** (`check_codim_additivity.py`, all of
  (2,2,2),(3,3,3),(4,3,2),(3,3,3,3),(5,4,3,2),(4,4,4,4,4)): `Mval(M,0) > minAdm` STRICTLY). E.g.
  (4,3,2): origin codim `Mval(M,0)=12`, but `minAdm=6` at achievers `(2,0),(3,0)`.
- **The single deterministic `schurState` chain collapses both front widths toward the origin**
  (`check_codim_compose.py`): (4,3,2) → (3,2,2) → (2,1,2) → (1,0,2). It bottoms at the
  front-collapse/origin region, whose codim `> minAdm`. So the uniform-`schurState` leaf threshold is
  `> ½·minAdm` and does **NOT** bind.
- **Root-anchoring is necessary but not sufficient** (`check_branch_needed.py`):
  `minAdm(schurState.red) < minAdm(M₀)` for ALL tested M (the pp2 g207/g214 undershoot — confirmed
  uniform). Anchoring `PivotWitness` at `M₀` fixes the *value bookkeeping*, but does not by itself make
  any leaf reach the achiever stratum.

⟹ **The obstruction to generalizing (2,2,2) is NOT (b) [root-anchor alone] and NOT (c) [global
surjectivity]. It is: `routeStep` must emit a GENUINE BRANCH whose cells correspond to DIFFERENT
rank-drop profiles, with ≥1 cell whose split holds the achiever's ranks (`T*`, not the front-collapse)
so its accumulated codim `= Mval M₀ T* = minAdm`.** The achiever-cell `ChainDimSplit` is NOT the uniform
`schurState` (which collapses fronts); it is the split dictated by `T*`'s profile. That achiever-cell
split + its codim-match is the unbuilt content. [FACT for the "achiever ≠ origin" arithmetic; INFERENCE
that this forces branching in the dispatcher.]

- **`T*` is GREEN.** `Finset.exists_mem_eq_inf' (Adm_nonempty M) (Mval M)` gives `T* ∈ Adm M` with
  `Mval M T* = minAdm` directly (it is destructed inside the green `close_of_feasible`,
  `Skeleton.lean:2937`; A1 `lambdaCore_eq_clean` is sorry-free). So the achiever exponent vector is a
  library-level constructor — the residual is the GEOMETRIC PATH that resolves it, not the vector.

## 5. The genuine residual — one analytic interface, named precisely

Everything reduces to: **construct, for general M, the per-cell blow-up Schur presentation `hnode`**
(the explicit hypothesis `schur_straighten_squeeze_exists` consumes):
`flatCore w = Σⱼ (w.1 j)² + Σᵢⱼ (bcol w i · w.1 j + SΓ w i j)²`, `G(w.2)² = Σ ‖SΓ‖²`, `‖bcol‖² ≤ T²`
on a nbhd of the cell's deepest point, with `redEmbed` det-1 MP and `S.red = schurState M` (or the
achiever-cell split). This is the only place a NEW obligation enters; the squeeze, transport
(`rlctAtOn_reduced_transport`), termination (`ChainDimSplit.redM_widthSum_lt`), value fold
(`foldFamily_iInf_eq_half_minAdm`), and `T*` are all GREEN.

- **(2,2,2):** `hnode` is supplied concretely (`Case222*` charts) — DONE.
- **general M:** `hnode` for each cell is the general hard-pivot Schur chart (g131/#127 `(L,R)`
  transvections, `S = D − b·a`) — the per-step content. The (2,2,2) chart is the template; the general
  lift is the same mechanism parametrised over M, with the per-cell `bcol`/`SΓ` read off the blow-up.
  This is **intricate-standard formalisation, NOT open math** — the mechanism is g131-certified; the
  work is constructing the chart at arbitrary M and discharging the four `hnode` conjuncts.

The SINGLE smallest missing theorem, stated precisely:
> **(R1-§4-gap)** For every reduced width vector `M` and a designated achiever stratum `T* ∈ Adm M`
> (`Mval M T* = minAdm`), there is a finite branch tree (the `routeAtlas` over `ChainDimSplit`) such
> that (i) every cell carries a `PivotWitness M₀ (codim)` [(C≥), combinatorial], and (ii) ≥1 leaf's
> codim-list contains `minAdm` [(C=∃), the `T*`-resolving branch], with each step's analytic descent
> supplied by an `hnode` Schur presentation at that cell.
>
> **Scale class: DLN-chart-combinatorics (formaliser-weeks), gated on the general `hnode` chart
> construction.** NOT Core-orbit-Kostant scale — the value never invokes `multSum`/orbit-codim.

## 6. The honest deliverable shape (the controller's decision input)

- The general-M **headline** does NOT close in this expedition as a sorry-free theorem: `routeStep`
  remains fenced, and even above it the achiever-leaf wiring (`foldFamily_iInf_eq_half_minAdm`'s
  `i₀`/`hbind₀`) and the per-step `IsSchurStraightenSqueeze` consumption are NOT yet assembled into
  `routeAtlas`/`routeMIota` (verified: both referenced ONLY in `routeStep`'s docstring; the value chain
  is unbuilt above the sorry).
- What IS honest and bankable: **(2,2,2)-instance end-to-end (3/2) + the conditional-general spine**
  (`routeM_rlctAtOn_eq_iInf`, `foldFamily_iInf_eq_half_minAdm`, `schur_straighten_squeeze_exists`,
  `rlctAtOn_reduced_transport`, `lambdaCore_eq_clean`/`T*` ALL green) **+ the roadmapped `routeStep`**
  with §5's named gap. The general result is `IN-REACH` (achiever-only, formaliser-scale) but the WORK
  (general `hnode` charts + branch assembly) is genuine and not yet done.
- **Do NOT** re-aim at `IsResolutionAtlas`/full `stratum_surjective` — it is strictly stronger than the
  value needs (§2) and would import the (b)-route Core-orbit dependency unnecessarily.

## Most likely thing to break this verdict

The `hnode` general construction (§5) hides whether the per-cell `bcol`/`SΓ` decomposition stays in the
clean Schur form at DEEP, MIXED nodes (g138's C5 partial-drop / multi-drop). g138 §"most likely to
break" already flagged the C5 block-column split's measure-preservation as the one place to verify
before locking the C5 chart. If the general `hnode` cannot be produced uniformly at C5/mixed nodes
(Codex's explicit Q4 escape hatch: "I would not classify this as a research gap UNLESS the Schur
presentation itself cannot be produced uniformly for general M"), the gap upgrades from
formaliser-scale to a genuine per-node-mechanism research piece. **The next construction that would
settle the open part:** a general-M `hnode` cert at a C5 mixed node (the `t=(3,3,2,2,2,0)` witness),
exact-algebra, confirming the four conjuncts + det-1 MP — the analogue of the g131 (2,2,2) cert at
arbitrary M. That cert (witness or refutation) is the single highest-value next decorrelated step.
