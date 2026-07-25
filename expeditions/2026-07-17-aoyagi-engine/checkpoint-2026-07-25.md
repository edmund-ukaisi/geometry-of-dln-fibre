# Checkpoint — 2026-07-25 (regrounding + refresh)

Operator-directed checkpoint after a long reactive stretch (the flat-fan cover saga → the θ=1
mirage → the operator's "consume don't re-derive" re-grounding → the #148 flip). Consolidate:
reground the math, pin the consumable assets **by interface** (forget internals once kernel-checked),
name the holes, plan. Pins marked ✅ = verified clean-three; ⏳ = pending consume-verify (#154).

## 1. The math (the payoff, regrounded)

Destination: **RLCT of the DLN square-Frobenius loss = C/2**, C = the geometric codim (the new content).
- The loss localizes to `∑ (coreGen dvec eWrap)ᵢ²` at 0 (flatten + coreReduction). [banked]
- `rlctAt(∑Fᵢ²) 0 = ½·(min over resolution charts of the binding exponent Mval) = ½·cCodim = ½·C`.
- **UPPER** `rlctAt ≤ ½·chartMin` from ONE chart (single-chart CoV) — ELEMENTARY. [#110 ✅ cite-free]
- **LOWER** `rlctAt ≥ ½·minMval` — needs the FULL resolution atlas (whole-neighbourhood integrability
  via `res.hcover`; NO ideal shortcut — #146, 4-channel). **THE crux / the "mildly singular" content.**
- The **resolution** = a recursive `buildTree` of blow-up charts; each TERMINAL (two-sided
  `⟨∏C∘g⟩=⟨diag b⟩`) AND the atlas COVERS a neighbourhood of 0. Value rides the minimizing branch.
- `exists_coreResolution:311 = ∃ res, AtlasRealizesExponents dvec res` = the SOLE open sorry on the
  payoff cone (AxCheck). Discharge it cite-free (build) OR cite it (`cited_aoyagi_lower_ax`, objects-only).

## 2. Assets — PINNED by interface (consume these; internals forgotten)

- **Value combinatorics (Object D)** ✅ `Core.CCodim*/CTheta*`: cCodim, θ, numTop. θ(3,3,4)=1, C=8. Clean-three.
- **Ledger (general-L)** ⏳ `EngineConstruction`: `isFullMonomialization_buildTree_conRoot {L}`,
  `minAdm_le_terminalExponents {L}`, stepUpdate/MvalCoh/L8'. The exponent read-off. No ledger work owed.
- **L5 fold (general-L)** ⏳ `L5FoldSpec` (`leaf_stepInv_of_path` hinge) + `DivBirthReach.leaves_chart_clauses {M}`.
  Owes ONE lemma: the **b-chain along a path**. Consumes the per-step protos; NOT the Encoding-S anchors.
- **Per-step hideal (the crux):**
  - (3,3,4) Fin-21 instance ⏳: `Corank2{,Maintenance,Terminal,Hideal,Composite}Proto`, `chart334`, part-C
    (`Corank2CoreGenWrap` ⟨c11·E⟩), 5a/5b. Decorrelated-validated (cruxB sympy reproduced ⟨c11·E⟩).
  - general-d uniform (S,J) lemma: MATH detail-at-scale (#148 — atoms (A) I₁-inv / (B) blow-up div / (C)
    b-chain-threshold; joint-regular-coord invariant survives via the polynomial automorphism). LEAN-crux
    CLOSES at symbolic width (sj-uniform-probe: `fromBlocks` + SUM-TYPE blocks, no fin_cases — the flatten
    was the pain, not the math). `schur_clear_two_sided` being promoted to a committed brick (#155). 2/3
    atoms ALREADY parametric in committed Lean (`regionRepresents_of_matrix_mul`,
    `blockBlowupMap`/`resid_comp_gBlk`, `terminal_bezout`); 3rd = the Schur brick.
- **Value-upper #110** ✅ `rlctAt ≤ ½·chartMin` (single-chart, cite-free) `Corank2UpperBound334`.
  **#110(i) LANDED (routeP-p1, pushed 8b4145366, `Corank2CiteFree334`, clean-three, NO `cited_watanabe_upper_ax`):**
  `codimRealFibre_334_zero_toNat = 8` (reduction (b), field-independent, fully discharged) +
  `rlctGlobal_lossDLN_334_zero_le_half_codimRealFibre (hmp : MeasurePreserving eWrap)` = the exact (3,3,4)/B=0
  instance of `cited_watanabe_upper_ax`, proved without the cite. **Cite-free MODULO `MeasurePreserving eWrap`**
  (the one un-banked gap — `eWrap` is the custom transpose flatten, only `measurePreserving_canonFlatten` banked;
  `eWrap`-mp is TRUE [linear reindex det ±1] but ~40-80 LoC measure-infra = the `eWrap↔canonFlatten` transport,
  owned by the consume-build 5d/#143). **Both the aggregator-wire AND `eWrap`-mp DEFERRED to the consume-build**
  (wire the unconditional version once, on an (A)/consume GO); banked/pushed regardless.
- **transportChart + coreGen K-equivariance** ✅ `ChartTransport`, `Corank2CoreGenEquivar` (K=S4×S3×S3).
  Reusable IF the recursive route transports; else parked.

## 3. FORGOTTEN / dead (do NOT consume; pruned)

- The **flat gWrapFan cover** (`exists_ball_subset_gWrapFan_leafImages`, resolution334-via-flat-fan): the flat
  fan is NOT a resolution (MONOMIALIZATION ⊥ COVERAGE; K-orbit annulus-only). The cover OBJECT is dead; only
  the box-containment BRICKS (`shearH_covers`, `blockShear_covers_scaled`, `abs_jacDet_permCoord`) transfer.
- **θ=1 bypass (#111 / V-wire)**: MIRAGE (#146 — the lower bound needs the atlas). #109 = a killed render.
- **MonumentAtlas Encoding-S anchors** (`case1_conjA`/`appendResidDescent`/`MergeBoostSplit`): the OTHER
  encoding's frontiers — off this path.
- **route-B K-orbit standalone cover**: dead (annulus-only).

## 4. Holes (open obligations, rendered)

1. **general-d per-step two-sided hideal lemma** (symbolic width): crux de-risked (math #148 + Lean Schur
   atom). Remaining = assemble the atoms (block-elim ∘ blow-up ∘ b-chain ∘ tail-recoord `C'=Q⁻¹C`) into ONE
   parametric lemma over sum-type blocks + re-state `blockBlowupMap` over the sum-type block. Multi-tide.
2. **b-chain-along-a-path** lemma (the L5 fold's one owed hypothesis).
3. **the recursive buildTree cover** (the atlas covers a nbhd): the flat-fan detour is dead; the per-sector
   adapted-center recursive cover is un-built (charter: route-a GREEN on the math; un-probed in Lean at the
   recursive/coupled level). **The genuinely-hard remaining piece.**
4. **the assembly**: wire per-step hideal + cover + ledger + L5 fold → `exists_coreResolution:311` → the
   lower bound → delete `cited_aoyagi_lower_ax` → the payoff.
5. **(3,3,4) instance** (near-term, fork-independent): merge the 3 lanes + wire the L5 fold body (+ b-chain)
   + the cover seam → the (3,3,4) Resolution. The Fin-21 engine is banked; this is a validation + the
   general-d build's base case.

## 5. The fork (elder-gated per operator hand-off #2)

- **(A) BUILD general-d** (#112): NOW detail-at-scale (math #148 + Lean-crux PASS), a real MULTI-TIDE build
  (per-step lemma assembly + recursive cover + wiring) → :311 cite-free → delete `cited_aoyagi_lower_ax` →
  the full cite-free payoff (charter-faithful full result). Build-commit = controller's call, elder-gated.
- **OBJECTS-ONLY close**: bank objects A-E + value combinatorics + #110 + the (3,3,4) instance; CITE general-d
  (`cited_aoyagi_lower_ax`, honestly labeled). Charter fallback; per #94 objects = DONE. Now PRAGMATIC (not forced).
- (C) θ=1: dead.

## 6. Refreshed plan

1. **Finish the tranche + pin assets:** consume-verify (#154 → the consume-map + clean-three pins for
   ledger/L5-fold/protos/cover-seam); schur-casttax (#155 → the `schur_clear_two_sided` brick); routeP-p1's
   #110 (3,3,4)-upper wiring. → verified pins for §2.
2. **This checkpoint** — reground done.
3. **Elder-gate the fork** (with the pinned assets + de-risked (A)-detail-at-scale + the multi-tide cost +
   the objects-only fallback + paper-fidelity). Controller commits per the charter.
4. **If (A):** general-d build — (i) per-step hideal (schur brick → assemble atoms → uniform two-sided hideal,
   sum-type blocks); (ii) recursive buildTree cover (per-sector adapted); (iii) wire via L5 fold + ledger →
   :311 → lower bound → delete the cite → payoff. Multi-tide, lane-delegated.
   **If objects-only:** close-out — bank objects + #110 + the (3,3,4) instance; payoff via_engine w/
   `cited_aoyagi_lower_ax`; the #94 close-phase (literal-name Skeleton clean-three).
5. **Parallel (fork-independent):** the (3,3,4) INSTANCE consume-build (merge lanes + wire the Fin-21 engine)
   — validation + the (A)-build's base case.

## 7. Discipline (session lessons — carry these)

- **Anti-optimism:** 5+ "clean route" over-generalizations corrected this session (wire → route-B → V1 →
  monument → objects-only). The decorrelated exact hunt is the damping — trust it; **cross-check the banked
  engine before pricing a build a monument** (the operator's #2 catch); for a RESOLUTION claim the load-bearing
  sensor is exact-algebra + Lean, not a coverage MC; sweep ρ→0 for homogeneous coverage.
- **Pin-and-forget:** consume verified interfaces; forget proof internals.
- **The cover (hole 3) is the genuinely-hard remaining piece** — the flat-fan was the detour.

---

## 8. CONSUME-VERIFY CORRECTIONS (force-elab `#print axioms`, 2026-07-25) — supersedes §2's optimistic pins

consume-verify (#154) verified each item on fresh scratch files. Net: the "banked-modulo-wiring" framing
(operator hand-off #2 + my §2) was **partly optimistic** — the ledger IS banked, but the fold + cover +
per-step hideal are **an unwritten value-path build, not wiring**. Accurate picture:

- **Item 1 LEDGER ✅ CONFIRMED** — clean-three, genuinely general-L. Consume as pinned.
- **Item 4 PROTOS ✅ clean-three, but ISOLATION MEASUREMENT bricks + a composition primitive** — NOT a wired
  per-step hideal. L-A (`HidealProto`, n=21) reaches ⟨peeled⟩ (a POLYNOMIAL — its own docstring is a STOP:
  does NOT deliver `Chart.hideal`; terminal needs the (S,J) recursion). L-B (`MaintenanceProto`) is
  CONDITIONAL on the b-chain hypothesis. L-C (`TerminalProto`, Fin 4) end-to-end. `regionRepresents_comp` =
  the composition primitive. Consume as bricks; the per-step hideal itself is UN-BUILT.
- **Item 2 L5 FOLD ⚠️ NOT banked** — `L5FoldSpec` is SPEC-ONLY (obligation map, proven as delegation). The
  actual hinge `MonumentAtlas.leaf_stepInv_of_path` CARRIES sorryAx (MonumentAtlas = 16 sorries, ENCODING-S:
  case1/case2/appendResidDescent/lastLayer/L6/L7/L8). The current committed fold consumes the **Encoding-S
  anchors, NOT the gate2 protos** — the proto-consuming (Encoding-I) fold is UNWRITTEN (an intended
  re-architecture). `leaves_chart_clauses {M}` IS proven general-L but is a DIFFERENT object (the combinatorial
  divCoord/resCoord ledger, not the b-chain). The b-chain lemma (precise): `b'_p ∣ b'ᵢ` along a path (the L-B
  hypothesis `hr`); the FULL hinge additionally owes the fold spine (M4 pivot-preservation, M7
  canonNormalizationOf, FoldProduced/FoldRealizes, L6/L7/L8).
- **Item 3 COVER ⚠️⚠️ seam dead-as-cover** — endpoints clean (`resolution334_of_ballCover`, `chart334`,
  `gWrapFan_covers`), but the certified-chart family must be **BUILT** (route A: 288 pivot-ADAPTED
  normalizations, each pivot-path its own shear → per-chart binding {8,9} → `..._ofValues`) — substantial NEW
  work, NOT from `leaves_chart_clauses`, NOT K-orbit (route B dead, escape cone). consume-verify's **route-C
  recommendation is STALE** (repeats sector-count's pre-#146 reconcile-certificate; #146 verified #109 is a
  KILLED RENDER, route C = mirage). #109 is NOT a landed lower bound — DO NOT revive route C on it.
- **Merge order** (no name clashes; identical protos gate2↔routeP; 3-way reconcile only `Corank2UpperBound334`
  [all lanes] + `Corank2FanDef334` [5d-transport rebase onto routeP]): gate2→trunk, then routeP (supersedes
  gate2's 11 older files), then 5d-cover, then 5d-transport; full `lake build DLNFibre` after each.

**⟹ CORRECTED holes (§4 expands):** the (3,3,4)/general-d resolution is NOT banked-modulo-wiring — it is a
SUBSTANTIAL multi-tide build: (i) the proto-consuming (Encoding-I) per-step hideal FOLD, replacing the sorried
Encoding-S MonumentAtlas hinge (+ the b-chain + the fold spine M4/M7/L6/L7/L8); (ii) the adapted-chart COVER
(route A, 288 adapted normalizations); (iii) the per-step hideal recursion (protos → the (S,J) fold, since L-A
only reaches ⟨peeled⟩); (iv) the assembly → :311. Detail-at-scale (math crux de-risked, #148 + the Schur atom),
but a real multi-tide build — NOT wiring.

**⟹ CORRECTED fork (§5):** (A) BUILD = this substantial multi-tide detail-at-scale build (cost materially
higher than "wire the banked engine"); (objects-only) = bank the SOLID pieces (ledger ✅, #110 ✅, value
combinatorics ✅, objects A–E) + cite the resolution (`cited_aoyagi_lower_ax`). The elder-gate weighs (A)'s
now-accurate multi-tide cost vs objects-only. (C) θ=1 = mirage (do not revive on consume-verify's stale route-C).

**(A)-crux de-risk now COMPLETE (2-channel Lean, 2026-07-25):** schur-casttax's committed-scratch PASS
(`scratch_schur_casttax.lean`, axiom-clean, non-vacuity (3,2,2)) + sj-uniform-probe's throwaway both close the
unit-pivot Schur atom at symbolic/dependent-Fin width. STRUCTURAL reason: the cast-tax pain is ENTRYWISE work
at opaque widths; the Schur clearing lives in the width-agnostic `Sum`-block category (⅟A abstract) + rides
bundled `reindex`/`submatrix_mul_equiv` — the `p=r+(p−r)` arithmetic is absorbed into an Equiv, never a raw
cast. So the (A) crux is de-risked BOTH on the math (#148) and in Lean; residual (A) risk = scale/labour +
two named downstream seams (`⅟→⁻¹` for the ∫⁻; rank-exactly-r vanishing), NOT a wall. The scratch is UNCOMMITTED
(HELD — committing the first general-d brick is arguably starting (A); the fork is operator-gated); evidence
captured, scratch reproducible from the certificate; promote `schur_clear_two_sided` as (A)'s first step on GO.

**UPPER/LOWER cite SPLIT (routeP-p1's #110 forward engine, LANDED d10ea128f, 2026-07-25):** the minimizer
upper `rlctAt ≤ ½·chartMin` follows FORWARD-only (`hideal_fwd` + Object C + a loss-null guard) — NO principality,
NO reverse, NO atlas (`Chart.rlctAt_le_chartMin_half_forward`, clean-three; the (3,3,4) instance
`rlctAt_coreGen334_le_four_forward` clean-three). ⟹ the two payoff cites split by DIFFICULTY:
- `cited_watanabe_upper_ax` (UPPER) = CHEAP to delete general-d (forward (S,J) maintenance over the minimizing
  branch + the jac-exponent ledger; no atlas, no reverse) — avoids BOTH #147 monument pieces.
- `cited_aoyagi_lower_ax` (LOWER) = the genuine remaining hard piece = the two-sided hideal (de-risked, #148/schur)
  + the recursive COVER (hole 3, un-built). Per #148 NOT principality — "the monument" = the recursive cover.
This refines BOTH fork horns: **objects-only** can additionally delete the UPPER cite general-d cheaply (leaving
ONLY the lower cite — a tighter honest close); **(A)-full** builds the lower (two-sided hideal + cover). The
fork's real cost is concentrated in the LOWER = the recursive cover. Fork-conditional + HELD (per operator-gate):
the UpperChart ~200-LoC extraction (forward-only input) + the general-d upper (fwd maintenance + jac ledger).
Recommended-but-deferred: a fidelity review of the forward engine ("proof uses no hideal_bwd") — clean-three
banked; audit when the general-d upper is on.

**First general-d brick PROMOTED (schur-casttax, 2026-07-25) — banked as EVIDENCE, UNTRACKED (hold-respecting):**
`lean/DLNFibre/Core/Matrix/SchurClearTwoSided.lean` (~148 LoC, fully abstract `{l m : Type*} [Ring R]`, no
Invertible/field/A⁻¹). Interface (all 9 force-elab clean-three, non-vacuity (1,1)/ℚ, no clashes):
`schur_clear_two_sided` (forward: `lowerShear(-C)·fromBlocks 1 B C D·upperShear(-B) = fromBlocks 1 0 0 (D-C·B)`),
`schur_reconstruct` (reverse), `schur_clear_two_sided_fin` (the `finSumFinEquiv` reindex bridge to flat
`Fin(r+s)`), + shear group-law/inverse/isUnit. UNTRACKED + UNWIRED (not starting (A); instant first step on
(A)-GO — add the import + green-gate). Fidelity review DEFERRED (fork-conditional). Sits beside
`RankNormalFormTriangular` (complementary: that's one-sided/invertible/ℝ/Fin; this is two-sided/unit/Ring/Sum).
Deferred algebraic obligation (named): the Schur complement is symbolic `D-C·B`, not asserted 0 —
rank-exactly-r vanishing is separate.
**Build hazards to BANK to lean/CLAUDE.md at the (A)-build/merge** (reusable, both hit): (1) bare `simp` SPINS at
whnf over abstract-Fintype block sums → use targeted `simp only` + `abel`, never bare `simp`; (2)
`fromBlocksZero₁₂Invertible` spins constructing `Invertible` over abstract `Ring R` → build `Invertible` from the
explicit shear-inverse identities.
