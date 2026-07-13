# endgame-lanes.md — the parallel-lane interface tracker (controller-owned, durable)

**Purpose (operator directive 2026-07-13).** Controller's durable interface ledger for the (□) endgame lanes.
Tides build in worktrees; controller integrates one-at-a-time (aggregator + AxCheck + green-gate + commit).
**Authoritative tick-by-tick trail = `synthesis.md` (UPDATE-1047 newest).** This is the lane-status view.

## Target chain
`DecoratedDescent` → driver `routeMBoxThresholdFinite_of_decoratedDescent` (clean-three) → `(□) ∀M`
→ `aoyagi_learning_coefficient_gen`'s `hbox` → unconditional `_gen` → re-point unsuffixed `#108`.
`DecoratedBaseHyp` (#4) DONE. `DecoratedStepHyp` (#5) = the mountain: **track (a) L≥1 head-split**
`deeperFlag_spineToCore` = F ∘ headSplit_domination; **track (b) L=0 base** = banked (`routeMBoxThresholdFinite_mnp`).

**★ MILESTONE: the (□) discharge is decorrelated-confirmed LABOUR to the end — ZERO walls.** Down to one
genuine analytic crux (`pivotDom_finiteness`, the cross-term drop) + mechanical assembly.

## LANDED on canonical (clean-three)
| Brick | Module | Result |
|---|---|---|
| D-A | `RouteMSJPivotBlowup` @e45d434d | `pivotBlock_radial_blowup` (P-radial blow-up CoV) |
| D-B | `RouteMSJRankRCodim` | `lintegral_cube_frobSq_neg_of_finrank_range` (rank-r codim integrability) |
| D-C core | `RouteMSJKyFan` @a09fdd26 | `finrank_add_weakCount_le` |
| D-C corollary | `RouteMSJShellContain` @e45d434d | `shell_subset_goodSet` |
| F2a | `RouteMSJOrderedRootsMeasurable` @d6bc1ed4 | `measurableEigenvalues₀` (Vieta+Lusin–Souslin) |
| **★ Brick F** | `RouteMSJMeasurableEigenframe`+`…Eigendecomp`+`RouteMSJHeadSplitFrame` @5e114405 | F2b `exists_measurableEigenframe` + assembly `measurableEigendecomp` + F1 `exists_headSplitFrame_impl` — the measurable head-split frame; the measurable-eigendecomposition Mathlib gap CLOSED |
| #108 mint pre-stage | `RouteMSJMint` @c8302a0e | `aoyagi_learning_coefficient_gen_of_descent` (wiring verified end-to-end) |
| base (track b) | `routeMBoxThresholdFinite_mnp` (banked, RouteMSchurRectCapB:453) | 3-width box finiteness ∀ widths, clean-three |

## LIVE (worktrees; controller integrates on landing)
| Lane | Tide | Branch | Status |
|---|---|---|---|
| **shellSpine_le_hsQ_box** (plumbing) | a8a42c82 | genm-sj5-headsplit-dom @8deb0aca+ | finishing #1 integrand-id + #2 transport/Tonelli (mechanical, route mapped; hsSplit + hsSplit_good_of_shell banked; all 4 stub-refinements committed) |
| **pivotDom_finiteness** (crux, tide b) | a93e7b9c | RouteMSJPivotFin on genm-sj5-pivotdom | CHECKPOINTED + LOCKED (Route A domination, uses hRHS directly, no exponent extraction). **ARCH-A CORRECTION #2 applied at checkpoint:** step-3 cross-term drop as a pointwise-in-corank C_ang at exponent c' (D-B codim uρ ⟹ c'<uρ/2) is UNSOUND for c'∈(uρ/2,minAdm(M)/2); witness (3,3,3) c'∈(3,3.5). The corank MUST supply the residual ab/2. Sound realizations: (a) JOINT D-B on (P̂,B̃₁₂,A_cor,Γ)↦freedLoss at codim uρ+ab≥minAdm(M) [cross-term drop = shear-preserves-rank, S3 drops out]; (b) sequence corank-first, C·decLoss^{-(c'-ab/2)}, pivot at reduced exp c'-ab/2<uρ/2. Recon-gate: (3,3,3) accounting + tide's Codex before grinding step 3. #166 |
| **RHS≠0 + uzero** (helper) | aa56113 @334e7f96 | RouteMSJPivotDom on genm-sj5-pivotdom | mechanical (confirmed 3-piece plan); fills the other 2 pivotDom sorries. (Its startup flaked into MAIN once — recovered; see Process) |

`headSplit_pivotDom_impl` ratio wiring is sorry-free (GLUE-2 @19dd58ff = origin/genm-sj5-pivotdom); reduces to those 3 sorries.

## DOWNSTREAM LANES — FRONT-LOADED (2026-07-13, operator parallelization; pivotDom-INDEPENDENT)
Use tide-b's arch-correction-#2 grind hours (hours) to lock every downstream contract now, so pivotDom's close leaves only one-exact fills, not fresh design questions on mint day.
| Lane | Agent | Branch | Status |
|---|---|---|---|
| **DecoratedStepHyp assembly skeleton** (contract-first) | stepasm a7673edf | genm-sj5-stepasm | Casing deeper-flag shells into 3 named holes (j<r=head-split / j=r=saturated arity-IH / waist=reduce-to-`_mnp`). Deliverable = TYPECHECKING skeleton + seam report (j≤r-vs-j<r quantifier gap, waist hole's REQUIRED statement). Doubles as the statement-level seam audit (the 4×-paid catch pattern). Do NOT fill holes. |
| **Waist-connector design pin** | waistpin (pen-and-paper) | (no git; returns cert, controller homes) | Adjudicate hpiv-FAILING waist shells → banked `_mnp`. Witness→obstruction; route-B orientation REFUTED (avoid). Only remaining unpinned design. TARGET = the waist hole's required statement from the stepasm skeleton (I relay). BOUNDED-vs-WALL verdict + Codex. |
| **L=1 mint brick** (headline) | helper aa56113 (QUEUED after RHS≠0/uzero) | genm-sj5-l1mint | Unsuffixed #108 (∀L≥1) needs L=1 via a separate path (`_gen` carries 2≤L). SCOPE-FIRST before grinding. Consumes nobody's output; lands any time before mint. |

**Interface handoff:** stepasm reports the waist hole's required statement → I relay it to waistpin as its exact target. When pivotDom closes: headSplit_domination clean-three → DeeperFlagCore stubs → deeperFlag_spineToCore → DecoratedStepHyp (skeleton's holes filled) → DecoratedDescent → (□) → mint (L=1 brick + _gen).

## CRUX DE-RISK (parallel to tide-b; advisory-to-controller)
| Lane | Agent | Status |
|---|---|---|
| **arch-#2 realization adjudication** | archfin (pen-and-paper) | Decorrelated check of the tide-b crux: verify (a) joint-D-B codim uρ+ab and (b) sequenced exponent-reduction c'-ab/2 are each SOUND (exact (3,3,3) accounting), NAME the single new sub-lemma each needs, RECOMMEND the cheaper-to-formalize route, flag any third arch-A-style hazard. Returns to controller; NO cross-talk with tide-b. Reconcile vs tide-b's own (3,3,3) gate → relay ONE locked answer. |

## PLAN-AHEAD — post-pivotDom assembly sequence + triggers (controller-owned)
1. hGmeas: soft-asked to #2 (consumer-owner); fallback = controller builds from F2a at integration.
2. **TRIGGER — on stepasm's report:** it names the j=r saturated-shell hole's exact statement. Assess j=r = one-liner (IH application at reduced arity) vs needs-a-tide; commission immediately if the latter (pivotDom-INDEPENDENT — it's the IH, not the head-split). Also relay the waist hole's required statement to waistpin.
3. **TRIGGER — on archfin's report:** reconcile with tide-b's (3,3,3) gate; if they agree, tide-b's route is confirmed (raise confidence, let it grind); if they diverge, dig before tide-b sinks more hours.
4. **On pivotDom + #2 + helper landing:** merge headsplit-dom + pivotdom branches (inline pivotDom_finiteness → RouteMSJPivotDom, break hsQ cycle) → fill headSplit_domination → DeeperFlagCore stubs (exists_headSplitFrame := F1 impl; hGmeas; refinements hjr/hε'le=le_refl/hZfMeas from Brick F) → deeperFlag_spineToCore = F ∘ it → DecoratedStepHyp (fill stepasm's 3 holes: j<r=spineToCore, j=r=IH, waist=waistpin route) → DecoratedDescent (+#4 base) → (□) → mint (_gen ∘ discharge + L=1).

## Controller-owned integration (at the head-split assembly)
1. **Head-split assembly**: fill `headSplit_domination` (RouteMSJDeeperFlagCore) = headSplit_pivotDom (GLUE-2 pieces) + shellSpine_le_hsQ_box (plumbing) + D-A/B/C banked + S3 + L1. Reconcile: inline pivotDom_finiteness (tide b, RouteMSJPivotFin) into RouteMSJPivotDom; merge the helper's RHS≠0/uzero.
2. **DeeperFlagCore stub refinements** (I own): `headSplit_domination` STUB gains `hjr : j<r` + `hε'le : ε'≤ε/√(M₁M₂)` + `hZfMeas : Measurable Zf` — all discharged in `deeperFlag_spineToCore` (ε'=ε/√(M₁M₂) by le_refl; j<r from shell dispatch; hZfMeas from Brick F's Measurable Zf; hGmeas via the wrapper below).
3. **hGmeas shared wrapper** (~15-20 LoC, I build from F2a): `Measurable (fun z => weakEigCount ε' (Z z))` → `MeasurableSet(good-set)`, for the plumbing's on-shell rewrite. Supplied in deeperFlag_spineToCore.
4. **exists_headSplitFrame stub** := F1's `exists_headSplitFrame_impl`. Then `deeperFlag_spineToCore` = F ∘ headSplit_domination.

## Open architecture (downstream, not blocking the above)
- **#5-compose waist-shell wiring**: how the hpiv-FAILING waist shells reduce to the banked `_mnp` (route-B orientation refuted). Scope at #5-compose.
- **saturated shell j=r**: a SEPARATE arity-(L+1)-IH branch (not the head-split domination, which is j<r) — verify its discharge in deeperFlag_shell_le at integration (must NOT be dropped).
- **L=1 at mint**: `_gen` needs `hL2:2≤L`; the unsuffixed headline (L≥1) needs the L=1 case via the separate path. Mint-time.
- **mint axiom footprint**: `_gen` is clean-three, NO cited-Aoyagi axiom (the cited equality lives only in the separate RlctPayoff framing) — the mint `_gen ∘ discharge` is unconditional + clean-three.

## Process (the recurring hazard — discuss#129/139/141/143)
Flaky `isolation:worktree` intermittently drops a tide into MAIN — `git reset --hard` there wipes controller edits AND, worse (2026-07-13, the helper aa56113 startup), can knock the main checkout onto a tide branch (`genm-sj5-pivotdom-fill`), stranding a controller commit off the expedition line. Recovered each time (Brick F never at risk — committed+pushed to origin @5e114405). The isolation self-check guard did NOT prevent the helper's startup reset. Mitigations: commit+push before launching; commit+push controller edits IMMEDIATELY (never hold uncommitted tracked edits); `git add` explicit paths only; verify `git branch --show-current` = expedition/aoyagi-full after any tide launch. A harness fix (guaranteed isolation) is the real solution — flagged to operator.

## Canonical
HEAD @f29a0bc8 (Brick F landed; the S1 head-split stubs `exists_headSplitFrame`/`headSplit_domination`/`deeperFlag_spineToCore` remain the known open stubs). Every landing AxCheck-gated clean-three.
