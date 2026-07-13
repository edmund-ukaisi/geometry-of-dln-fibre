# endgame-lanes.md — the parallel-lane interface tracker (controller-owned, durable)

**Purpose (operator directive 2026-07-13).** Controller's durable interface ledger for the (□) endgame lanes.
Tides build in worktrees; controller integrates one-at-a-time (aggregator + AxCheck + green-gate + commit).
**Authoritative tick-by-tick trail = `synthesis.md` (UPDATE-1047 newest).** This is the lane-status view.

## Target chain
`DecoratedDescent` → driver `routeMBoxThresholdFinite_of_decoratedDescent` (clean-three) → `(□) ∀M`
→ `aoyagi_learning_coefficient_gen`'s `hbox` → unconditional `_gen` → re-point unsuffixed `#108`.
`DecoratedBaseHyp` (#4) DONE. `DecoratedStepHyp` (#5) = the mountain: **track (a) L≥1 head-split**
`deeperFlag_spineToCore` = F ∘ headSplit_domination; **track (b) L=0 base** = banked (`routeMBoxThresholdFinite_mnp`).

**★★ #1 PRIORITY — CORE SOUNDNESS BUG in `adm` (stepasm found, controller CONFIRMED from the def):**
`adm`'s corank disjunct (`admCorankA/B M = 0`, RouteMSJAdm:192) BYPASSES FaithfulSJAt's β threshold
(:170). `genuineCarrier` (:60-66) constrains ζ/ν/e/ctx but NOT d/jac/supp ⟹ a genuineCarrier decoration
with jac≡0 is `adm` via the corank disjunct yet DIVERGES below threshold. Decide-checkable witness: M=(5,2,1),
admCorankB=0 (bindingCut=2=M₁), minAdm=2; decLoss=|u₀|²·frobSq(prod) ⟹ ∫₀¹u₀^{-2c'}=⊤ for c'∈[1/2,1)<1
⟹ **`DecoratedStepHyp adm` is FALSE as stated.** Base #4 masked it (corank=0⟺minAdm=0⟺vacuous,
`decoratedBase_corankZero`); the step's interior binding cut un-masks it. ★ **FIXED** (admfix verdict, decorrelated
hand+Lean+Codex; `witness_adm` at (5,2,1) native_decide-confirmed): candidate (a) = `adm := genuineCarrier D ∧
FaithfulSJAt D` (DROP the corank disjunct — never a producer; both adm_trivial + cornerComparator_adm use
FaithfulSJAt). Bounded ripple (2 one-token + ~4-line decoratedBaseHyp_faithful; adm-abstract consumers untouched;
NO sound banked result re-opens). Converts `DecoratedStepHyp adm` FALSE-as-stated → SOUND TARGET. apply-tide
**admapply** (ac13b308, genm-admfix-apply) applying now. Verdict: threads/genm-admfix/adm-soundness-verdict.md. **LOCALIZED:** the analytic cruxes (head-split step-2, waist O2, L=1) prove FaithfulSJAt finiteness —
the fix EXCLUDES non-FaithfulSJAt corank decorations, so those lanes are ROBUST (not wasted). stepasm:
dispatch-fix @7a132673 stands; banking clean + FaithfulSJAt-(e) bricks; corank subcases HELD pending the fix.

**★ STATUS (2026-07-13, CORRECTED — the earlier "ZERO walls" milestone is STALE):** the endgame has TWO
descent structures, each with a crux: **(1) head-split** (via redChain) — the pivotDom crux (step 1 grinding
~60% + step 2 forward-finiteness archfin-pinning), LABOUR; **(2) WAIST — O2 RESOLVED as LABOUR (scout a06046ba, decorrelated Codex; NO confirmed wall remains).**
Route-(b) drop-front is a RED HERRING: the eigenvalue-profile weight J_c is NON-admissible (Hölder β<3/4 <
needed β<1; no projection detects λ_min), and re-pointing the head-split to dropHead FAILS (the good assembly
is hpiv-gated). SOUND waist route = route-A **SVD-qPeel** (deep-layer SVD → banked `qPeelIntegral`; #156 = the
L=0 base) + **REORIENTATION** to a good end (every ≥4-width chain has one; reversal CoV I(M)=I(rev M), minAdm
half-banked via minAdm_comp_perm; SVD-qPeel consumes the decoration BEFORE the plain reversal → sidesteps
waistpin's decoration-transport obstruction). NEW labour: one deep-layer Gram-spectral/Weyl-Jacobian CoV brick
+ the reversal-CoV lemma — BOUNDED. Head-split STANDS (the (d)-overlap does NOT obviate it: good+waist emit the
same non-adm J_c; the head-split's cut-folding avoids it). O3 charge ineq VERIFIED tight (minAdm=min_q(M₀q+d_q));
gate #172 corroborated (waist⟺¬hpiv(1); hpiv monotone → stepasm's M₁<deepTailMin key confirmed). Plus (d) decorated-peel
[mid-size], O1/O3 [bounded], (e) M₁=1 [small, FILLING], gate reconciliation. BUILD-TO-THE-END: isolate O2
(SD-7), build everything above it. Not "mechanical assembly" — two cruxes + a potential wall, all mapped.

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
| **shellSpine_le_hsQ_box** (plumbing) | #2 aad3e6f2 (a8a42c82 stood down) | genm-sj5-headsplit-dom → @693bf5a5 | ★ DONE sorry-free clean-three. Full 5-step transport/Tonelli calc + NEW `measurable_hsQ_freedLoss_integral` (AEMeas via chartInner_schurShearFree_eq→frobSq_schur_split_inv→lintegral_prod_right). SIGNATURE: +`hZfMeas` on shellSpine_le_hsQ_box + call site (thread at assembly, from Brick F). hGmeas left as hyp (F2a not on base 7466eb8f; controller builds at integration on canonical where F2a lives → trivial). RouteMSJHeadSplitDom now has ONE sorry left = headSplit_pivotDom ⟹ head-split assembly gated on the pivotDom crux ALONE. |
| **pivotDom_finiteness** (crux, tide b) | a93e7b9c | RouteMSJPivotFin on genm-sj5-pivotdom @70ac68ea | RECONCILED (tide-b (3,3,3) gate + Codex xhigh). Confirmed my step-3-at-c' unsoundness; and showed BOTH my fixes flawed — (a) UNREALIZABLE: B₁₂·A_cor·Zf BILINEAR ⟹ freedLoss not jointly ‖linear‖², the 3.5 is the OUTER (z,A_cor) degeneracy stratum (fixed-outer codim=9, threshold 4.5≠3.5), A_cor can't be a D-B var; (b) chicken-and-egg: S3 needs A_cor-free pivot = the drop itself (ab/2-reduction+drop = ONE joint estimate). **ACTUAL decomposition:** step 1 = extraction RHS<⊤⟹c'<minAdm(M)/2 (SOUND+cheap, corner sublevel-VOLUME lb μ≳decLoss^{ab/2} + smearedSubBox_weighted_diverges) — GRIND NOW; step 2 = forward finiteness c'<minAdm(M)/2⟹LHS<⊤ = the bilinear-RLCT crux (~100s LoC; b>u failure window + uniform ratio lemma UNPINNED). DECISION (A)+(B) parallel. ★ STRUCTURE BANKED green @d45d5759 (→push genm-sj5-pivotfin, distinct from helper's genm-sj5-pivotdom): pivotDom_finiteness_impl u-split, wired to step1 `pivotDomRHS_lt_top_exponent` (sorry, GRINDING — sound, ~200-300 LoC, new corner sublevel-VOLUME lb) + step2 `forward_LHS_finiteness` (the isolated bilinear-RLCT crux, sorry, awaiting archfin pin) + u=0 sorry-free. BOTH sorries at SHARED threshold X=(minAdm(redChain u M)+peelCharge M u)/2, peelCharge=(M0−u)(M1−u)=ab — NO gap. FIDELITY RESOLVED: X=minAdm(redChain)/2+ab/2 ≥ minAdm(M)/2 (= only at binding cut), via banked `minAdm_le_peelCharge_add_redChain` (an INEQUALITY; the equality is hbind at the binding cut only). Head-split operates at c'<minAdm(M)/2≤X ⟹ step-2 hyp holds throughout; forward_LHS_finiteness at sharp cut-u X is TRUE, not overclaiming. Pushed origin/genm-sj5-pivotfin @91c01699. STEP-1: 4 helpers + decLoss identity (`pivotRHS_decLoss_eq` — the flagged-hard cornerComparator instance-junk RESOLVED) all DONE axiom-clean; extraction `pivotDomRHS_lt_top_exponent` turnkey-sorry'd (in-file 3-step note, ~85-120 LoC, NO wall). **tide-b RETIRED** (banked+pushed). **ROUTE SETTLED (step2 SPECIFY-catch):** Option-B σ-coupled DOMINATION `pivotDomLHS ≤ C·pivotDomRHS` (C<⊤ via D-A σ-coupled peel + D-B + S3) closed by `hRHS` — the step1-extraction/shared-X split was a DETOUR (uniform-C artifact); the extraction is DROPPED as vestigial (no downstream sig change; pivotDom_finiteness : RHS<⊤→LHS<⊤ unchanged, _impl just passes its hRHS to step2). **step2 tide** (a27134b, genm-sj5-step2): Option-B REWIRE DONE @55701f74 (RouteMSJPivotFin → 1 sorry = the peel; Brick F merged; vestigial extraction removed; no downstream sig change). PEEL clarified: frobSq_schur_split_inv cancels P⁻¹ → D-subst → clean block-front RLCT → row-split pivot(P|B₁₂)[D-A-radial, σ_i via P̂] + corank(C|D)[S3]. This IS the full headSplit_pivotDom crux (unbuilt); ~65-75%-new = the σ-coupled **C-ABSORPTION** (C·Q_p cross-term vs S3 fixed Ccross → charge ab, closes b>u; multi-hundred-LoC, cert-LABOUR, risky = adapted chart-constant lemma). PLAN (SD-7): scaffold sorry-free + isolate C-absorption as 1 precisely-stated sub-lemma → checkpoint for wall-vs-labour. #165/#166/#170 |
| **RHS≠0 + uzero** (helper) | aa56113 | genm-sj5-pivotdom → @4746bd2c | ★ DONE — pivotDom_RHS_ne_zero (@58568ab8) + pivotDom_uzero (@4746bd2c) both axiom-clean (forced #print axioms), pushed. RouteMSJPivotDom's only remaining sorry = pivotDom_finiteness (tide-b). Reviewer ac0ad4c0 verdict: BOTH SOUND (not vacuous, genuine integrand identities, ℕ-jc stress-test, Codex-corroborated, no green-but-wrong) — integration-ready modulo pivotDom_finiteness. Helper now building HeadlineL1Mint (_L1 + #108 prestage wrapper) at @10d69c43. |

`headSplit_pivotDom_impl` ratio wiring is sorry-free (GLUE-2 @19dd58ff = origin/genm-sj5-pivotdom); reduces to those 3 sorries.

## DOWNSTREAM LANES — FRONT-LOADED (2026-07-13, operator parallelization; pivotDom-INDEPENDENT)
Use tide-b's arch-correction-#2 grind hours (hours) to lock every downstream contract now, so pivotDom's close leaves only one-exact fills, not fresh design questions on mint day.
| Lane | Agent | Branch | Status |
|---|---|---|---|
| **DecoratedStepHyp skeleton + hole-fills** | stepasm a7673edf (RETIRING @clean checkpoint) | genm-sj5-stepasm @a34fe053 | ★ SKELETON DONE (`decoratedStepHyp_dispatch` sorry-free, green, 5 holes) + dispatch-fix @7a132673 (M₁<deepTailMin key) + 3 clean bricks @880f6ddb (`frobSq_rmatMul_mid_one`, `minAdm_le_minAdm_dropHead_of_mid_one`, + deepTailMin/minAdm lemmas). Waist (c) route-docs → SVD-qPeel+reorientation @a34fe053. FaithfulSJAt-(e) recipe MAPPED in-module (d=0: prod_headSplit→frobSq_rmatMul_mid_one→paramsHeadSplit_preimage_box→Tonelli→corankLeaf_rpow_lt_top@n=1 + hIH(dropHead,trivial); d≥1: +decLoss_clean_of_uniformResidualSupport+gammaPrimeClause+monomialIntegrand β). **ASSEMBLY COMPLETION = ONE post-adm-fix tide** (full (e)=FaithfulSJAt+corank; (b); (d); (c)=SVD-qPeel) — batched (FaithfulSJAt-(e) + corank-(e) are the same lemma). SCOPE: SCOPE IN — all 3 non-crux holes reduce to the coupled Γ×Z_tail integral (#4 `decoratedBase_routeA_of_leafForm` Tonelli-separates; Z_tail=prod(dropHead M)). **(d)** good connector = mid-size NEW tide (load-bearing = coupled→shellSpineIntegrand bridge + decorated shell-cover peel; rest banked); HOLD until gate recon + crux F/D. **(e)** M₁=1 = SMALL [stepasm FILLING now]: rank-1 factor ‖Γ‖²‖Z‖² + Tonelli + threshold split. **(b)** j=r = one-liner-or-small, gated on crux Q "does deeperFlag_spineToCore F/D hold at j=r (off-sector degeneracy)?" → head-split-assembly TRIGGER (collapse into (a) if yes). Waist (c) route = (b) drop-front (NOT reversal — dead). Seams → #171/#172. ★#172 RESOLVED: the skeleton's BINDING-CUT-hpiv dispatch is BUGGY (bindingCut=0 ⟹ 0≤0 trivially true ⟹ 356 waist chains / 1188 CEs mis-route to GOOD → divergence); FIX = dispatch on `M 1 < ⨅_{i≥2} M i` + derive good-branch per-cut hpiv via upper-bound lemma `minAdm(u,M₂..)≤u·min(M₂..)` [BANK]. stepasm applying (priority over (e)). |
| **Waist-connector design pin** | waistpin (pen-and-paper) | (no git; returns cert, controller homes) | Adjudicate hpiv-FAILING waist shells → banked `_mnp`. Witness→obstruction; route-B orientation REFUTED (avoid). Only remaining unpinned design. TARGET = the waist hole's required statement from the stepasm skeleton (I relay). BOUNDED-vs-WALL verdict + Codex. |
| **L=1 mint brick** (headline) | helper aa56113 (QUEUED after RHS≠0/uzero) | genm-sj5-l1mint | Unsuffixed #108 (∀L≥1) needs L=1 via a separate path (`_gen` carries 2≤L). SCOPE-FIRST before grinding. Consumes nobody's output; lands any time before mint. |

**Interface handoff:** stepasm reports the waist hole's required statement → I relay it to waistpin as its exact target. When pivotDom closes: headSplit_domination clean-three → DeeperFlagCore stubs → deeperFlag_spineToCore → DecoratedStepHyp (skeleton's holes filled) → DecoratedDescent → (□) → mint (L=1 brick + _gen).

## CRUX DE-RISK (parallel to tide-b; advisory-to-controller)
| Lane | Agent | Status |
|---|---|---|
| **step-2 forward-finiteness pin** (#170; was arch-#2 adjudication) | archfin (pen-and-paper) | REDIRECTED — (a)/(b) shown flawed by tide-b. Briefly confirm (esp. (a) bilinearity), then PIN the exact sound decomposition of the forward-finiteness crux `c'<minAdm(M)/2⟹LHS<⊤`: the b>u failure window (C via Ccross-uniformity/box-vol vs au-codim — verify OR find the sound route), the cross-term drop's UNIFORM angular/Jacobian ratio lemma near degenerating Q_p/Q_b (Codex: NOT implied by a.e. rank). BOUNDED-vs-WALL + exact new sub-lemmas. Returns to controller; NO cross-talk with tide-b. GATES whether tide-b grinds step 2 or isolates a correct-statement wall-sorry. |

## PLAN-AHEAD — post-pivotDom assembly sequence + triggers (controller-owned)
1. hGmeas: soft-asked to #2 (consumer-owner); fallback = controller builds from F2a at integration.
2. **TRIGGER — on stepasm's report:** it names the j=r saturated-shell hole's exact statement. Assess j=r = one-liner (IH application at reduced arity) vs needs-a-tide; commission immediately if the latter (pivotDom-INDEPENDENT — it's the IH, not the head-split). Also relay the waist hole's required statement to waistpin.
3. **TRIGGER — on archfin's report:** reconcile with tide-b's (3,3,3) gate; if they agree, tide-b's route is confirmed (raise confidence, let it grind); if they diverge, dig before tide-b sinks more hours.
4. **On pivotDom + #2 + helper landing:** merge headsplit-dom + pivotdom branches (inline pivotDom_finiteness → RouteMSJPivotDom, break hsQ cycle) → fill headSplit_domination → DeeperFlagCore stubs (exists_headSplitFrame := F1 impl; hGmeas; refinements hjr/hε'le=le_refl/hZfMeas from Brick F) → deeperFlag_spineToCore = F ∘ it → DecoratedStepHyp (fill stepasm's **5 holes**: (a) j<r=spineToCore [=pivotDom crux]; (b) j=r saturated=arity-IH [degeneracy, small]; (d) good peel+cover for ARBITRARY adm D [NEW decorated-peel, #171 scoping]; (c) waist M₁≠1=reversal→(d) on rev M [route-a, gated on commutation #172]; (e) waist M₁=1=rank-1 factorization [small]; + gate reconciliation #172) → DecoratedDescent (+#4 base) → (□) → mint (_gen ∘ discharge + L=1).

**MINT STRUCTURE (helper canonical-check 2026-07-13):** the unsuffixed `aoyagi_learning_coefficient` ALREADY EXISTS @Skeleton.lean:1685 (∀L≥1, hL:1≤L, via deepest_point_reduction+product_reduction) carrying **5 sorryAx rungs** (AxCheck: sorryAx-expected — the conditional headline). Stage-2 mint = **re-point that name** (controller-owned, operator-visible) to the CLEAN version: case-split [L=1 → `aoyagi_learning_coefficient_L1` (regular Morse, banked engine, helper building) ; L≥2 → `aoyagi_learning_coefficient_gen_of_descent hDescent`] with hDescent=(□). Helper pre-stages the wrapper as `aoyagi_learning_coefficient_prestage` on-branch (one hDescent hole); re-point on (□) landing. `_gen_of_descent`'s docstring already anticipates "L=1 folded in at mint".

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
