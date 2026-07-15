# recon-map.md — the AUTHORITATIVE #108 dependency-cone sorry-map (endgame ownership)

**Thread `genm-endgame-map` (self-recon, READ-ONLY). Produced 2026-07-15.** Closes the ownership gap
the controller flagged: it had been tracking Brick D narrowly; (v) is ALSO gated on Brick F, with
uncertainty on the crux's role. This is the git-verified dependency cone of the UNCONDITIONAL mint target
`aoyagi_learning_coefficient` (#108) — every REAL `sorry`/`sorryAx`, its home branch, and its owner-status.

Method: real `sorry`-tactic tokens + genuine `sorryAx` only (the naive substring grep = ~557 NOISE
hits: `sorry-free`, `sorryAx` comments, docstrings). Cone traced from the mint target down; OLD parallel
exploration (Core/, Validate/D1*/Deepest*/Case*/RouteMInterior*/DeepestGaugeChart …) EXCLUDED — not on
the #108 path. Cross-verified against the live branch tips (`git fetch origin` done), not just the log.

Base commits (short, at time of recon): canonical `expedition/aoyagi-full` @34e959256 /
`origin/expedition/aoyagi-full` @829eded89; brickdcont @0cc73285c (LIVE, advancing — was c5954d6cc at
session start); brickdbuild @2c3778837; brickdfin @9c748b6cd; brickF-wire @759fcf72a; step2 @e395121c9;
jreqb @c94e7fde0; good @8672869f6; waist @5e49d2361; holesbe @4068d740c; l1mint @85e6d7327;
mintrehearsal @2dc2682a. Brick F impl banked on canonical @5e114405.

---

## HEADLINE (what to reuse / what's open / the real bottleneck)

The mint is **one analytic brick from done, and that brick is Brick D — `headSplit_domination`.**

- The mint target `aoyagi_learning_coefficient_prestage (hDescent : DecoratedDescent)` is on canonical,
  **sorry-free modulo the `hDescent` HYPOTHESIS** (an honest hyp, NOT sorryAx). #108 = supply an
  unconditional `DecoratedDescent`.
- `DecoratedDescent = ∃ adm, (adm contains trivial) ∧ DecoratedStepHyp adm ∧ DecoratedBaseHyp adm`
  (`RouteMSJDecoratedRec:206`). Of the three: **`adm_trivial` DONE**, **`decoratedBaseHyp_faithful`
  (DecoratedBaseHyp) DONE** — both clean-three on canonical. The mountain is **`DecoratedStepHyp adm`.**
- `DecoratedStepHyp adm` = `decoratedStepHyp_dispatch` (a sorry-FREE 3-way dispatch) reducing to five
  holes. **(e) DONE, (c) analytic content DONE, (d)-connector DONE, (b) DONE-modulo-SD-7.** The only
  genuinely-open analytic content is **hole (a) strict-shell = `deeperFlag_shell_le` = Brick F ∘ Brick
  D**, plus the **SD-7** degenerate-corner reduction feeding (b).
- **Brick F is CLOSED** (wrapper wired sorry-free on `brickF-wire`; impl banked clean-three on canonical).
- **Brick D (`headSplit_domination`) is the ONE open analytic brick.** The old full-block route
  (finfin/shearfin/wallfin/flagpeel) was KILLED (target `frobSqBlockFull_lt_top` FALSE, thresholdhunt).
  The LIVE route is the **incidence-resolution** (`RouteMSJIncidenceChart*`, brickdcont) — pieces (i)+(iv)
  landed sorry-free, (ii) charts 4-5 in progress, (iii)/(v) pending, **assembly (v) + aggregate exponent
  gate are `bltj`-GATED** (the b<j mixed-degeneration soundness hunt — no cert yet).
- **The crux `pivotPeel_domination` is SORRY-FREE (step2, closed by rhsfin) but SHELL-0-ONLY (t2adjud) —
  it does NOT discharge the strict shell (a); it is SUPERSEDED for the (□) critical path by the
  incidence-resolution Brick D.** It survives as a valid banked j=0/shell-0 lemma only.
- **LANDMINE (load-bearing):** canonical's `deeperFlag_shell_le`/`headSplit_domination`/
  `deeperFlag_spineToCore` are **FALSE as stated** — they lack the upper bound `hcT : c' <
  carrierThreshold M`. The fix is landed on `brickdfin` (@9c748b6cd) and MUST be threaded through 4
  consumers before Brick D's @544 sorry can be honestly filled. This is a wrong-statement sorry, not a
  missing-proof sorry.

---

## (i) THE #108 DEPENDENCY-CONE TREE (each REAL gating sorry: name@file:line · home branch · owner-status)

Legend: ✅ DONE · 🔒 LANDED-AWAITING-MERGE (sorry-free on a branch, not yet on canonical) ·
🟡 ACTIVE LANE · ⛔ OPEN/BLOCKED · 🧩 rendezvous wiring (no math). "canonical" = `expedition/aoyagi-full`.

```
aoyagi_learning_coefficient  (#108, the unsuffixed name)
└─ MINT re-point (RELOCATE+REHOME; rehearsed @mintrehearsal 2dc2682a) 🧩 controller
   └─ aoyagi_learning_coefficient_prestage (hDescent)      HeadlineL1Mint.lean:77 · canonical · ✅ sorry-free mod hDescent
      ├─ aoyagi_learning_coefficient_L1                    HeadlineL1Mint.lean:41 · canonical · ✅ clean-three
      ├─ aoyagi_learning_coefficient_gen_of_descent        RouteMSJMint.lean:41   · canonical · ✅ clean-three
      └─ hDescent : DecoratedDescent  ── THE OPEN INPUT ──  RouteMSJDecoratedRec:206
         ├─ adm_trivial (htriv)                            RouteMSJAdm.lean       · canonical · ✅ clean-three
         ├─ decoratedBaseHyp_faithful (DecoratedBaseHyp)   RouteMSJBaseHyp:395    · canonical · ✅ clean-three
         └─ decoratedStepHyp_dispatch (DecoratedStepHyp adm)  RouteMSJDecoratedStep:651 · jreqb · dispatch sorry-FREE
            │  (dispatch key: M 1 < deepTailMin M → waist ; else good — waistpin #172 sound key)
            ├─ (e) deeperFlagWaistM1_finite  [waist, M₁=1]  RouteMSJDecoratedStep:484 · jreqb/holesbe · ✅ FILLED clean-three
            ├─ (c) deeperFlagWaist_finite    [waist, M₁≠1]  RouteMSJDecoratedStep:441 · jreqb · ⛔ sorry@449
            │     └─ deeperFlagWaist_finite_impl           RouteMSJWaistConnector:88 · waist @5e49d2361 · 🔒 sorry-free BODY
            │        ├─ O2 routeMLayerBoxIntegral_comp_rev (reversal CoV)  RouteMSJWaistReversalCoV · waist · ✅ clean-three (o2cov)
            │        ├─ deepTailMin_rev_le_of_waist         RouteMSJWaistConnector · waist · ✅ clean-three (general ∀L∀M)
            │        ├─ (d)-call: deeperFlagGood_finite (rev M)  ── see (d) below (good) · 🔒
            │        └─ O1 hred  = decoratedBoxThresholdFinite_of_routeMBoxThresholdFinite  · 🧩 controller EXTRACTS at rendezvous from GoodConnector
            ├─ (d) deeperFlagGood_finite     [good]         RouteMSJDecoratedStep:416 · jreqb · ⛔ sorry@423
            │     └─ deeperFlagGood_finite_impl             RouteMSJGoodConnector:331 · good @8672869f6 · 🔒 SORRY-FREE clean-three
            │        │  (peel@bindingCut + cover by singularShells jf∈{0..r}; consumes 3 per-shell hyps:)
            │        ├─ hstrict [1≤jf<r]  ⇐ (a)  ── see (a) ──                              · ⛔ (Brick D)
            │        ├─ hsat    [jf=r]    ⇐ (b)/SD-7 ── see (b) ──                          · ⛔ (SD-7)
            │        └─ hsector [jf=0]    ⇐ RouteMSJSectorBorderline (hsecfix) · 🔒 analytic DONE; composes w/ Brick D/F 🧩
            ├─ (a) deeperFlagStrictShell_finite [strict shell] RouteMSJDecoratedStep:254 · jreqb · ⛔ sorry@269
            │     └─ eventual fill = deeperFlag_shell_le (below)                            · ⛔ (Brick F ∘ Brick D)
            └─ (b) deeperFlagSaturatedShell_finite [jf=r]   RouteMSJDecoratedStep:327 · jreqb · ✅ sorry-free MODULO SD-7
                  └─ SD-7 deeperFlagSaturatedShell_reduce   RouteMSJDecoratedStep:315 · jreqb · ⛔ sorry@315  (see ORPHAN list)

  ── the (a)/hstrict + hsector + SD-7 all bottom out on the head-split chain ──
  deeperFlag_shell_le                       RouteMSJDeeperFlagCore:750 · canonical · sorry-free BODY, carries sorryAx via:
   ├─ exists_headSplitFrame  (BRICK F wrapper)   RouteMSJDeeperFlagCore:501 · canonical=⛔sorry
   │    └─ CLOSED 🔒 on brickF-wire @759fcf72a  (body := exists_headSplitFrame_impl · pure wiring)
   │         └─ exists_headSplitFrame_impl / measurableEigendecomp  RouteMSJHeadSplitFrame:181 · canonical @5e114405 · ✅ clean-three
   ├─ headSplit_domination   (BRICK D)           RouteMSJDeeperFlagCore:544 · canonical=⛔sorry  ★ THE OPEN BRICK
   │    └─ LIVE ROUTE = incidence-resolution (brickdcont, RouteMSJIncidenceChart*):
   │         ├─ (i)  transverseSchurGram / det_chartGram      RouteMSJIncidenceChart   · brickdcont · ✅ landed sorry-free
   │         ├─ (iv) per-stratum exponent gate (clsCodim…)    RouteMSJIncidenceExponent· brickdbuild· ✅ landed sorry-free
   │         │        └─ AGGREGATE min_{ℓ,s} C_{ℓ,s}/2 = T1  · ⛔ bltj-GATED (index-completeness; NOT the 332-sweep)
   │         ├─ (ii) charts 4-5 CoV  (Chart4Polar / Chart5BigCell)  · 🟡 brickdcont (ch4) + chart5recon/genm-sj5-chart5 (ch5)
   │         ├─ (iii) null-overlap gluing                     · ⛔ PENDING (no distinct owner; brickdcont continuation)
   │         └─ (v)  incidenceCell_lintegral_le → G<⊤ → domination → deeperFlag_shell_le · ⛔ PENDING + bltj-GATED (wiring point into canonical)
   └─ hcT : c' < carrierThreshold M  (LANDMINE upper bound)  · MISSING on canonical · 🔒 fix on brickdfin @9c748b6cd · 🧩 thread 4 consumers

  bltj (soundness gate)  — b<j mixed-degeneration hunt (r≥3, upper j-range: j−b weak σ forced into Q_p not Q_b)
     · 🟡 LIVE pen-and-paper · GATES (iv)-aggregate + (v)-assembly · NO cert yet (genm-bltj/mixdegen-cert.md not written)

  crux pivotPeel_domination                 RouteMSJPivotFin:1240 (step2)/:253 (good/waist stale) · step2 @e395121c9
     · ✅ SORRY-FREE + clean-three (closed by rhsfin; E/B done) BUT SHELL-0-ONLY (t2adjud) ⇒ NOT on the (a)/(b) critical path.
     · Stale copies still carry sorry@267 on good/waist (the pre-rebuild generation) — rvprep read one of these.
```

### The DONE / banked pieces to REUSE (do not rebuild)
- Contract + mechanical driver: `routeMBoxThresholdFinite_of_decoratedDescent`, `decoratedBoxThresholdFinite_of_decoratedStep` (RouteMSJDecoratedRec) — clean-three.
- `adm := genuineCarrier D ∧ FaithfulSJAt D` (RouteMSJAdm:194 — **corank disjunct DROPPED**; the #1 adm soundness bug is FIXED on canonical), `adm_trivial`, `cornerComparator_adm`, `decoratedBaseHyp_faithful` — all clean-three on canonical.
- Brick F impl (`exists_headSplitFrame_impl`, `measurableEigendecomp`) — canonical @5e114405.
- D-A `pivotBlock_radial_blowup`, D-B `lintegral_cube_frobSq_neg_of_finrank_range`, D-C `finrank_add_weakCount_le`/`shell_subset_goodSet` — canonical (feed the incidence resolution).
- L=0 base `routeMBoxThresholdFinite_mnp` — canonical (the track-(b) leaf; every triple incl. waists).
- hole (e) fill + (b)-modulo-SD-7 (jreqb); (d) connector `deeperFlagGood_finite_impl` (good); (c) connector `deeperFlagWaist_finite_impl` + O2 reversal CoV (waist); hsector `RouteMSJSectorBorderline` (hsecfix); mint pre-stage + L1 (canonical/l1mint) + re-point rehearsal (mintrehearsal).

---

## (ii) THE ORPHAN LIST (gating sorries with NO active owner — actionable)

An orphan = a gating sorry whose owning lane has RELEASED and whose fill is not covered by a LIVE lane.

1. **SD-7 `deeperFlagSaturatedShell_reduce`** (RouteMSJDecoratedStep:315 · jreqb) — **the clearest orphan.**
   - jreqbuild (owner) RELEASED. Its verdict: SD-7's j=r finiteness = "finfin's S3 ∀j finiteness — no
     cheaper independent route." But finfin's route was KILLED. So SD-7 must either be covered by the
     incidence-resolution Brick D at the degenerate corner `min(a,b)=0` / `peelCharge=0`, or needs its
     own lane. **This is UNRESOLVED** (the finfin coverage caveat explicitly flagged j=r as SEPARATE; and
     bltj's b<j hunt covers the upper j-range, adjacent to but not obviously identical to j=r).
   - ACTION: assign an owner (or confirm the incidence Brick D discharges j=r). Do NOT assume it
     auto-closes — the "j=r = Brick D content" claim is a coverage claim that has bitten before.

2. **Brick D (iii) null-overlap gluing** and **(v) assembly `incidenceCell_lintegral_le` → `headSplit_domination`** — no DISTINCT active owner.
   - brickdcont is LIVE on (ii)-chart-4; chart5recon/genm-sj5-chart5 on (ii)-chart-5. (iii) and (v) are
     "PENDING" with no named lane; (v) is additionally `bltj`-GATED (statement-shape frozen only once
     bltj clears). These will presumably fall to brickdcont post-charts, but are currently unowned.
   - ACTION: earmark brickdcont (or a fresh lane) for (iii)+(v) once charts + bltj land; the aggregate
     exponent gate `min_{ℓ,s} C_{ℓ,s}/2 = T1` (general nat proof, NOT the 332-sweep) is part of (v)/(iv)
     and is bltj-gated — this is the last general-proof obligation on the resolution side.

3. **`bltj` soundness gate itself** — LIVE agent, but NO cert produced yet (`genm-bltj/mixdegen-cert.md`
   absent). This is the true CURRENT bottleneck: (iv)-aggregate + (v) cannot be honestly assembled until
   bltj returns (a)/(b)/(c). It is not an orphan (it is owned + live) but it GATES the whole Brick D close.

**Not orphans (owned or pure wiring):**
- Brick F wrapper @501 — 🔒 landed on brickF-wire.
- (a)/hstrict wiring, hsector composition, (c) O1 `hred` extraction, LANDMINE `hcT` threading, mint
  re-point — all 🧩 rendezvous/controller wiring (no new math), blocked on Brick D.
- crux `pivotPeel_domination` sorry@267 on good/waist — a STALE copy; superseded by step2's sorry-free
  clean-three crux. Not gating (and the crux is off the (a)/(b) path anyway).

---

## (iii) MERGE ORDER (to assemble #108)

The rendezvous plan in `endgame-lanes.md` (§RENDEZVOUS, file-level assembly via asmbase on a fresh
`genm-sj5-rendezvous`) was written for the OLD full-block crux route and is SUPERSEDED by the
incidence-resolution Brick D. Corrected order:

1. **Finish Brick D (the gate).** `bltj` returns a verdict on the b<j mixed-degeneration soundness →
   freezes the (v) statement shape → charts 4 (brickdcont) + 5 (chart5) land → (iii) null-overlap +
   aggregate exponent gate → (v) `incidenceCell_lintegral_le` assembles → wire `headSplit_domination`@544
   := the incidence `_impl`. This is the critical path; everything below is wiring behind it.
2. **Merge the LANDMINE fix** (brickdfin @9c748b6cd): add `hcT : c' < carrierThreshold M` to
   `deeperFlag_shell_le`/`headSplit_domination`/`deeperFlag_spineToCore` + thread the 4 consumers
   (ShellCover / DecoratedStep / DeeperFlagShell / AxCheck). Do this BEFORE filling @544 (the @544
   statement is FALSE without it).
3. **Merge Brick F wrapper** (brickF-wire @759fcf72a): `exists_headSplitFrame` := impl (byte-identical
   statement, no cycle). Small; can land any time.
4. **Assemble `DecoratedStepHyp`** (fresh downstream file per rvprep's T5 re-home, to break the
   connector→DecoratedStep→(d)-stub import cycle):
   - DecoratedStep dispatch + (e) + (b)-modulo-SD-7 from **jreqb**;
   - wire (d) `deeperFlagGood_finite` := `deeperFlagGood_finite_impl` (**good**), supplying hstrict (=(a)
     via deeperFlag_shell_le), hsat (=(b)/SD-7), hsector (=**hsecfix** borderline);
   - wire (c) `deeperFlagWaist_finite` := `deeperFlagWaist_finite_impl` (**waist**) + O1 `hred` extraction
     + the (d)-call on rev M (**good**);
   - fill (a) `deeperFlagStrictShell_finite` := `deeperFlag_shell_le` (now Brick F ∘ Brick D + hcT);
   - close SD-7 (see ORPHAN #1 — assign or confirm-via-Brick-D).
5. **Bundle `DecoratedDescent`** := ⟨adm, adm_trivial, [assembled dispatch], decoratedBaseHyp_faithful⟩;
   discharge `_gen`'s `hbox`; re-point the unsuffixed `#108` (mintrehearsal recipe: `_legacy` rename +
   HeadlineL1Mint re-home + AxCheck true-mint). Mint-vacuity caveat: nondeg ⟹ `minAdm ≥ 1`
   (`one_le_minAdm_of_pos_general`, already load-bearing) — record beside the claim, no new obligation.
6. **Final gate** (controller): force-recompiled `#print axioms` clean-three on the assembled
   `DecoratedDescent` + `aoyagi_learning_coefficient`; delete `_legacy` + rehearsal harness; single-writer
   AxCheck.

**Where the current live lanes plug in:** `brickdcont` = step 1 Brick D (charts + resolution);
`bltj` = the step-1 soundness GATE that unblocks (v); `chart5recon`/genm-sj5-chart5 = step-1 chart 5.
Everything in steps 2-6 is wiring/assembly that waits on step 1.

---

## (iv) DISCREPANCIES WITH rvprep's READ (2026-07-15)

rvprep's structural read is CONFIRMED where it overlaps canonical; the deltas are all "rvprep read a
stale feature branch or the pre-thresholdhunt architecture":

1. **Crux `pivotPeel_domination` "PivotFin:267 still 1 sorry" — STALE + role-superseded.**
   - rvprep read the OLD generation (`good`/`waist`: `pivotPeel_domination`@253, sorry@267). On the CURRENT
     crux branch **step2 @e395121c9 the crux is SORRY-FREE + clean-three** (rebuilt, `pivotPeel_domination`
     now @1240; E/B closed by rhsfin; rhsfin RELEASED). PivotFin:267 on good/waist is `blockFront_rowSplit`
     or a stale copy, not the live crux.
   - MORE IMPORTANT: **the crux is SHELL-0-ONLY** (t2adjud OBSTRUCTION cert: `shellSpine_le_hsQ_box` FALSE
     for j≥1; `pivotShell` = shell-0 exactly). So even sorry-free it does **NOT discharge the strict shell
     (a) [1≤j<r] or (b) [j=r]** — the "crux discharges (a)/(b)/(d)-hsector" ledger claim was an OVERCLAIM.
     **Answer to the controller's Q2: the crux is SUPERSEDED by the incidence-resolution Brick D
     (`headSplit_domination`); it is NOT on the (□) critical path** (kept only as a valid j=0/shell-0 lemma).
     rhsfin is RELEASED (crux done); there is no residual crux sorry to own.

2. **Brick F — rvprep/controller "wrapper still carries sorryAx".** True on CANONICAL (@501), but the
   wrapper is **CLOSED sorry-free on brickF-wire @759fcf72a** (`:= exists_headSplitFrame_impl`, banked
   clean-three on canonical @5e114405). So Brick F is 🔒 landed-awaiting-merge, not open.
   **Answer to Q1: Brick F CLOSED (brickF-wire), impl banked; only a small merge remains.**

3. **rvprep: "(v) deeperFlag_shell_le has sorry-free body carrying sorryAx via just 2 named sorries
   (F@501 + D@544)."** CONFIRMED exactly on canonical (the only 2 real cone sorries on canonical).

4. **DecoratedStepHyp branches (Q3):** all five accounted — **(e) DONE, (c)/(d) connectors DONE
   (sorry-free `_impl`s on waist/good), (b) DONE-modulo-SD-7. The genuinely-open ones are (a) [=Brick D]
   and SD-7 [j=r reduction].** rvprep noted the connector layer has "ZERO canonical presence — all on
   feature branches" — CONFIRMED (DecoratedStep, GoodConnector, WaistConnector, Incidence* are
   feature-branch-only; canonical carries only the contract + the 2 DeeperFlagCore sorries).

5. **The LANDMINE (`hcT` upper bound) — canonical's `deeperFlag_shell_le`/`headSplit_domination`/
   `deeperFlag_spineToCore` are FALSE AS STATED without it.** Fix landed on brickdfin @9c748b6cd; NOT yet
   on canonical. This is a wrong-statement sorry at @544 — flag prominently so Brick D isn't filled
   against the false statement. (rvprep's SCOPE-A "hjr vestigial" was already self-corrected to false;
   the hcT threading is the live version of that concern.)

6. **`adm` #1 soundness bug — RESOLVED on canonical** (`adm := genuineCarrier ∧ FaithfulSJAt`, corank
   disjunct dropped, RouteMSJAdm:194). Not a discrepancy, but load-bearing: every branch's `adm` must
   match canonical's fixed form at merge (verify — divergent branches that predate the fix could carry
   the old 3-disjunct `adm`).

---

## Caveats on this map
- The DecoratedStep assembly file diverges across branches (jreqb 661 LoC is most-advanced; good/waist/
  hsecfix/rescopefin/stepasm/holesbe carry the 335-LoC skeleton). The hole↔connector hyp shapes (jreqb's
  (a)/(b) vs good's hstrict/hsat/hsector) differ and must be reconciled at assembly — a wiring detail, not
  new math, but non-trivial.
- brickdcont is a LIVE lane (tip advanced c5954d6cc→0cc73285c during this recon); its exact internal
  sorry/chart state is fluid. The structural claim (i landed, iv landed, ii in progress, iii/v pending +
  bltj-gated) is from the controller-owned `endgame-lanes.md` (2026-07-14/15) cross-checked against the
  branch tip (RouteMSJIncidenceChart + RouteMSJIncidenceExponent present + sorry-free; Chart4Polar/
  Chart5BigCell not yet on the pushed tip).
- Authoritative trail: `endgame-lanes.md` (controller-owned, current through 2026-07-15) > `synthesis.md`
  numbered UPDATEs (stop at 1047 / 2026-07-13). This map is consistent with both.
