# The owed register — owed math + owed paper results (standing elder audit)

**Charge (operator, 2026-07-21):** a standing audit of (1) OWED MATH — insufficient generality and
incomplete object API against charter bar (i), and (2) OWED PAPER RESULTS — statements Aoyagi proved
that the plan does not yet include. **Author:** elder (sole; controller commits). **Cadence:** full
pass at wave-open (this document, against tip `03b20225b`); event-updates at leaf landings / API
changes; feeds the close-phase synthesis and the next-expedition runway.

**Guardrails in force:** detail-at-scale = build, monument = cite; known-defect ledger not re-flagged;
statement soundness is rev-leaves' lane — this register is about MISSING BREADTH. Interaction with the
live wave is read-only EXCEPT statement-level generality defects on a live leaf (stop-on-suspect).

**Sweep-pairing (standing, learned 2026-07-21):** every status in this register is a READING until
ground-truthed against the tree — the auditor's corpus is the tree, not any brief's module list;
full-tree grep for the entry's target statement is the minimum bar before OPEN is written. The
office's form is the PAIR: the elder authors, seat-api ground-truths. Evidence for sweep 1:
[threads/39-register-sweep/sweep-1-evidence.md](threads/39-register-sweep/sweep-1-evidence.md).

Entry format: `id — what is owed — wires at — class — price (S/M/L; strike-able/frontier/runway) —
recommendation — status`.

---

## §0 Seed: the O-series (from `verify-owed-math-audit.md`), status-updated

- **O1** — the atlas min-over-charts CoV equality — `ProductResolution.rlctAt_sumSqFam_eq_iInf_charts`
  — paper-silent (our properness surrogate) — L, strike-able — IN STRIKE. Substrate landed:
  `AreaFormula.lintegral_image_eq_lintegral_abs_det_fderiv_mul_of_injOn_off_null`. Note folded in: the
  ∫⁻-to-`IntegrableAtFilter` (real) bridge is PART OF O1's remaining price (see M12). — OPEN/live.
- **O2** — the monument — now = the 8-leaf foldState programme (`MonumentAtlas` + `PrincipalInv`);
  the wall = `case1_preserves_stepInv` at the fold's concrete states — L, frontier (the wall) +
  strike-able shell — IN STRIKE (wave). — OPEN/live.
- **O3** — the general-rank (r > 0) lane — see P3 for the precise sub-list — L, runway — DEFER, named.
- **O4** — non-monotone `d` via permutation transport — `LearningCoefficient` (named future leaf) —
  M, strike-able — wave-tail candidate AFTER the monument (independent seat). — OPEN.
- **O5** — cCodim ↔ the paper's printed Thm-2 / clean q²−m² form, ∀(L,M) — see P2; RE-PRICED DOWN:
  `DLN/Aoyagi/ClosedForm.lean` already carries the apparatus (`lambdaCore`, `residueA`, the
  `residueA_mul_sub_eq_qipDelta_abs_mul_sub` bridge) and the proof skeleton is p.23's
  completing-the-square (image-read) — M, strike-able — WAVE-TAIL UNIT recommended. — OPEN, re-priced.
- **O6** — Object E order ρ — see P6/P7; combinatorial half RE-PRICED DOWN by the foldState spine —
  deferred-in-reach per charter §1-E. — OPEN, re-priced.
- **O7** — (a) φ-form Def-1 equivalence (cheap, runway — P8); (b) free-energy identification
  (permanent cite — P11). — OPEN by design.
- **O8** — deeper-mix chain survival — DISSOLVED under M'=1 (b₁ truncation-stability; subsumed by
  L4/L5). — **DISCHARGED**.
- **O9** — the block-center blow-up atom — `BlockBlowup.lean` LANDED (map + structure lemmas
  sorry-free; `jacDet_blockBlowupMap` + `injOn_blockBlowupMap` pinned as the seat-w0l3 leaf, off the
  driver cone). — **LANDED/in-strike** (the two pinned proofs remain).

---

## §1 OWED MATH (axis 1: generality + API completeness)

### Flagged prominently (fix-at-next-touch; not a formal stop — the leaves are not being struck now)
- **M5** — SPURIOUS `hd : Monotone d` on `leaf_stepInv_of_path` (L5) and `leafPath_realizesExponents`
  (L8): neither statement consumes monotonicity (L5's fold and the tree are hd-free; L8 references
  `minAdm` only — the qipMin tie that needs hd lives in `RecursionAdapter`, correctly). The drivers
  (`exists_atlasRealizesExponents`, `…_via_monument`) consume hd legitimately (qipMin). Same class as
  my leaf-binder exclusion ruling — bar (i), a promise of less generality than the statement has. —
  `MonumentAtlas.lean:492,571` — generality — S — fix at next arch-C touch of the file (with rev-leaves
  noting the diff); do NOT open a dedicated round. — OPEN.

### Wave-tail API units (S, strike-able, high reuse)
- **M1** — the UNWEIGHTED monomial-rule corollary: `rlctAt (sumSqFam (monomialFam e)) 0 =
  monomialThreshold (e k₀) (fun _ ↦ 0) hbind` (W = 1, h = 0 — the classical monomial-ideal RLCT,
  THE citable Mathlib-grade form). One `wrlctAt_one` rewrite from the landed C rule. —
  `MonomialRLCT` — API — S — wave-tail; highest external-reuse value per line in the library. — OPEN.
- **M2** — `StepInv.mono` / `PrincipalInv.mono` (restriction to a subregion `V' ⊆ V`): the wiring
  NEEDS these (terminal_bezout shrinks; L6 consumes on the shrunk region). — `PrincipalInv` — API —
  S — wave-tail NOW (the L5/L6 seats will otherwise inline them twice). — OPEN.
- **M8** — `RegionRepresents` composition + restriction API (transitivity; `V' ⊆ V` monotonicity;
  the `Fin 1`-family simp normal form L1 repackages by hand). — `IdealInvariance` — API — S —
  wave-tail. — OPEN.
- **M3** — `pathMap_append` (`pathMap (l₁ ++ l₂) = pathMap l₁ ∘ pathMap l₂`) + the corresponding
  jacDet product over a list — the fold's induction will want both. — `PathAtoms` — API — S —
  wave-tail. — OPEN.

### Hygiene-pass items (S, no consumer blocked)
- **M4** — deprecate-to-corollary: once O9's `jacDet_blockBlowupMap` lands, `OriginBlowup.
  jacDet_blowupMap` should become the `S = univ` corollary via the landed `blockBlowupMap_univ`, and
  its `2 ≤ D` guard audited as artifact (at D = 1 the map is `id`, det = 1 = (w p)^0 — the general
  form needs no guard). The old atom must POINT AT the general one, not stand as a parallel proof. —
  `OriginBlowup`/`BlockBlowup` — generality — S — hygiene pass post-O9. — OPEN.
- **M9** — `BlockDivision` is ℝ-pinned; its identities are polynomial and CommRing-generalizable
  exactly as `WeightedCofactor` was (the model instance: general `ι`, `X`, `CommRing 𝕜`). No kill-path
  consumer needs it; do it when the module is next touched or at upstreaming. — generality — S —
  hygiene/runway. — OPEN.
- **M13** — `monomialThreshold` reindex/permutation-invariance API (relabeling `Fin D`); an outside
  user reindexing coordinates has `conjResolution` for charts but nothing for the threshold. —
  `MonomialRLCT` — API — S — runway. — OPEN.

### Runway (M/L, next expedition or upstreaming pass)
- **M7** — the A-layer (and `wrlctAt`) is `Fin n → ℝ`-pinned where `RLCT.Global` is already
  polymorphic; the Mathlib-grade form states ideal-invariance over a general measure space carrier.
  Inherited pinning from `RLCT.Local`, not A's own choice — lift the whole layer at once, not A alone.
  — `IdealInvariance` + `Core.Analysis.RLCT` — generality — M/L — runway (upstreaming pass). — OPEN.
- **M6** — `conjResolution` is 0-pinned (`Resolution G 0`) while `Chart`/`Resolution` are x₀-general;
  the missing companion is the translation transport (`Resolution F x₀ ↔ Resolution (F ∘ (· + x₀)) 0`).
  No current consumer. — `ConjResolution` — API — S/M — runway. — OPEN.
- **M10** — `Resolution` union/refinement/restriction API (combine two atlases; restrict `U`); the
  kill-path builds one atlas directly, so no consumer yet — but any multi-stage resolution reuse will
  want it. — `ProductResolution` — API — M — runway. — OPEN.
- **M11** — `LocallyNullZeros` discharge for ANALYTIC (non-polynomial) families — the paper's own
  generality; ours needs only polynomial (`Waypoint.locallyNullZeros_sumSqFam_of_polynomial`).
  Requires analytic-zero-set-null, which Mathlib may lack. — `Waypoint` — generality — M — runway
  (flagged since the v4 round). — OPEN.
- **M12** — the real-integral (Bochner/`IntegrableAtFilter`) face of the `AreaFormula` ∫⁻ lemma —
  consumed inside O1's proof; not a separate leaf, PRICED INTO O1. — `AreaFormula`/O1 — API — S —
  in-strike with O1. — OPEN (tracked under O1).

### Staged obligations already locked (recorded here so the register is complete)
- **M14** — `foldRegion ≡ univ` stand-in: acceptable while StepInv rides global polynomial
  identities; the L6 Chart `nbhd` MUST be the terminal-shrunk bounded `V'` (round-5 (d) HARD LOCK,
  in L6's docstring; the gate refuses `nbhd = univ`). — `MonumentAtlas` — staged — carried. — LOCKED.
- **M15** — `foldNR` parent-count padding: benign iff the padding slot is the absorbed cleared entry;
  rev-leaves watches the eventual L3 proof for padding exploitation (round-5 (b) tripwire). — staged
  — carried. — LOCKED.
- **M16** — `TreeEdge.center/pivot` free fields + the documented derivation spec: sound under the (B)
  `SupportedOn` hypothesis; the fold-determined def-body is bridge-blocked (see P12/runway — the
  flatDim card↔sum coordinate bridge). — staged — carried. — LOCKED.

---

## §2 OWED PAPER RESULTS (axis 2: her theorem inventory vs the plan)

Inventory basis: the worked reproduction + the elder page-image passes (pp.08, 10–26 all read;
load-bearing displays image-verified). Not re-listed: results LANDED (Lemma 1 = A; the boxed S2 rule
under her chain = C; the deepest-point instance = GlobalHomog; the codim/QIP layer = D) and the
monument-in-plan (pp.14–22 recursion = the 8 leaves).

- **P1** — **Theorem 1 (RRR / L = 2 closed form + order)** — "for the L=2 model, λ and θ are given by
  the four-regime closed form." NOT stated in Lean. Machinery: at r = 0 it falls out of the engine
  corollary + O5's bridge at L = 2 (`ClosedForm` has the apparatus); at r > 0 it needs P3. —
  wires: a new `DLN.Aoyagi.RRR` instance module — M (r=0 instance; strike-able) / L (full) —
  recommend: r=0 λ-instance as a WAVE-TAIL unit (a strong external-facing deliverable: the classical
  Aoyagi–Watanabe RRR value, engine-derived); full Thm 1 to runway with P3. — OPEN.
- **P2** (= O5) — **Theorem 2's printed value form** — "λ_core = a(ℓ−a)/4ℓ − … + ½ΣMM (equivalently
  ½(Σq² − Σm²))." Owed: the equality `(cCodim d 0).toNat = 2·lambdaCore d 0`-class theorem ∀(L,M)
  (enumeration-verified L ≤ 6 only). Proof skeleton = p.23 completing-the-square + Lemma 3 (p.24,
  image-verified); `ClosedForm.residueA…qipDelta` is the bridge already under construction. — wires:
  `ClosedForm` ↔ `Core` QIP layer — M, strike-able — WAVE-TAIL UNIT (also unlocks P1). — OPEN.
- **P3** (= O3) — **the general-rank lane**, precisely: (i) Thm 3 as stated (the gauge-slice normal
  form — Skeleton #44's content, old carrier); (ii) Thm 4 in HER form (sub-block homogeneity,
  admissible φ — ours covers full-variable homogeneity only); (iii) the regular-block Fubini splice
  (`n/2` shift) on the NEW carrier; (iv) transport of the engine corollary from `lossDLN d 0` to
  `lossDLN d B`, rank r. Nothing on the kill-path consumes it. — L, runway — DEFER, named as the
  follow-on expedition's natural headline (with P10). — OPEN.
- **P4** — **Theorem 4, her general form** — folded into P3(ii); recorded separately because it is
  also the only place her paper leans on [22]/Aoyagi-2013 — any build should re-derive, not cite,
  per the standing discipline. — runway. — OPEN.
- **P5** — **Lemma 2 (block elimination, regular pivot)** — DISCHARGED-equivalent: banked as the
  `RankNormalForm`/Schur layer (`Core/RankNormalFormDim.lean`, `Core/RingTheory/Determinantal/
  Schur.lean`); the r=0 recursion needs only the pivot-1 case (shear-pin). No action. — **DISCHARGED**
  (pointer recorded).
- **P6** — **Lemmas 4–5, the combinatorial order θ = a(ℓ−a)+1** — RE-PRICED by the foldState spine:
  the branch/chart enumeration and the per-leaf ledger data that Lemma 4's two-condition
  characterisation counts are now first-class (`TreePath`, `FoldProduced.leafOf`, the divExp ledger) —
  the combinatorial half drops from L to M (ℕ-arithmetic over the tree + the two envelopes,
  worked.tex §order transcribes both conditions). Still deferred-in-reach per charter §1-E; when the
  operator re-opens E, START HERE. — wires: `Order.boxedOrder` aggregate + a new tree-count module —
  M, strike-able — deferred per §1-E, price updated. — OPEN.
- **P7** — **the analytic pole-order identification** (ρ = zeta multiplicity) — unchanged: blocked on
  meromorphic continuation Mathlib lacks; monument-class. — cite/defer (with E). — OPEN by design.
- **P8** (= O7a) — **Def 1's φ-form and φ-independence** — a bump-function comparison; cheap;
  interpretive fidelity only. — S/M, runway. — OPEN.
- **P9** — **the full `diag(b₁,…,b_M)` terminal normal form as a statement** — her terminal display;
  our M'=1 compression is value-equivalent (ratified) and the full form has NO consumer; it falls out
  of the path ledger if ever wanted. — runway API note only. — OPEN (no action).
- **P10** — **her Main Theorem in her generality** (all width orders × all r ≤ min-width × printed λ
  and θ) = P2 + P3 + O4 + P6 composed. The honest name for a FOLLOW-ON expedition; nothing in the
  current destination requires it (the charter corollary is the zero fibre). — runway headline. — OPEN.
- **P11** (= O7b) — the free-energy/learning-coefficient interpretation — permanent cite (charter
  destination wording). — CLOSED by design.
- **P12** — the `RLCT.flatDim` (card) ↔ `Aoyagi.flatDim` (sum) coordinate bridge — paper-silent,
  Lean-only; ruled runway at round-4 (value-level ties suffice for the kill-path); blocks only M16's
  def-body and the structural chart↔leaf correspondence. — runway. — OPEN.

### The inverse list (we build, she never proves — this is the wave's honest price; CONFIRMED complete)
The compact-dom a.e./full cover (L7); the atlas-min CoV equality (O1 — her boxed rule is in-paper
cited-class); the terminal Bézout inversion (implicit in her ideal display); a.e.-injectivity /
birationality bookkeeping (implicit); the region discipline (absent — all germs); the `SupportedOn`
center-support linkage (her definitional center); the deterministic foldState vocabulary (her
Let-blocks); the measure-preserving LINEAR flatten + `he_lin` guard (Lean-carrier only; the guard is
codex-found, no paper analogue); the junk-0 and measurability guards (Lean-convention honesty);
Watanabe-upper — NOT separately owed: her per-chart boxed EQUALITY (= O1) subsumes both bounds, and
both cites die together at the monument (re-confirmed; nothing else is owed there).

---

## §3 Event log
- 2026-07-21 — register created (tip `03b20225b`, wave opening); O-series folded in; O8 discharged,
  O9 landed-in-strike, O5/O6 re-priced; M1–M16, P1–P12 opened. Wave-tail recommendations for the
  briefs: **M1, M2, M8, M3 (API units) + P2/O5 (the printed-form bridge) + P1-at-r=0 (the RRR
  instance)**; M5 flagged fix-at-next-touch.

---

## §3 CORRECTIONS — sweep 1 (elder-authored 2026-07-21; evidence: threads/39-register-sweep/)

STATUS FLIPS: **O1 → LANDED** (rlctAt_sumSqFam_eq_iInf_charts :540, sorry-free axiom-clean — the
full min-over-charts equality given a Resolution). **M12 → DISCHARGED** (consumed transitively
inside O1's clean cone). **O9 → FULLY LANDED** (both pinned proofs; the "two remain" was stale).
**O5/P2 → LANDED** (2026-06-25, pre-register; miss recorded — five clean-three theorems incl. the
paperLambda/Def-3-ℓ fidelity closure; Monotone-d resolved in-file via shiftedSorted; the composite
cCodim_eq_two_lambdaCore appended this wave as the P2-residual micro-entry, now LANDED).
**P1 → LANDED** (pre-register; miss recorded — conditional only on the general monument obligations,
inheriting the #44 sorry, visible in its statement: LANDED-as-stated is honest, and nobody reads it
as P3-progress). **M1/M2/M8/M3 → LANDED** (this wave).

NUANCINGS: **P3/O3** — the L1/L2/gen-front gauge-slice normal forms ARE BUILT; residual = the one
general #44 sorry (Skeleton:1087) + the r>0 transport (iv). **P12** — residual SHRUNK and pinned:
the RLCT-internal card=sum equality exists and is consumed; the absent piece is the CROSS-NAMESPACE
bridge specifically. **O4** — residual PINNED to the leaf-level transport only (:286); the value
side is already sort-invariant; the loss-side rlctGlobal permutation transport is the whole
remaining content.

THE NET LINE (replacing all prior summaries): **the engine's genuinely-open surface = O2 — the
eight monument leaves, including THE WALL — plus the named runway. Nothing else. Every wave-tail
unit this register recommended was already landed when recommended.**

THE META-FACT, one honest sentence: the first pass's value was the NAMING (the M-series, the inverse
list, the re-pricings — several of which the sweep then found already satisfied because the names
made them findable); its status column was systematically stale; the office's correct form was never
solo authorship — it is the author + ground-truther pair, and it took one full cycle to learn that.

EVENT: sweep pass 1 (seat-api, force-elaborated): 8 status corrections, 3 nuancings, 0 new owed
items. The status column is henceforth calibrated by sweep-pairing.

---

## §4 EVENT-UPDATE — 2026-07-21 evening (elder-authored; the repair-rounds day + the parallelisability audit)

STATUS CHANGES: **NEW M17** — IgnoresCoords/Deg1SupportedOn + the closed equivalence bridges
(update-invariance canonical; agreement/zeroing as derived lemmas; the M14-interaction docstring flag
carried) — LANDED (repair rounds). **NEW P13** — canonCenter (the DLN-side canonical center/pivot
assignment from (S, J, esubst, d); the L7 road) — OPEN, M, strike-able, IN-FLIGHT follow-round;
kill-condition DISCHARGED (thread-40 STABLE: rollover slot-stability, both remnant orientations;
two discharge conditions banked — merge pivots return the BIRTH slot, cross-layer legitimate;
the runMinWidth row bound). **M6 → LANDED. M13 → LANDED. M10 → BANKED-UNMERGED** (91f8e016e in
branch history; merge at the next hygiene window). **M4+M9 → the consolidated post-bake unit.**
**P2-composite → LANDED.** §0 guardrail appended: the PER-FIELD SEVERANCE PRINCIPLE (every free
field on a quantified structure is its own severance axis; the audit is per-field, never
per-statement) + the 4-AXIS WITNESS BANK as the standing regression set (content = Σw²/free-center;
size = d=![1,2,1]; path = all-charts-one-path; coordinate = the same-coordinate atlas). §3 event:
the (A′)-reversal arc (shape → assumed-delivery → stated-invariant, with the falsification witness);
sweep-1 corrections applied; thread-40 STABLE.

## §5 PARALLELISABILITY (operator charge 2026-07-21; elder-classified, register-side)

- **O2 / the 8 leaves** — MONUMENT-GATED (it IS the pipeline). Sub-item: **P13 def-drafting =
  PARALLEL-NOW** (a new data-only file + traversal verification); its reachesLeaf WIRING =
  monument-gated.
- **O4 loss-side transport** — PARALLEL-POST-BAKE (math monument-independent, all substrate banked,
  M; the FILE is bake-touched — seat-ready the moment the bake lands).
- **P6 combinatorial θ** — **READY-OPTION, OPERATOR GATE (§1-E)**: M-priced post-foldState,
  file-disjoint ⟹ parallel-now IF OPENED; the analytic pole-order half stays monument-class.
  Elder recommendation: the best breadth-per-seat on the board if E re-opens — the operator's call.
- **P8/O7a φ-form Def-1** — PARALLEL-NOW (fully file-disjoint, S/M standard material; the
  lowest-risk independent seat available).
- **P3's #44 general normal form** — PARALLEL-NOW-CAPABLE, RUNWAY-RECOMMENDED (L-priced, serves the
  r>0 lane only; wants a pnp certificate first — the wall's own lesson; do not open casually).
- **P3 remainder** — MONUMENT-GATED → runway. **P12 bridge** — PARALLEL-NOW-CAPABLE as COLD PREP,
  RUNWAY-RECOMMENDED (thread-40 removed its last near-term consumer).
- **M4+M9 unit** — PARALLEL-POST-BAKE (one quiet window; touches the wall's toolkit imports).
- **M11** — PARALLEL-NOW-CAPABLE (M, low priority). **M7/M10-merge/P9/P10** — RUNWAY-ONLY.
- **M14/M15/M16** — MONUMENT-GATED (the staged locks themselves).

THE SUMMARY LINE (elder): the genuinely seat-ready parallel set TODAY is small and honest — P13's
def-drafting, P8, and (post-bake) O4 + the M4/M9 unit; P6 is the one big READY OPTION and it is the
operator's to open; everything else parallelisable is runway that should not jump the queue. "The
board's scarcity is not seats — it is the wall, and the wall is correctly not waiting on any of this."
