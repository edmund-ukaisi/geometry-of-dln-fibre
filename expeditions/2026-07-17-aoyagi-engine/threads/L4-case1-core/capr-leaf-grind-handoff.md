# CAPR leaf-grind handoff — the §4 b-ledger induction, decomposed and blessed

seat-CAPR → fresh grind seat. Lane `expedition/aoyagi-engine-CAPR @ 585f75fb9` (this doc adds one commit
on top). The capstone's ARCHITECTURE is done, elder-blessed, banked; the CONTENT LEMMA is proven by
decomposition; what remains is the patient leaf-proof grind, scoped per-leaf below. Owner transfer: on
your spawn, `SourceClearedResid.lean` + `MergeBoostSplit.lean` are yours (single-writer); the standing
constraints (§4 below) transfer with them.

Primary contract: `capstone-invariant-certificate.md` (§4 = the induction). Object ruling: §7-§7.8 +
§12.2 (`design-round-2-ruling.md`, db7b8e123). Elder blessing (this render): P1 boost-conjunct
canonPivotOf-anchored (StepChild/(b)-form preferred, your call by transport-cleanliness); P2 dissolved
(`blockCoords 0 = layerCoords 0`, proven); P3 vacuous-at-root confirmed.

## 1. Lane state (file-by-file: proven vs sorried @ 585f75fb9 + this doc)

`DLN/Aoyagi/SourceClearedResid.lean` (imports MonumentAtlas):
- PROVEN (axiom-clean `[propext, Classical.choice, Quot.sound]`): `ignoresCoords_of_subset`,
  `blockCoords_zero_eq_layerCoords` (= ROOT part a), `belowPivotCol`, `couplingCoords`, `couplingClear`,
  `accumulatedPivots`, `ledgerTarget`, `sourceClearedResid` ((A)-primary = `foldResid ∘ couplingClear`),
  `sourceClearedResid_root` (= `coreGen`), `sourceClearedResid_eq_restrict` (rfl fidelity anchor),
  `bMon` + `bMon_zero`, `SourceClearedInv` (the §4 b-ledger predicate).
- SORRIED (LIVE-frontier leaves): `sourceClearedInv_holds` (the induction), the Q₁-lift bridge
  `rlctGlobal_sumSqFam_foldResid_eq_sourceCleared` (state-only — see §5), the append-analog
  `sourceClearedResid_stepMap_eq_pivot_mul` (L4D/GM-facing — see §5), the §12.2 obligation (b)
  `realBranch_appendResidDescent_fresh_sourceCleared`, the containment `case11_center_subset_ledgerTarget`.

`DLN/Aoyagi/MergeBoostSplit.lean` (imports SourceClearedResid):
- PROVEN: `MergeBoostSplit` (predicate), `MergeBoostSplit.deg1SupportedOn` (the clean-three assembly),
  **`foldResid_case11_mergeBoostSplit_sourceCleared`** (THE CAPSTONE — proven by decomposition
  `:= mergeBoostSplit_of_sourceClearedInv … (sourceClearedInv_holds …)`), `realBranch_boostReady_case11'`
  (the wall, via the content lemma + the assembly).
- SORRIED: `mergeBoostSplit_of_sourceClearedInv` (the §4 iv read-off), `foldResid_case11_mergeBoostSplit_canon`
  (OLD raw-object FOSSIL — off every cone, REFUTED banner; prune at close, do NOT prove).

So the capstone-cone frontier = `sourceClearedInv_holds` + `mergeBoostSplit_of_sourceClearedInv`; the rest
(bridge, append-analog, obligation-b, containment) are consumer/state-only leaves.

## 2. The §4 invariant (what the induction proves)

`SourceClearedInv d p := ∀ j, ∃ (μ : Fin (flatDim d) → (Fin (flatDim d) →₀ ℕ)) (q : … → … → ℝ),`
`  (∀ i, ContinuousOn (q i) (foldRegion …)) ∧ (∀ i, IgnoresCoords (q i) (ledgerTarget d p) …) ∧`
`  (∀ i, (μ i).support ⊆ accumulatedPivots d p) ∧ [BOOST LEDGER] ∧`
`  (∀ u ∈ foldRegion …, sourceClearedResid d p j u = ∑ i ∈ supportAt …, bMon (μ i) u * q i u * u i)`.

- Target `ledgerTarget p = accumulatedPivots p ∪ supportAt p` — the edge-independent `IgnoresCoords`
  carrier; contains every case11 `ed.center` (the hard containment §3-containment), so it specializes to
  IgnoresCoords-`ed.center` at the read-off via `ignoresCoords_of_subset`. (L4D+pnp corrected Codex here:
  the birth-corner `e₂` is a pivot, NOT in `couplingCoords` — must be `accumulatedPivots`.)
- BOOST LEDGER (the one design point the elder blessed): rendered over real case11 extensions using
  `ed.pivot` (= `canonPivotOf`). run-block coord → `μ i ed.pivot = 0`; extension coord → `= 1`. The elder
  PREFERS the `StepChild`/`canonPivotOf`-direct form (drops the free-`TreeEdge` quantifier, transports
  edge-independently) — adopt whichever is transport-cleanest, pivot MUST resolve to `canonPivotOf`.
- Step law (pnp Q2, the transport's constructive content): δ=1 SUBTRACTS the pivot exponent (the
  `blockBlowupCoordQuot` strict transform divides it out); δ=0 ADDS it (the blow-up multiplies center
  coords). This is the COMPLEMENT of `foldB`'s recursion (`foldB_child = u_pivot^δ · foldB_parent∘stepMapRaw`
  — the residual loses what `foldB` gains). μ(root)=0, `bMon 0 = 1`.

## 3. Per-leaf proof routes

**ROOT** — target `sourceClearedInv_holds` at `.root` (its induction base; factor a `sourceClearedInv_root`
if cleaner). 3 parts:
- (a) DONE — `blockCoords_zero_eq_layerCoords` (proven). `supportAt(root) = blockCoords d 0 = layerCoords d 0`.
- (b) — the continuous `coreGen` support-decomposition: `coreGen d (canonFlatten d) j = ∑_{i∈layerCoords 0}
  q i · u i` with `q` CONTINUOUS + IgnoresCoords. NOT available from `coreGen_layerHomogeneous'`
  (`AffineOn`/`HomogeneousDeg1On` records only IgnoresCoords, not continuity). RE-DERIVE tracking
  continuity, reusing that proof's `bcoeff = ∑ p, if enc p = x then (M·R) else 0` structure (M,R = `submult`
  of `canonFlatten`). Needs a NEW `continuous_submult` (`Nat.leRec` interval induction; template
  `continuous_multPrefix` (LearningCoefficient:107, clean `Fin.induction`) — mind the interval lower-bound +
  the dependent `hij`, fiddlier than the prefix case) ← per-layer `canonFlatten` continuity. `submult_self`
  / `submult_succ` (Core/Submult.lean:57/65) are the recursion lemmas. ~2-3 nested lemmas. `continuous_submult`
  is a general Core/Submult fact — consider siting it in Core/Submult.lean (controller-only; request via
  controller) or a local candidate-lift.
- (c) — the BOOST LEDGER conjunct is VACUOUS at root: `conRoot.numDiv = 0` ⟹ no case11 `StepChild` of
  `conRoot` ⟹ the case11-extension hypothesis is unsatisfiable. Route: reduce `(conOracle conRoot).stepChildren`
  and show none has `.ecase = case11`. WARNING (banked lesson, lean/CLAUDE.md): the `match hmin : occ.min?`
  in `stepChildren` resists reduction under a projection — use the per-branch REDUCTION-EQUATION idiom
  (`OracleInv_conOracle_stepChildren` pattern), not `simp [theDef]`.

**δ=1 / δ=0 transports** — the induction step of `sourceClearedInv_holds`. `foldResid_extend_delta1`/`_delta0`
(Case1Wire:90/101) give the child = parent∘(strict-transform / pullback). Construct the child `μ` from the
parent's per the step law (§2); the child `q` from the parent via `blockBlowupMap_shear_center_eq`
(BlockDivision, the FIX-A center division) + the `couplingClear` commutation (the cleared object rides
`foldResid`'s recursion — verify `couplingClear (child) ∘ strict-transform = strict-transform ∘ couplingClear (parent)`;
if a C↔F fact is needed BEYOND the append-analog's statement, STOP — that's the bridge surfacing, elder+L4D
re-engage). Per-layer degree ≤1 conjunct of the child descends from the raw `foldResid_layerHomogeneous'`
via `couplingClear`'s degree-non-increase (elder pointer).

**read-off** — `mergeBoostSplit_of_sourceClearedInv`: instantiate `MergeBoostSplit` from `SourceClearedInv d p`
at a case11 `ed`. `e₂ = ed.pivot`; `part = supportAt ∩ ed.center`, `extra = supportAt ∖ ed.center`. From the
INV decomposition split the sum over `part ⊔ extra`. `α i := bMon(μ i)·q i` (part). For `extra`: the boost
conjunct gives `μ i ed.pivot = 1`, so `bMon(μ i) = u_{e₂} · bMon(μ i - single e₂ 1)`; `β i := bMon(μ i.erase e₂)·q i`.
IgnoresCoords-`ed.center`: `ed.center ⊆ ledgerTarget` (containment) + `ignoresCoords_of_subset` on q; the
`bMon`-factor's `ed.center`-freedom is the restriction laws (part → e₂-exp 0; extra → the e₂ factored out).
THE RAW-c_i TRAP: `c_i = u_{e₂}·β_i` does NOT itself ignore `ed.center` (e₂∈ed.center) — only `β_i` + the clean `q` do.

**containment** — `case11_center_subset_ledgerTarget`: `ed.center = {e₂} ∪ (layer-S partial block) ⊆
accumulatedPivots p ∪ supportAt p`. `e₂ = canonPivotOf` ∈ `accumulatedPivots` (the reused divisor's birth edge
is a recorded ancestor blow-up — via `IsRealBranch`/`DescendView`); the partial block ⊆ `blockCoords S` =
`supportAt(p)` (via `runLen ≤ widthMinUpto`). Combinatorial + oracle leg.

**bridge** — `rlctGlobal_sumSqFam_foldResid_eq_sourceCleared`: STATE-ONLY (certificate §2, the det-1 Q₁-gauge
ψ). NOT the §4 induction — a separate follow-on consuming the landed det-1-CoV machinery + pnp's ψ_gen;
GM's #74 consumes it as (iv). Leave sorried unless separately tasked.

**append-analog** — `sourceClearedResid_stepMap_eq_pivot_mul`: STATE-ONLY, consumed by GM's `ClearedFold`
append re-point + L4D. Reduces to the `couplingClear`/step-map commutation + Deg1-over-`ed.center`.

## 4. Standing constraints (inherited with the files)

- STATEMENT-LOCK: all statements are elder-green/frozen. A statement change is a statement-class event →
  STOP + escalate to elder (never render around it). Prove against the frozen statements.
- TRIPWIRES: certificate §8 per-section kill-conditions; the C↔F bridge (the induction runs entirely on C —
  if any leaf needs ⟨C⟩=⟨F⟩ or a C↔F fact beyond the append-analog, STOP: ⟨C⟩ ≠ ⟨F⟩ (restriction changes the
  ideal), the reconciliation is L4D/GM integration territory).
- CROSS-REF HONESTY (elder): docstrings referencing Aoyagi/worked.tex say "RLCT-equivalent via the
  source-clear rendering (coordinate-form differs by our shear-frame)", NEVER coordinate-identity.
- GM-PRIMITIVE STABILITY: `couplingClear`, `sourceClearedResid`, `sourceClearedResid_stepMap_eq_pivot_mul`
  are load-bearing for seat-GM's #74 `ClearedFold` — keep their STATEMENTS locked; proving the append-analog
  is fine (statement unchanged). Route any statement change through the controller.
- GATES at close: full `scripts/lb DLNFibre` green; forced `#print axioms` (bMon/defs clean; leaves' sorryAx
  accounted); census delta named-frontier-by-frontier; cordon (`decide +kernel`, no `native_decide`); push.

## 5. Verification battery (for the transport leaves)

pnp's caveat (carried): the single-exceptional b_i was sampled; a STACKED-exceptional slot was NOT. The
transport-leaf battery MUST include a stacked-exceptional witness — the double-boost **(3,3,2,2)** class
(a case11 reusing a divisor whose b_i already carries an exceptional). Also the wide **(2,3,2,2)** (cap-bite)
and the archetype **(2,2,2,2)**.

## 6. def-owner consult (CAPR, retired to consult status)

Route def-intent questions (the (A)-primary `sourceClearedResid` shape, `ledgerTarget`/`accumulatedPivots`
semantics, the boost-ledger conjunct's intent, `couplingClear`'s frame) through the controller to CAPR,
budget-permitting.
