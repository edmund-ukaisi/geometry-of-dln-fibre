# t03 → t04 handoff — the D package + chart carrier

*Construction seat (t03) stand-down artifact. Spine A→C + D§i + E assembled and merged
(tip `5fff06dc9`); aggregator green; `monomialization_terminates` = `[propext, sorryAx,
Classical.choice, Quot.sound]` via EXACTLY the two named holes; capstone + `minAdm ≤` stay
clean-three. This note is t04's entry surface — the whole D package (reify-Clearable + §3 + §4 +
pull-ordering brick) and the chart-emission carrier are t04's, with full budget and the cert.*

## 1. The two named holes (exact types + consumption site)

Both in `lean/DLNFibre/DLN/RLCT/Engine/EngineObligations.lean`, consumed by
`monomialization_terminates (M) (hL : 0 < L)`'s witness `⟨buildTree M (conOracle M) conRoot, …⟩`:

- **`chartBridge_buildTree (M : Fin (L+1) → ℕ) (_hL : 0 < L) : ChartBridge M (buildTree M (conOracle M) conRoot)`**
  — the 4th slot of the `CanonicalResolution` tuple. Fills ← T3 coverage lane, AFTER the chart carrier (§3).
- **`o5_realization (M) (_hL : 0 < L) : minAdm M ∈ terminalExponents (buildTree M (conOracle M) conRoot) ∧ (∃ l ∈ leaves (buildTree M (conOracle M) conRoot), l.srcBox.Nonempty ∧ minAdm M ∈ (List.finRange l.numDiv).map l.divExp)`**
  — its `.1` is the 2nd half of slot 5's `⟨minAdm_le_terminalExponents M hL, o5_realization.1⟩`; its `.2` is slot 6 (live attainment). Fills ← D§ii/iii.

The other four slots are PROVEN clean-three and need no touching:
`isFullMonomialization_buildTree_conRoot M hL`, `stepRel_all_of_buildTree`,
`base_of_buildTree … (conRoot_steps hL)`, `minAdm_le_terminalExponents M hL`.

## 2. D§ii/iii tail (`o5_realization`) — what it needs beyond cert §§3-4

Cert: `threads/12-realization/cert-o5-realization.md`. Naming pin: `minAdm_mem_terminalExponents`-class;
NEVER `*_complete` / `*_eq_Adm` (⊇ Adm is FALSE — ledger #4). Scope = minimizer-only.

Where the cert's steering output meets the Lean shape:
- `terminalExponents (buildTree…)` = `(leaves …).flatMap (fun l => (finRange l.numDiv).map l.divExp ++ (if 0 < l.resRank then [l.resRank] else []))`. `leaves_resRank_zero` (LANDED) gives `resRank = 0`, so the residual part is `[]` — every terminal exponent is a `l.divExp k` for a t̃=0 analytic divisor. So `minAdm ∈ terminalExponents` ⟺ ∃ a leaf `l`, ∃ analytic `k`, `l.divExp k = minAdm`, i.e. (via `MvalCoh.toNat` + `IsFullMonomialization`) ∃ a t̃=0 leaf divisor with profile `a` s.t. `(Mval M a).toNat = minAdm` and `a ∈ Adm`.
- §3 (envelope-splice) is ALGEBRAIC (`Mval`/`Adm`/`Clearable` arithmetic — same flavor as my `Mval_setTail_runMinWidth`/`_delta`): reduces `minAdm = inf_{Adm} Mval` to `inf_{Clearable-Adm} Mval`. Tractable with the banked `Mval` lemmas.
- §4 (steering + anchor descent) is the CONSTRUCTION-TRACING half: it must exhibit ONE clearable minimizer `a*` realized as a t̃=0 leaf divisor of `buildTree M (conOracle M) conRoot`. This is where the Lean effort concentrates — tracing a specific root→leaf path in the built tree and reading its terminal divisor. The ONE flagged brick (intra-layer pull-ordering) reuses my banked `LiveHeadDom` + `chooserTotalOnChain_of_sameLevel` (chooser minimality).
- `srcBox.Nonempty` (slot 6): `leafOfState`'s srcBox = `paramsEquivFlat ⁻¹' cubeBox (flatDim M) 1` — nonempty (a cube at radius 1; needs `0 ≤ 1`), cheap.

## 3. Chart-emission carrier (t04's FIRST item; prereq for `chartBridge_buildTree`)

Spec pointer: journal tick 163 (4-part per-edge surface). Status as I left it: PLACEHOLDERS —
every decision (`case2Decision`/`case1Decision`/`case11Decision`/`case12Decision`/`rolloverDecision`)
emits `ChartSubst.localSub = id`; `leafOfState.chartMap = id`.

My read on WHERE the per-edge fields live: **`ChartSubst` already IS the per-edge chart surface** —
its `localSub : Params M → Params M` (the coordinate change) + `jacDivCount`/`jacPow` (the
monomial-Jacobian ledger) are exactly the 4-part surface. No sibling bundle needed. The carrier is:
(a) populate `localSub`/`jacPow` in each decision with the REAL blow-up substitution (not `id`);
(b) thread a path-accumulator through `buildTree` (the `WellFounded.fix` body) so `leafOfState.chartMap`
becomes the root→leaf `localSub` fold — matching `leafPaths id`'s accumulator, so
`ChartBridge`'s coherence clause `p.1.chartMap = p.2` holds BY CONSTRUCTION.
**Safety (verified):** the chart-independent spine (`isFullMonomialization_buildTree_conRoot`, `StepRel`,
base, `minAdm ≤`, `leafOfState_rootLedger`/`hleaf`) reads ONLY the divisor/full ledger, NEVER `chartMap`
— so populating charts leaves them, and the two named-hole types, unchanged.

For coverage-t07: build the wiring skeleton reading the LEAF FIELDS (`l.chartMap`) — the carrier makes
`l.chartMap` the real fold, so `chartBridge_of_pieces` stays valid against the fields.

reify-Clearable (elder-gate7, = §3's first brick): `Clearable` predicate (cert §1) + sorried
`P(M) = Clearable-Adm(M)` statement theorem + AxCheck watch line (+sorryAx until R7).

## 4. Local subtleties around the assembly

- **`0 < L` is load-bearing** (base conjunct false at L=0). It is DEFEQ `1 ≤ L` (`Nat.lt` = `succ ≤`),
  so the DLN fit witness's `hL : 1 ≤ L` supplies it directly. Keep `hL` on every downstream decl
  (resolutionOf + 6 projections + region_glue + engine_box_threshold_finite).
- **Dependent-match reduction** (gotchas ledger): `conOracle`'s `match hmin : … .min? with` resists
  `simp`/`rw` inside. Idiom: establish `min? = none/some` as a STANDALONE hyp first (for `conRoot`,
  `min? = none` is `rfl` since `numDiv = 0`; `List.finRange` does NOT whnf inside a match), then the
  horacle `unfold conOracle; rw [dif_neg …]; split <;> simp_all only [reduceCtorEq]`.
- **`MvalCoh` is the ℤ-equality form** `(divExp k : ℤ) = Mval` (not `toNat`); `MvalCoh.toNat` derives
  the `IsFullMonomialization` read-off. Keep deltas over ℤ (clean); cast at the leaf.
- **Fin proof-irrelevance**: `M ⟨layer+1, p1⟩` vs `M ⟨layer+1, p2⟩` are defeq; `ring`/`exact` close
  across them, but `rw` needs the same proof term — pin one `by omega`/`hh` and reuse it.
- No universe/namespace traps in the assembly (all `Engine` namespace, `Type 0`).

*Do not modify t01-r2 after this — t04 takes it over.*
