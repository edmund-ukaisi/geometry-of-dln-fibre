# ∀M-L2 interior-det headline — scoping (verdict: DRIVE, no wall)

Decorrelated pen-and-paper (aa3bb63f) + its decorrelated Codex, converged with two prior
triple-confirmed certificates (thread-36 `certificate-genM-det.md` / `certificate-genM-Bdet.md`).

## Target
Generalize `interiorDet_headline_222` to opaque-width M at L=2:
`|det (fderiv ℝ (phiFlatLiveR1At M t ha p hp1 hp2 p₀ rfin) u)| = |u p₀|^(minAdm M − 1) · ∏_{s:Fin L} engine_s`
with `engine_s = |det K_s|^{r_s+c_s} · ∏_i |q_{s,i}|^{2(t_s−1−i)}` (paper per-boundary form).
Built by constructing a `BDataAt M t ha p hp1 hp2 p₀ rfin u` term + `interiorDet_headline_of_BDataAt`.

## Foundation already in place (genm-detfderiv, merge-pending @ c9abbd6b)
- `radial_abs_det_minAdm_at` (RouteMCardBridge), `radialComp_abs_det_at` (RouteMRadialComp): pivot-generic.
- `phiFlatLiveR1At` (RouteMFlatLive): radial-slot-parametric chart, ∀M.
- `BDataAt` + `interiorDet_headline_of_BDataAt` (RouteMBInterface): pivot-generic frozen interface, ∀M.
- slotEquiv deconfliction: name the interior-det cone's slot bijection distinctly (canonical's
  RouteMSmearedDecodeL2 owns `slotEquiv`); the ∀M build must NOT re-define `slotEquiv` — use a
  scoped name (e.g. `bdataSlotEquiv`/`bdataSlotEquivM`).

## Obstruction catalogue (4 obligations of the BDataAt instance)
1. **hdet** (`|det DB| = ∏ engine`): VIABLE via `foldDerivList_abs_det_perBoundary` (RouteMBFactorsDet)
   + `schur/ldu/chainChartFactor_abs_det` (RouteMFactorMaps). NEEDS a concrete
   `BFactors M : List (ChartFactor (routeMAmbient M))` assembled (only a docstring stub today; the
   (2,2,2) bypassed it with the explicit `litMatLT` route). Bounded new construction.
2. **hmap** (`φ = composeFold BFactors ∘ pivotBlowupOn active p₀`): THE BOTTLENECK. Per-layer
   `Params`-level funext via `chainA_apply_castAdd/natAdd` (kept row `C_{s+1}−N_s·W_s` / lift row
   `W_s`) + per-boundary role-reindex CLEs (`paramsBlockSplitCLE`, only the radial split is
   exemplified ∀M today). VIABLE-BUT-HEAVY: dependent-Fin row-cast over opaque Text/Wext.
   Engineering, not new math; dominant piece; a green-but-wrong reindex could hide here.
   DE-RISK: validate the parametric bridge on (3,3,3,3) FIRST (genuine multi-boundary coupling the
   L=2 anchors lack), then lift ∀M-L2 via `List.ofFn` over `Fin L`.
3. **slot-zone** (choose pivot+leaf coords from reader-complement, distinct by membership): VIABLE.
   General role-slot API EXISTS: `schurSlotEquiv`/`liftSlotEquiv`/`readSchur`/`readLift` +
   `readSchur_index_injective`/`readSchur_ne_readLift_index` (RouteMChartSlots). Build
   `readerSet M = (chartIdxEquiv.symm) '' (schur+lift tag images)` as a Finset; the FIRST concrete
   brick = the cardinality invariant `readerSet.card + minAdm M ≤ flatDim M`, provable ∀M-L2 from
   `budget_identity` (∑ chainEdimZ + Text·Wext = minAdm, RouteMBudget) + `chartDim_eq_flatDim`
   (chart-dim = flatDim, RouteMChartIdx) — both banked. Then `Finset.exists_subset_card_eq`
   abstracts the (2,2,2) named-triple to a `minAdm`-subset of the complement. NB: distinctness is by
   MEMBERSHIP (the count is necessary-not-sufficient).
4. **extraCount = a·M₂+b·M₀−ab**: NOT load-bearing for the headline — it's LOWER-leg only (the
   rlctAtOn Morse-square peel, D1ChartProducerL2Build). Off the headline critical path.

## Recommended brick order
1. general `readerSet M` + `readerSet_card_add_minAdm_le_flatDim` (the cardinality invariant). LOW risk.
2. general pivot+leaf triple/tuple from the complement (membership ⟹ ∉ readerSet, distinct). LOW.
3. `BFactors M` assembly + `hdet` via the engine. MEDIUM.
4. `hmap` — validate (3,3,3,3) first, then ∀M-L2 funext. HEAVY (the bottleneck).
5. assemble `BDataAt M` + the ∀M-L2 headline; #print axioms clean-three.

## Level caveat
This is the interior-det headline (chart-Jacobian level) ONLY. Does NOT transfer to `rlct = ½·codim`
(needs the cited Aoyagi equality) nor close the lower-leg `rlctAtOn` divergence (where extraCount lives).

## NAMED GAP (2026-06-29, during (b-rest) assembly): the (2,2,2) decoder is E-block-1×1-special

Driving (b-rest) surfaced a genuine scope gap. The (2,2,2) headline uses `genBlkFlatLiveR1`, whose
`Rmat p = rmatPad (pivotEIndicator)` with `pivotEIndicator = single 1 at (0,0)` — so the ENTIRE
interior E-block at the pivot boundary is the fixed-1 (zeros elsewhere). At (2,2,2) the interior
E-block is `(Text1−Text2)×(Wext1−Text2) = 1×1`, so single-pivot = the full E-block, and
`active = {pivot} ∪ {leaf}` with `card = 1 + Text(L)·Wext(L) = 1 + 2 = 3 = minAdm`.

For M with interior E-block > 1×1 at L=2 (e.g. (3,3,4): E-block `2×2 = 4`, leaf `1×4 = 4`,
minAdm `8`), `genBlkFlatLiveR1` ZEROES the 3 non-pivot E-block angular coords, so its
`active = {pivot} ∪ {leaf}` has `card = 1 + 4 = 5 ≠ 8 = minAdm`. The HONEST (3,3,4) chart
(`RouteMLayerCoverGEL2.leafH334`) confirms the true radial exponent is `minAdm−1 = 7`, with the 7
active coords spread over the interior E-block angular (`τ`, `Δ`) + leaf — NOT a {pivot}∪{leaf}.

So the ∀M-L2 headline needs the CERT's decoder (`certificate-genM-Bdet.md` §2): the interior E-block
angular entries READ from x (active, `x_p · angular`) EXCEPT one fixed-1 pivot, + the live leaf. This
is a NEW decoder (the cert's `B_det M`), NOT a lift of (2,2,2)'s `genBlkFlatLiveR1`. The banked bricks
(1 cardinality, 2a per-boundary Cgen=schurFrameProd, 3-atom E-block embedding) are decoder-agnostic
and remain valid/reusable; the gap is the achiever-chart decoder for the headline.

CONSEQUENCE: (c)/(d) cannot proceed on `genBlkFlatLiveR1`. Options: (i) build the cert's `B_det M`
decoder (the E-block-angular-active + leaf, the genuine ∀M achiever) — substantial new construction,
touches the achiever chart; (ii) restrict the ∀M-L2 headline to the 1×1-interior-E-block sub-family
(where `genBlkFlatLiveR1` suffices) — narrower, but `genBlkFlatLiveR1`-faithful. Coordinator call:
this touches the achiever-chart construction (a coordination point per the standing instruction).

## REFINEMENT (same session): option (i) is LESS new construction than feared

`genBlkFlatLive` (the live-leaf decoder WITHOUT the R1 single-pivot override) ALREADY reads the
interior E-block angular coords via `readE` (`Rmat (k+1) = rmatPad(readE)`, inherited from
`genBlkFlatStruct`) AND has the live leaf (`Rfin L = rfin`). In `Cgen`, the radial `u` scales the
WHOLE residual: `u • Rmat` (E-block angular) + `u • Rfin` (leaf). So `genBlkFlatLive` IS the cert's
`B_det M` decoder (the full residual active, u-scaled) — the R1 `pivotEIndicator` override was a
(2,2,2)-only simplification (valid there because the 1×1 E-block = single pivot).

So option (i) ≈ use `genBlkFlatLive` (banked) with chart `phiGen (x p₀) … (genBlkFlatLive …)` and
active = the full residual (E-block-angular slots via `activeSlotE` + leaf slots). The non-pivot
per-boundary brick `Cgen_live_interior_eq_schurFrameProd` (brick 2a, E=readE) is ALREADY the right
identity (not the pivot variant). Remaining: the pivot placement (one residual slot as `p₀`, the
fixed-1), the leaf-slot reading, the full active.card=minAdm (E-block via activeSlotE_inj + leaf),
and the chart rate (genBlkFlatLive's rate is likely banked — RouteMFlatLive has C0_eq_one_live etc.).
Substantially de-risked; awaiting coordinator go on (i) vs (ii).

## PINNED DESIGN (Codex-confirmed, active-genblklive-answer.md): the genBlkFlatLive + leaf-pivot decoder

The ∀M-L2 headline decoder = `genBlkFlatLive M (tach M) ha (rfinFixedPivot x) x` with the LEAF-pivot:
- `rfinFixedPivot x : Matrix (Fin (Text L)) (Fin (Wext L))` with `(0,0) = 1` (the fixed bare-`u`
  pivot, so `Cgen … L = u • rfin` gives `C_L(0,0) = u·1 = u` — the radial axis), and the OTHER leaf
  entries read from chosen complement slots (`u·angular`).
- `Rmat₁ = rmatPad(readE)` UNCHANGED (all interior E-block entries READ from x = `u·angular`). NO
  E-block override (unlike genBlkFlatLiveR1, which zeroed the E-block — the 1×1-special bug).
- `active = E₁ ∪ Rfin_L` (the full interior E-block slots ∪ the leaf slots), `card = minAdm`,
  `p₀ = Rfin_L(0,0)` ∈ active. The non-pivot residual entries are `u·angular`; `pivotBlowupOn active
  p₀` reproduces this (p₀→u, rest→u·angular).
- (3,3,4): tach=(3,1,0), Text=[3,3,1]; E₁ = 2×2 = 4, Rfin₂ = 1×4 = 4, active.card = 8 = minAdm,
  p₀ = Rfin₂(0,0). The `|u1|²` in leafH334 is a SEPARATE spectator (the b=aβ substitution), NOT the
  radial blow-up — so the radial Jacobian is `|u0|⁷ = |u_p₀|^{minAdm−1}`, matching.

WRONG alternatives (Codex): p₀ separate from E∪Rfin → card = minAdm+1 (exp wrong); raw-read at pivot
slot → u·x_p₀ = u² (no bare-u). So the decoder MUST supply the fixed-pivot rfin (not raw genBlkFlatLive).

REMAINING: rfinFixedPivot + the leaf-slot complement choice; structured active M (E-block via
activeSlotE ∪ leaf slots) + active.card=minAdm; the chart phiFlatLiveAt (= phiGen (x p₀) … genBlkFlatLive)
+ its rate (RouteMFlatLive's live machinery); the hmap funext (brick 2a non-pivot Cgen + leaf) + BDataAt.

## STATE (2026-06-30): ∀M-L2 headline MODULO hdet — 3 of 4 legs closed

The capstone `interiorDet_leaf_headline_Bchart` (RouteMLeafBData) is the ∀M-L2 headline
`|det Dφ| = |u p₀|^{minAdm−1}·∏ engine` for the REAL chart phiFlatLiveAt, with B (BchartLeaf), hmap
(hmap_leaf), hasDB (hasDB_leaf) ALL CLOSED concretely + axiom-clean [propext,Classical.choice,
Quot.sound]. It CARRIES one hypothesis: hdet.

NAMED RESIDUAL (hdet): `|det (fderiv BchartLeaf …)| = ∏_s engine_s`, BchartLeaf = paramsEquivFlat ∘
chartParamsGen-at-1 (the u-free boundary chart), engine = the per-boundary Schur·LDU value
`(|det K|^{r+c}·∏_i|q_i|^{2(t−1−i)}, 1)`. The route EXISTS (BOUNDED, not a wall): factor BchartLeaf's
fderiv as (paramsEquivFlat CLE, |det|=1) ∘ (entry-Jacobian = composeFold [schurChartFactor,
chainChartFactor, lduChartFactor]), then composeFold_abs_det + schurFrame_abs_det (validated vs 334) +
the lduCore/chain dets = ∏ engine. The (2,2,2) TEMPLATE is bData222.hdet (DB = Q222CLM ∘ TbCLM,
|det| = 1·|aRead|²). The opaque-width work: the entry-Jacobian factorization + matching its det to the
engine product (the N-block couples layer-0 frame + chaining, so a genuine block-triangular split —
NO free-product shortcut, Codex-confirmed; engine:=|det DB| self-referential would be vacuous).

CONE (modulo-hdet, deconflicted vs canonical 5184db86, 0 clashes, purely additive): 10 NEW modules —
RouteMReaderCard, RouteMHmapGen, RouteMActiveSlots, RouteMLeafSlot, RouteMLeafChart,
RouteMLeafHeadline, RouteMLeafBData, RouteMChainAssembleDiff, RouteMChartDiff, RouteMFrameDiff.

## hdet ROUTE PINNED (Codex-verified, hdet-route-answer.md): route (A), the explicit entry-Jacobian

The coordinator's "BchartLeaf's fderiv = composeFold[schur,chain,ldu]" is NOT literally true from the
defs (BchartLeaf = paramsEquivFlat ∘ chartParamsGen-at-1; the inner fderiv is the per-layer Agen-fderiv
assembly, NOT a composeFold). Route (B) would need a map-level bridge `BparamsLeaf = pack_M ∘ composeFold
BFactors` proven first. The SOUND route is (A), the opaque-width generalization of the (2,2,2) DB template:
- `BchartLeaf = Q_M ∘ TbGen`, `Q_M = paramsEquivFlat ∘ pack_M` (linear CLE, |det| = 1), `TbGen` the
  EXPLICIT entry-Jacobian chart (the general analogue of (2,2,2)'s TbCLM/litMatLT).
- `fderiv BchartLeaf y₀ = Q_M ∘L fderiv TbGen y₀`, so `|det fderiv BchartLeaf| = |det fderiv TbGen|`.
- `|det fderiv TbGen| = ∏ engine` = the Schur-frame det × LDU det (chain det 1), via the banked
  schurFrame_abs_det (validated vs 334) + lduChartFactor_abs_det + the BLOCK-LOWER-TRIANGULAR grading.
- The N-block coupling (N feeds layer-0 Schur frame AND layer-1 chaining C−N·W) is NOT a free product —
  needs a genuine block-triangular/ordered-factor det argument (the N off-diagonal/unit-triangular/
  det-irrelevant). This is the heavy piece, where a wrong reindex hides.
ENGINE = honest Schur·LDU value (boundary 0: |det K|^{r+c}·∏|q_i|^{2(t−1−i)}; boundary 1 leaf = 1),
NOT engine:=|det DB| (self-ref vacuous). (2,2,2) template: RouteMBData222 DB_abs_det/TbCLM_abs_det/litMatLT_det.

## STATE (2026-06-30, genm-detfderiv hdet thread): validate-(3,3,4) PASS + FIDELITY CORRECTION + WALL

VALIDATE-(3,3,4) result: **PASS, with a fidelity correction.** Numeric Jacobian of the boundary
factor `BparamsLeaf` (the u-free chart, the inner factor of `BchartLeaf = paramsEquivFlat ∘
BparamsLeaf`) at (3,3,4): `det (fderiv BparamsLeaf) = (det K)^{r+c} = (det K)^4` EXACTLY, where K is
the interior Schur core `readK ⟨0⟩` (1×1 at (3,3,4)), `r = Text1−Text2 = 2`, `c = Wext1−Text2 = 2`.
Confirmed at a second case (t=2 Schur core, M=(4,4,5)): `det = (det K)^4` again. So the honest engine
for the EXISTING `BchartLeaf` is **free-K Schur `|det K|^{r+c}`, NOT Schur·LDU**.

FIDELITY CORRECTION (decorrelated Codex `hdet-realize-answer.txt` corroborates the numeric): the
`∏ᵢ|qᵢ|^{2(t−1−i)}` LDU multiplier of the briefed engine is FALSE for `BchartLeaf` — `BparamsLeaf`
reads the K-core via `readK` DIRECTLY (free coords), it does NOT pre-apply the `kLDU` lens
(`RouteMKLens`). The LDU factor appears only for a *lensed* decoder `BparamsLeafLDU`. The precise
false identity is `readK y = kLens (readK y)`. At (3,3,4) the two coincide vacuously (t=1 → LDU
exponents 0 → product 1), which is why `|det K|^4` is simultaneously free-K and (vacuously) Schur·LDU
there; for t≥2 they genuinely differ and the honest value is the free-K one. The honest engine is
`engineFreeK 0 = |det K|^{r+c}`, `engineFreeK 1 = 1`.

LANDED (genm-detfderiv, sorry-free, axiom-clean [propext,Classical.choice,Quot.sound], clean-three):
- `RouteMLeafEngine`: `engineFreeK` + `engineFreeK_prod` (the honest free-K engine).
- `RouteMLeafReduce`: `Bchart_abs_det_eq_Dtot` — `|det (fderiv BchartLeaf y₀)| = |det (Dtot y₀)|`,
  `Dtot = paramsEquivFlatCLE ∘L (fderiv BparamsLeaf)` (the `paramsEquivFlat` measure-preserving reindex
  STRIPPED; via `HasFDerivAt.unique`, NOT `.fderiv`, to dodge the opaque-width `ContinuousAdd` synth).
- `RouteMLeafFreeKHeadline`: `interiorDet_leaf_headline_freeK` — the ∀M-L2 headline
  `|det Dφ| = |u p₀|^{minAdm−1}·∏ engineFreeK`, modulo the SINGLE sharp fact
  `hDtot : |det (Dtot …)| = |det K|^{r+c}`. Strictly sharper than the capstone's opaque `|det DB|`.

THE WALL (named, NOT graded): `hDtot : |det (Dtot ha (pbo u))| = |det K|^{r+c}`. This is the staircase
determinant of the boundary-factor Jacobian: `Dtot` regrouped into V0 = {Schur frame inputs K,X,N1,E}
and V1 = {lift W1, leaf} is a 2-block staircase (`stairMap V 2`) with `f 0 = schurFrameDeriv`
(det `|det K|^{r+c}`, banked), `f 1 = chainUnit` (det 1, banked), the shared N1-coupling strictly
head→tail (det-invisible). It discharges via `RouteMStairTwoSided.stairMap_abs_det_twoConj` once the
two layer-collecting equivs `eIn/eOut : (Fin N → ℝ) ≃ StairProd V 2` are built + the entry match
`eOut ∘ Dtot ∘ eIn.symm = stairMap` is proven over the opaque dependent `Fin (Text/Wext)` widths.

This is the SAME wall already isolated and named by `RouteMInteriorDetReal.interiorDet_phiFlatLiveR1_of_stairConj`
(the `hconj` hypothesis) — the "cast-heavy multi-tide staircase decomposition over the opaque
chart-coordinate widths" the `staircase-det-bricks-statement-card.md` flags, the `frameB` ∀M
generalization (done by hand at (3,3,3,3), never for ∀M). `RouteMGradingObstruction` proves the simpler
single-grading square `Matrix.BlockTriangular` route is mathematically blocked (FlatIdx layer counts ≠
ChartIdx boundary counts), so it MUST be the rectangular two-sided staircase. Beyond a 3-4 attempt
budget for one goal — surfaced, not ground. The headline is now reduced to exactly this ONE det.

CONE (additive, 0 name clashes vs siblings): RouteMLeafEngine, RouteMLeafReduce, RouteMLeafFreeKHeadline
(NOT yet wired into DLNFibre.lean — single-writer; controller integrates).

## STATE (2026-06-30, hdet leg): headline MODULO hDtot — engine corrected to free-K

FIDELITY CORRECTION (sound): the honest engine is FREE-K `|det K|^{r+c}` (engineFreeK), NOT
"Schur·LDU `·∏|q_i|`" — the `∏|q_i|` is ALREADY inside det K (K = the full LDU core; verified vs
schurFrame_abs_det's (3,3,3,3) validation: the `(z1z4−z2z3)²` block = `|det K₁|²`). My route brief
double-counted; corrected. engineFreeK = explicit `|det leafKcore|^{r+c}` (NOT self-ref).

CAPSTONE `interiorDet_leaf_headline_freeK` (RouteMLeafFreeKHeadline): `|det Dφ| =
|u p₀|^{minAdm−1}·∏ engineFreeK`, B/hmap/hasDB CLOSED, hdet REDUCED to hDtot (via
Bchart_abs_det_eq_Dtot stripping paramsEquivFlat). Axiom-clean. CARRIES hDtot.

NAMED WALL hDtot: `|det (Dtot …)| = |det K|^{r+c}` — the staircase det of the boundary-factor
Jacobian at opaque widths. Discharges via the banked RouteMStairTwoSided.stairMap_abs_det_twoConj
ONCE eIn/eOut : (Fin N→ℝ) ≃ StairProd V 2 are built + `eOut ∘ Dtot ∘ eIn.symm = stairMap` proven over
opaque Fin(Text/Wext). This IS the prior-isolated hconj/stairConj
(RouteMInteriorDetReal.interiorDet_…_of_stairConj — done by hand at (3,3,3,3), never ∀M).
RouteMGradingObstruction proves the single-grading BlockTriangular route is BLOCKED (partitions
differ), forcing the rectangular two-sided staircase. A cast-heavy MULTI-TIDE piece, not a 3-4-attempt
fill — the honest ceiling for the genBlkFlatLive headline without the staircase-conjugacy tide.

PROGRESS LEDGER: B/hmap/hasDB CLOSED (the (2,2,2)-bottleneck ∀M); hdet→hDtot (opaque→sharp staircase
det); engine = honest free-K. Cone (modulo-hDtot): the 10 prior + RouteMLeafEngine/Reduce/FreeKHeadline,
deconflicted vs canonical 5184db86 (0 clashes), green 8335.
