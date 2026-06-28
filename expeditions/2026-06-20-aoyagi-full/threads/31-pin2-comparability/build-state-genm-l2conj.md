# build-state-genm-l2conj — W-a wire-close resume note (for genm-l2thread)

**Base:** `origin/genm-l2conj` @6dfef93d (off `genm-l2wire2`). All listed lemmas **clean-three**
`[propext, Classical.choice, Quot.sound]`. `DeepestLDUReadback` + `DeepestSchurShift` sorry-free;
`DeepestL2Wiring` + `DeepestGaugeConstruction` green with documented residuals.

Build: from `lean/`, `scripts/lb DLNFibre.DLN.RLCT.Validate.<Module>`. `#print axioms` via a scratch
file after `rm -f .lake/build/lib/lean/.../<Module>.olean` (defeat stale sorryAx).

## What is DONE (the irreplaceable work — do NOT redo)

PRIMARY — the hLDUtie crisis resolved:
- `prod_deepestM_eq_schur_ldu_readback` (DeepestLDUReadback.lean) — the readback restated TRUE with the
  W-a conjugated dict, proven from banked lemmas. `H : Fin 3` (hL2-specialized), takes the conjugated
  tuple `C` abstractly + two readback hyps `hC0`/`hC1`. **Consumes:** `prod_deepestM_eq_two_of_L2`
  (banked) + `score_eq_unframedSchur_prodDecode` + `unframedSchur_prodDecode_eq_ldu` +
  `prodDecode_eq_two_of_L2` (all in DeepestLDUReadback, clean-three).

SECONDARY foundation (DeepestSchurShift.lean + DeepestLDUReadback.lean, all clean-three):
- `deepBlkA / deepBlkY / deepBlkZ` — reindexed deepest-layer blocks `(reindex deepestPoint_s).toBlocks··`
  (the actual pivot base M̄_s; **B-dependent**).
- `schurCorrectionConj H r B hB hr hL p s = −(deepBlkZ_s + readZ_s)·(deepBlkA_s + readX_s)⁻¹·(deepBlkY_s + readY_s)`
  — the conjugated full-layer Schur correction (reads the FULL reindexed decode layer).
- `reindex_decode_blocks_split` — `reindex(decode w)_s = reindex(deepest_s) + fromBlocks(reads)`.
- `absorbedCoreConj_eq_schurCore` — **THE DICT-MATCH KEYSTONE**. For a boundary layer (hyp
  `hT : (reindex deepest_s).toBlocks₂₂ = 0`): `decode(q).core_s + schurCorrectionConj_s = (1,1)-Schur
  core of reindex(decode w)_s` = exactly the conjugated cores `hC0`/`hC1` read. **This is the proof that
  the conjugated producer discharges the readback — the green-but-won't-wire risk, eliminated in Lean.**
- `deepBlkT_layer0_zero` / `deepBlkT_layerLast_zero` — the `hT` hypothesis at L=2's two boundary layers
  (`deepestPoint_layer0_cols_vanish` / `_layerLast_rows_vanish` + `rThresholdSplit_symm_inr`).

KEY FACT for the threading: `schurCorrectionConj 0 = 0` at **every** layer (boundary: deepest Y₀=0 /
Z₁=0 ⟹ a zero factor; interior corM: off-diagonal 0). ⟹ the conjugated `deepestCoreAbsorbConj` stays
**basepoint-fixing**, so PIN-0's shift-agnostic obligations transfer. (Verify in Lean — don't assume.)

## REMAINING — the mechanical wire-close (math risk fully retired; dict-only, NO Score/loss touch)

### RECOMMENDED ARCHITECTURE: PARALLEL `…Conj` versions (NOT mutating the bare path)
The bare `schurCorrection`/`schurShiftRaw`/`schurCutoffShift`/`deepestCoreAbsorb` are consumed by
`DeepestGermCharge` (the h2/folded-charge leg) and the L≥3 paths. **Do NOT add `B` to the bare sigs**
(breaks those legs + the abstract coreShear obligations are B-agnostic). Instead build B-dependent
`…Conj` parallels, used ONLY in the L2 wire. The bare path stays untouched (no regression).

### Stage 1 — thread `schurCorrectionConj` up to a conjugated absorb (DeepestSchurShift + DeepestGaugeConstruction)
Conjugated signatures (mirror the bare, + `(B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)`):
```
noncomputable def schurShiftRawConj (H) (r) (B) (hB) (hr) (hL) (p) : Fin (flatDim (deepestM H r)) → ℝ :=
  paramsEquivFlat (deepestM H r) (schurCorrectionConj H r B hB hr hL p)
noncomputable def schurCutoffShiftConj (H) (r) (B) (hB) (hr) (hL) (p) :=
  (cutoffBump H r hr hL p) • schurShiftRawConj H r B hB hr hL p
noncomputable def deepestCoreAbsorbConj (H) (r) (B) (hB) (hr) (hL) :
    DeepestSplit H r (deepestNGauge H r) ≃ₜ DeepestSplit H r (deepestNGauge H r) :=
  coreShearHomeo (schurCutoffShiftConj …) (continuous_schurCutoffShiftConj …)
```
The `cutoffBump`/`unitSet` cutoff machinery is shift-agnostic — REUSE it (the conjugated correction is
ContDiffAt on a unit set where `det(deepBlkA_s + readX_s) ≠ 0`, which holds near 0 since deepBlkA_s = M̄_s
is a UNIT — `deepestPoint_leadingBlock_isUnit` is the source). `schurCorrectionConj_zero` (= 0, see KEY
FACT) ⟹ `schurShiftRawConj_zero` ⟹ `schurCutoffShiftConj_zero` (mirror the bare `*_zero` proofs).

### Stage 2 — the 5 S2/S4 conjugated re-derivations (DeepestSchurSmooth.lean)
Mirror these (the generic matrix bricks `contDiff_matrix_*` / `contDiffAt_matrix_*` /
`hasStrictFDerivAt_triple_mul_zero` are reusable AS-IS — only the schurCorrection-keyed ones re-derive):
1. `contDiffAt_schurCorrectionConj_entry` (mirror `contDiffAt_schurCorrection_entry` @134): the conjugated
   entry is ContDiffAt on a conjugated unit set. Same triple-product route; pivot `(deepBlkA_s + readX_s)⁻¹`
   is ContDiffAt where its det ≠ 0 (deepBlkA_s = M̄_s a unit ⟹ holds near 0). deepBlk·_s are CONSTANT in
   `q` (contDiff_const), readX/Y/Z ContDiff — so the sum is ContDiff.
2. `contDiffAt_schurShiftRawConj` (mirror @162): `paramsEquivFlatCLE ∘ schurCorrectionConj`.
3. `contDiff_schurCutoffShiftConj` (mirror `contDiff_schurCutoffShift` @208): `contDiff_contDiffBump_smul`.
4. `hasStrictFDerivAt_schurCorrectionConj_entry_zero` (mirror @299): the entry has strict-deriv 0 at 0.
   **Subtlety:** the conjugated correction does NOT have BOTH outer factors vanish at 0 (deepBlkZ_s,
   deepBlkY_s are constants ≠ 0 in general). BUT at the boundary layers deepBlkY_0 = 0 (layer-0) and
   deepBlkZ_1 = 0 (layer-(L−1)) — so ONE outer factor's CONSTANT part is 0 and the deviation part vanishes
   at 0; the product `(deepBlkZ + readZ)·A⁻¹·(deepBlkY + readY)` at layer 0 = `(deepBlkZ + readZ)·A⁻¹·readY`
   (deepBlkY_0=0), whose strict-deriv at 0 is 0 because the RIGHT factor `readY` vanishes value+deriv at 0
   (`hasStrictFDerivAt_matrix_mul_entry_of_right_zero`, banked in DeepestDiffeoBridgeL2). Layer-1 dually
   (left factor `readZ` vanishes, deepBlkZ_1=0). **So S4 needs the per-boundary-layer deepBlk vanishing —
   this is the genuine non-mechanical bit; use deepBlkY_layer0_zero / deepBlkZ_layerLast_zero (analogues
   of the deepBlkT_*_zero I banked, via deepestPoint_layer0_cols_vanish / _layerLast_rows_vanish on the
   .toBlocks₁₂ / .toBlocks₂₁ arms).** This S4 is L2-layer-specific (NOT all-layer) — fine, the wire is L=2.
5. `hasStrictFDerivAt_schurShiftRawConj_zero` / `hasStrictFDerivAt_schurCutoffShiftConj_zero` (mirror
   @357 / @379): the flat-descent + the χ=1 inner-ball congr. Same template.

### Stage 3 — a conjugated `deepestCoreF_coreAbsorbConj_eq_prodSchur` (DeepestGaugeConstruction or a new file)
Mirror `deepestCoreF_coreAbsorb_eq_prodSchur` (@1945): on the inner ball,
`deepestCoreF (deepestCoreAbsorbConj q).2.1 = frobSq(prod(deepestM)(fun s => decode(q).core_s +
schurCorrectionConj (q.1,q.2.2) s))`. Same proof (the `coreShearHomeo` ADD-form + `schurCutoffShiftConj =
schurShiftRawConj` on the inner ball + `paramsEquivFlat` additivity).

### Stage 4 — rewire sub-4 + close the bridge (DeepestL2Wiring.lean, the `hsub4core` block ~line 636-654)
The current `hsub4core` discharge is a documented `sorry` (line ~654). Replace with: use
`deepestCoreAbsorbConj` for the chart's `coreAbsorb` (NOTE: this changes the chart's `coreAbsorb` field —
check `deepest_gauge_construction` threads `coreAbsorb := deepestCoreAbsorbConj` consistently, incl. PIN-0
`deepest_coreAbsorb_exists` → a conjugated `deepest_coreAbsorbConj_exists`). Then:
- `deepestCoreF (deepestCoreAbsorbConj (psiSplitRawL2 …)).2.1 = frobSq(prod(deepestM)(decode + conjCorr))`
  [Stage-3 lemma];
- the cleaned tuple `C := Function.update (fun s => decode(q).core_s + schurCorrectionConj_s) last
  ((1−l2K)·l2S1)` (conjugated l2K/l2S1 too — or absorb into C directly);
- discharge `hC0`/`hC1` via `absorbedCoreConj_eq_schurCore` (+ `deepBlkT_layer0_zero` /
  `deepBlkT_layerLast_zero` for the `hT` at the two layers; note `prod_deepestM_eq_schur_ldu_readback` is
  `H : Fin 3` — the wire is general-L + hL2eq, so `subst hL2eq` first to land at `Fin 3`);
- apply `prod_deepestM_eq_schur_ldu_readback` → Score; feed `deepest_diffeo_bridge_L2_wired`.
**The L2K/l2S1 last-layer pieces also conjugate** (pivot `deepBlkA_last + readX_last` not `1 + readX_last`)
— mirror l2K/l2S1/l2W/l2P00 in DeepestDiffeoBridgeL2 as `…Conj` OR fold the last-layer core directly into
`C 1` = the conjugated `(1−K̂)·Ŝ1` from `absorbedCoreConj_eq_schurCore` (cleaner — the keystone already
gives the per-layer Schur core; the last-layer (1−K̂) cross-term comes from the LDU in
`unframedSchur_prodDecode_eq_ldu`, NOT from a separate conjugated l2K). **Recommended: set `C` via the
keystone's per-layer cores + the LDU's K̂, sidestepping a conjugated l2K/l2S1 entirely.**

### Stage 5 — the two B-independent residuals (DeepestL2Wiring.lean)
- `hQtri'` (~line 488): the `(lastLayer).succ = Fin.last L` **Matrix-WIDTH** `▸`-cast transport of
  `toBlocks₂₁ = 0` from the bundle `hQtri` (on `Qf (lastLayer)`/`Jb`) to `endpointQL`/`J`. Unlike `hPtri'`
  (layer-0 `castSucc 0 = 0` is a NO-width-change rfl-cast, one-liner @479), this is a genuine width cast.
  Needs a small helper: `reindex e e (he ▸ M) = reindex (e.trans (finCongr he)) … M`-style, then the
  bundle `hQtri` collapsed to threshold (`pivotThresholdSplit_frontEmbed` /
  `_pivotJSucc_frontEmbed` under `hJfront'` + `hpivJ`). In-scope: `hQtri`, `hpivJ`, `hJfront'`,
  `H_lastLayer_succ`. B-independent, no math — pure cast.
- `hm11 / hm12 / hm21` (~lines 579/584/589): the raw-middle {11,12,21} block agreement (e2/leak-kill,
  RELATIVE so dict-independent). Route MAPPED in the file (lines ~562-572): step1 `Aψ 0 = Aq 0` (layer-0
  shared, `framedParamsPivot_psiSplitRawL2Core_of_ne` + unit-frame cancel), step2 two-factor unfold
  (`prod_eq_prodAux_mul_last` m=1), step3 layer-1 X/Z fixed + e2 on {12} via `e2_regPreserve` +
  `reindex_prod_regBlocks_eq_of_e2` (banked). Foundation `reindex_decodeDev_eq_fromBlocks_reads` (banked).

### OUT OF SCOPE (leave as-is, scoped sorries)
DeepestL2Wiring `hinterface` L≥3 interior (lines ~308/313) + the L≥3 branch (~662) — the general-L
grouped-G0 diffeo, NOT this tide.

## Call-site enumeration (for the parallel-version threading)
`schurCutoffShift` (bare, KEEP) live call sites — the conjugated wire needs `…Conj` analogues, NOT edits here:
- DeepestGaugeConstruction.lean:342 (`deepestCoreAbsorb` def), :351 (`_mp`), :370-371 (`_exists` PIN-0),
  :1956/:1958/:1960 (`_eq_prodSchur` inner-ball raw).
- DeepestL2Wiring.lean:235-246 (`hTilde`: `contDiff_schurCutoffShift` + `contDiff_coreShearHomeo_symm` +
  `hasStrictFDerivAt_…_symm_zero`) — **NOTE: hTilde uses coreAbsorb.symm; if the chart's coreAbsorb
  becomes Conj, hTilde must use `deepestCoreAbsorbConj` + `contDiff_schurCutoffShiftConj` etc.**
- DeepestSchurSmooth.lean:208/379 (the bare ContDiff/strictFDeriv — KEEP; add Conj parallels).
- DeepestSchurShift.lean:359/364/380/387 (the bare def + lemmas — KEEP; add Conj parallels).
`deepestCoreAbsorb` live sites: DeepestGaugeConstruction :349/:359-364/:1950/:1955/:1977/:2006/:2676;
DeepestGermCharge :10 (h2 leg — DO NOT TOUCH, stays bare); DeepestDiffeoBridgeL2 :2884/:2901/:2971/:2994/
:3048/:3092/:3115 (sub-4 + comp_identity + _impl — these take `coreAbsorb` as a PARAM `hcoreabs :
coreAbsorb = deepestCoreAbsorb`; for the conjugated wire, supply `coreAbsorb = deepestCoreAbsorbConj` and
change `hcoreabs` accordingly, OR keep the param abstract and thread Conj at the wire); DeepestL2Wiring
:70/:90/:209/:641.

**genm-l2conj (me) is available as the L2-context resource** via the controller for the ~30-site
specifics, the keystone internals, and the S4 boundary-vanishing subtlety (Stage 2 step 4).
