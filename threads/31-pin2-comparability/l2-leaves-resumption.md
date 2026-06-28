# L2 diffeo-bridge leaves — resumption state (genm-l2cle)

Bridge file: `lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean`.
Branch `genm-l2cle` (off `origin/genm-l2-wt`). Build: `scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2` from the worktree `lean/`.

## LANDED this tide (sorry-free, committed @355515d1)

**The #138 brick already existed** — `regGaugeSlotCLE` + `contDiff_regGaugeSlotEquiv` are in
`DeepestFramedProduct.lean:43-61`; the whole entrywise ContDiff/matrix-inv ladder
(`contDiffAt_matrix_inv_entry_of_det_ne_zero`, `contDiffAt_matrix_mul_entry`,
`contDiffAt_inv_one_add_readX_entry`) AND the full S4 analogue for the single Schur shift
(`hasStrictFDerivAt_schurShiftRaw_zero` via `hasStrictFDerivAt_triple_mul_zero`) are in
`DeepestSchurSmooth.lean`. No new CLE was needed.

**S0b lens decomposition** (the linchpin both S2+S4 stand on):
- named matrices `l2A0/A1/Y0/Z1/Y1/T1/P00/T1p/Y1p` + `l2g'` (= `psiSplitRawL2Core`'s `let` bodies; `psiSplitRawL2Core_eq` confirms by `rfl`)
- `paramsEquivFlatCLE_symm_coe` / `regGaugeSlotCLE_symm_coe`
- payloads `l2CoreΔTuple` (= `update 0 last (T1'−T1)`), `l2GaugeΔ` (= `g' − g`)
- `paramsEquivFlatCLE_l2CoreΔTuple_eq`
- **`psiSplitDeltaL2Core_eq_payload`**: at L=2, `psiSplitRawL2Core q − q = (rgΔ.1,(cΔ,rgΔ.2))`, `rgΔ = regGaugeSlotCLE.symm (l2GaugeΔ q)`, `cΔ = paramsEquivFlatCLE (l2CoreΔTuple q)`

**S4a matrix-entry strict-fderiv-0 helpers** (generic over `X`, proven):
`hasStrictFDerivAt_matrix_mul_entry_of_left_zero` / `_of_right_zero` / `_triple_mul_entry_zero`.

**S4b at-0 values** (proven): `gaugeProj_zero`, `l2A0_zero`/`l2A1_zero` (=1), `l2Y0_zero`/`l2Z1_zero`/`l2Y1_zero`/`l2T1_zero` (=0).

Scalar atoms available: `hasStrictFDerivAt_triple_mul_zero` (DeepestSchurSmooth), and (built but NOT yet
moved to the bridge — re-derive or lift from git history of ScratchS4) `hasStrictFDerivAt_mul_zero_zero`,
`hasStrictFDerivAt_mul_of_right_zero`, `hasStrictFDerivAt_mul_of_snd_zero`.

## REMAINING (3 honest sorries)

### S4 — `hasStrictFDerivAt_psiSplitDeltaL2_zero` (line ~683), the L=2 branch
Reduction VALIDATED in scratch (build it back): `psiSplitDeltaL2 = (q ↦ encoded payloads)` (rw
`psiSplitDeltaL2`/`psiSplitRawL2 dif_pos`/`psiSplitDeltaL2Core_eq_payload`), then each of the 3 prod
slots has strict-fderiv-0 via CLE-composition:
- `regGaugeSlotCLE.symm.toCLM .hasStrictFDerivAt .comp 0 (hasStrictFDerivAt_l2GaugeΔ_zero)` → `.1`/`.2` via fst/snd CLM
- `paramsEquivFlatCLE.toCLM .hasStrictFDerivAt .comp 0 (hasStrictFDerivAt_l2CoreΔTuple_zero)`
- assemble `h1.prodMk (hcore.prodMk h3)`

The two payload facts (the genuine algebra, Codex route A — answer banked at
`codex/s4-matrix-deriv-answer.md`):
- **`hasStrictFDerivAt_l2GaugeΔ_zero`**: via `hasStrictFDerivAt_pi'` per `idx`; only last-layer Y-tags
  nonzero = `(l2Y1p − l2Y1) i j`. `l2Y1p − l2Y1 = A0⁻¹·Y0·(T1−T1')` (triple, `Y0` and `(T1−T1')` vanish
  → `_triple_mul_entry_zero`). Needs `(T1'−T1)` value-0 at origin (from `psiSplitRawL2Core_zero` /
  `l2T1p 0 = l2T1 0` — derive).
- **`hasStrictFDerivAt_l2CoreΔTuple_zero`**: via `pi'` per layer; only last layer nonzero = `T1'−T1`.
  Normalize `T1'−T1 = (W⁻¹−1)·Br + (Br−T1)`, `Br−T1 = −K·S1 + R·T1` (matrix `ring`/`ext`+`simp`),
  each summand `_left_zero`/`_triple` (`K`,`R` are O(read²); `(W⁻¹−1)` is the one new piece).
  **`W⁻¹−1` deriv-0**: on the open nbhd `{det W ≠ 0}` (det W continuous, =1 at 0), `W⁻¹−1 = −(W⁻¹·(W−1)) = −(W⁻¹·R)`
  (from `nonsing_inv_mul`, `IsUnit det`), RHS deriv-0 via `_of_right_zero` (R = W−1 = Z1·A1⁻¹·A0⁻¹·Y0 vanishes
  value+deriv); lift entrywise by `HasStrictFDerivAt.congr_of_eventuallyEq`.

### S2 — `contDiffAt_psiSplitDeltaL2_of_mem_tsupport` (line ~623), the L=2 branch
Same payload decomposition; `ContDiffAt` of `regGaugeSlotCLE.symm ∘ l2GaugeΔ` + `paramsEquivFlatCLE ∘ l2CoreΔTuple`.
Reduces (CLE.contDiff.comp + contDiffAt_pi') to ContDiffAt of `l2T1p`/`l2Y1p` matrix entries.
**RADIX BLOCKER (design decided, NOT yet built)**: needs `det(1+readX_s)≠0` AND `det l2P00 ≠ 0` AND
`det W ≠ 0` at `q ∈ tsupport(cutoffBumpSplit)`. The banked `cutoffBumpSplit` is keyed to `unitRadius/2`
(only the `1+readX` locus). RE-KEY `cutoffBumpSplit` to a joint-unit radius (ball where all three dets ≠ 0;
P00,W = 1 at 0, so a small ball works). `cutoffBumpSplit` is used abstractly downstream (ContDiffBump
fields + `eventuallyEq_one` + `.contDiff`) → re-keying is LOCAL to the bridge file. Build a `jointUnitSet`
(intersection of 3 open det≠0 conditions, guarded by `dite (L=2)` for L-genericity) mirroring
`unitSet`/`unitRadius`/`isOpen_unitSet`. Then a `ContDiffAt`-variant matrix-inverse-entry lemma is needed
(`contDiffAt_matrix_inv_entry_of_det_ne_zero_at` — same proof as the landed one but with `ContDiffAt`
determinant/adjugate, since W's entries are only ContDiffAt).

### S6 — `comp_identity_L2` (line ~876), the genuine geometric leaf (deepest, research-grade)
`Φcore ∘ psiL2 =ᶠ[𝓝 wstar] Φscore`. Near wstar: `psiL2 = psiRawL2` (S5 germ, `psiL2_eventuallyEq_psiRawL2`),
`deepestCoreF(coreAbsorb …) = frobSq(prod(core+schurCorrection))` (`deepestCoreF_coreAbsorb_eq_prodSchur`,
inner ball). Core algebra banked in `DeepestCompositionE1.lean` (`prod_absorbed_eq_schur_ldu`: the LDU
`Rcore = S0(I−K)S1`). Needs: E2 reg-preservation (`e2_regPreserve`, landed) + wiring psiL2's edited
(T1',Y1') into the LDU energy identity + the framed-product `Score`. Largest remaining; assess for a
dedicated tide.

## Codex artefacts
`codex/s4s2-decomposition-{prompt,answer}.md`, `codex/s4-matrix-deriv-{prompt,answer}.md`.
