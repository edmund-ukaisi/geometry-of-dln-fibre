# Statement card — L=2 gauge-slice diffeo bridge (`DeepestDiffeoBridgeL2.lean`)

**Status (2026-06-28, genm-l2leaves @ `1b5ddbba`):** the REAL certified joint `(T1,Y1)` action is built,
and **S4 and S2 — the two honest diffeo-side leaves — are now sorry-free and fidelity-reviewed (PASS).**
S3 (fixpoint), S5 (`e2_regPreserve`), and the χ=1 reduction (`psiL2_eventuallyEq_psiRawL2`) stand,
axiom-clean. Builds green (2741 jobs). **ONE remaining `sorry`:** `comp_identity_L2` (S6, the LDU
composition identity — depth-checkpointed as a dedicated tide). Forced `#print axioms`: S2, S4, S3, S5,
the χ-reduction, `psiL2_contDiff`, `isOpen_jointUnitSet`, `tsupport_cutoffBumpSplit_subset_jointUnitSet`
all `[propext, Classical.choice, Quot.sound]` (no `sorryAx`); FINAL still carries `sorryAx` via S6.

## What is the goal
`deepest_diffeo_bridge_L2_impl` — the standalone, `#print axioms`-verifiable content of
`deepest_diffeo_bridge_L2` (the `DeepestGaugeConstruction:2925` site). Conclusion:
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, `Φscore = ∑‖reg‖² + Score` (matrix-Schur Score),
`Φcore = ∑‖reg‖² + deepestCoreF(coreAbsorb(split ·)).2.1` (absorbed core). Signature carries the
soundness-amending triangularity hypotheses `hPtri`/`hQtri` (E2 false at general endpoint frames).

## The reparametrization Ψ (`psiL2`)
`psiL2 = split⁻¹ ∘ psiSplitCutL2 χ ∘ split`, `psiSplitCutL2 χ q = q + χ q • (psiSplitRawL2 q − q)`.
At `L = 2`, `psiSplitRawL2 = psiSplitRawL2Core`, the certified closed form (cert-verified ~1e-17):
`T1' = W⁻¹·[(1−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1]`, `Y1' = Y1 + A0⁻¹·Y0·(T1−T1')`. The cutoff
`χ = cutoffBumpSplit` is re-keyed to `jointUnitRadius` (the joint-unit locus where `1+readX_s`, `P00`,
`W` are all invertible).

## PROVED sorry-free + reviewed (the diffeo side)

> **Claim (S4).** The joint-action correction has vanishing strict Fréchet derivative at the split origin.
>
> - **Lean:** `DLNFibre.DLN.RLCT.hasStrictFDerivAt_psiSplitDeltaL2_zero`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean` @ `1b5ddbba`)
> - **Gloss.** `HasStrictFDerivAt psiSplitDeltaL2 0 0` — `D(psiSplitRawL2 − id)(0) = 0`.
> - **Proved.** The `O(read²)` higher-order vanishing: lens decomposition (`psiSplitDeltaL2Core_eq_payload`)
>   to the encoded payload triple; core payload via the flat-decode (each flat coord a `l2T1p − l2T1`
>   last-layer entry or const-0), gauge payload via `pi'` per `RegGaugeIdx` (last Y-tag = `l2Y1p − l2Y1`).
>   The block deriv-0 facts come from the additive matrix normalization `T1'−T1 = (W⁻¹−1)·Br + (−K·S1 + R·T1)`
>   (via `abel`), each summand's left factor (`W⁻¹−1`, `K`, `R`) vanishing value+deriv at 0 (`K`, `R` via the
>   triple-helper; `W⁻¹−1 = −(W⁻¹·R)` via eventuallyEq on `{det W ≠ 0}` + `nonsing_inv_mul`).
> - **Assumed.** none beyond the L-generic hypotheses (`hr`, `hL`); the L=2 branch is the real action.
> - **Cited.** none. **Deferred.** none. **Status.** sorry-free + reviewed.

> **Claim (S2).** The joint-action correction is `ContDiffAt ⊤` on the cutoff support.
>
> - **Lean:** `DLNFibre.DLN.RLCT.contDiffAt_psiSplitDeltaL2_of_mem_tsupport`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean` @ `1b5ddbba`)
> - **Gloss.** for `q ∈ tsupport(cutoffBumpSplit)`, `ContDiffAt ℝ ⊤ psiSplitDeltaL2 q`.
> - **Proved.** Re-keyed `cutoffBumpSplit` to `jointUnitRadius`; `jointUnitSet` open (`isOpen_jointUnitSet`)
>   and contains 0 (`mem_jointUnitSet_zero`), so `tsupport ⊆ jointUnitSet` gives the four det conditions
>   (`A0`, `A1`, `P00`, `W`) at `q`; the general-`p` entry-`ContDiffAt` bank assembles the payload triple.
> - **Assumed.** `q ∈ tsupport(cutoffBumpSplit)` (the genuine cutoff support; det conditions derived, not assumed).
> - **Cited.** none. **Deferred.** none. **Status.** sorry-free + reviewed.

- **S3 `psiL2_fixpoint`**, **S5 `e2_regPreserve`**, **`psiL2_eventuallyEq_psiRawL2`**, **`psiL2_contDiff`**,
  **`contDiff_psiSplitCutL2`** — all sorry-free, axiom-clean; now consume the real S2/S4.
- **FINAL `deepest_diffeo_bridge_L2_impl`** — fully WIRED via `rlctAtOn_diffeo_bridge_of`, consuming
  S2 + S4 + S3 + S6. Compiles; the only `sorryAx` it inherits is S6's.

## The one remaining gap (S6 `comp_identity_L2`) — DEDICATED TIDE
`Φcore ∘ psiL2 =ᶠ[𝓝 wstar] Φscore`. The geometric leaf. Banked starting pieces:
`DeepestCompositionE1.prod_absorbed_eq_schur_ldu` (the LDU `Rcore = S0·(1−K)·S1`, sorry-free + axiom-clean),
`e2_regPreserve`, `psiL2_eventuallyEq_psiRawL2`, and `deepestCoreF_coreAbsorb_eq_prodSchur` (for the SINGLE
Schur shift). The wall (all NEW): (1) tie psiL2's actual `T1' = l2W⁻¹·l2Br` to the E1 absorb form
`S1' = (1−K)·S1` (a matrix identity re-derived against the actual `l2T1p` def); (2) expand the framed-product
`Score` and match `prod_absorbed_eq_schur_ldu`'s RHS at wstar; (3) wire the E2 reg-term through `deepestEFull`;
(4) assemble the `=ᶠ[nhds wstar]` germ. Estimate: a dedicated tide.

## Files
`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean`. Design certs:
`threads/31-pin2-comparability/h2-diffeo-bridge-cert.md`, `h2-joint-psi-cert.md`. Codex consults:
`threads/31-pin2-comparability/codex/s4s2-decomposition-{prompt,answer}.md`,
`s4-matrix-deriv-{prompt,answer}.md`, `s2-rekey-{prompt,answer}.md`. Resumption:
`threads/31-pin2-comparability/l2-leaves-resumption.md`.
