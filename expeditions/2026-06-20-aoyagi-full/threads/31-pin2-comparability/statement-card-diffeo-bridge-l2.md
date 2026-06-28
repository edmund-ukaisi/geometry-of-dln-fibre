# Statement card — L=2 gauge-slice diffeo bridge (`DeepestDiffeoBridgeL2.lean`)

**Status (2026-06-28 update — REAL map now built):** `psiSplitRawL2` is the genuine certified joint
`(T1,Y1)` action at L=2 (no longer the `id` placeholder). **S3 (fixpoint) is now proven FOR THE REAL
MAP** (axiom-clean, via `psiSplitRawL2Core_zero` — the real action fixes the split origin). S5
(`e2_regPreserve`) + the χ=1 reduction (`psiL2_eventuallyEq_psiRawL2`) stand, axiom-clean. FINAL assembly
WIRED. Builds green (2741 jobs). **THREE remaining `sorry`s, all under correct statements:** the two L=2
leaves `contDiffAt_psiSplitDeltaL2_of_mem_tsupport` (S2's composite-inverse ContDiff) and
`hasStrictFDerivAt_psiSplitDeltaL2_zero` (S4's O(read³) deriv-0) — re-opened (correctly) when the real
map replaced the placeholder — plus `comp_identity_L2` (S6, the LDU composition identity). Forced
`#print axioms`: S3/S5/χ-reduction `[propext, Classical.choice, Quot.sound]`; S2/S4/FINAL carry `sorryAx`.

## What is the goal
`deepest_diffeo_bridge_L2_impl` — the standalone, `#print axioms`-verifiable content of
`deepest_diffeo_bridge_L2` (the `DeepestGaugeConstruction:2925` site). Conclusion:
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, where `Φscore = ∑‖reg‖² + Score` (matrix-Schur Score)
and `Φcore = ∑‖reg‖² + deepestCoreF(coreAbsorb(split ·)).2.1` (absorbed core). The signature carries the
soundness-amending triangularity hypotheses `hPtri`/`hQtri` (E2 false at general endpoint frames).

## The reparametrization Ψ (`psiL2`)
`psiL2 = split⁻¹ ∘ psiSplitCutL2 χ ∘ split` (the affine-chart conjugate), with
`split = deepestSplit … wstar` (the banked smooth affine chart) and `psiSplitCutL2 χ q = q + χ q •
(psiSplitRawL2 q − q)` (Codex-confirmed correction-cutoff form). The cutoff `χ = cutoffBumpSplit` is a
fresh full-`DeepestSplit` `ContDiffBump` at `0`. `psiSplitRawL2` is the joint `(T1,Y1)` action; it is
the **skeleton placeholder `id`** at this stage (S6/S5 fill the certified `W⁻¹·[…]` closed form).

## PROVED sorry-free (the diffeo side — Codex confirmed these land before S6)
- **S3 `psiL2_fixpoint`** — `psiL2 wstar = wstar` (basepoint `split wstar = 0` + `psiSplitCutL2_zero`).
- **S4 `psiL2_hasStrictFDerivAt`** — `HasStrictFDerivAt psiL2 (id) wstar`. Via the named
  `hasStrictFDerivAt_psiSplitCutL2_zero` (deriv `id` at `0`: the smul product rule `χ(0)•Dδ(0) +
  Dχ(0).smulRight δ(0) = 0` since `δ(0) = 0` AND `Dδ(0) = 0`) + chain-rule through `deepestSplitCLE`.
- **S2 `psiL2_contDiff`** — `ContDiff ⊤ psiL2`. Via the named `contDiff_psiSplitCutL2` (banked
  `contDiff_contDiffBump_smul` on the correction, needing `δ` `ContDiffAt` on `tsupport χ`) + the banked
  `contDiff_deepestSplit`/`_symm`. The composite-inverse `ContDiffAt`-on-support is isolated in
  `contDiffAt_psiSplitDeltaL2_of_mem_tsupport` (the W⁻¹/⅟P00 smoothness leaf, banked-pattern-ready).
- **S5 `e2_regPreserve`** — the frame-free E2 keystone: for `Invertible A0`,
  `A0·(Y1 + ⅟A0·Y0·(T1−T1')) + Y0·T1' = A0·Y1 + Y0·T1` (the `P01` block fixed under the joint move, any
  `T1'`). The exact `A0·⅟A0 = I` cancel; ~6 LoC. The matrix core the eventual reg-term consumes.
- **`psiL2_eventuallyEq_psiRawL2`** — the χ=1 germ reduction: `psiL2 =ᶠ[𝓝 wstar] psiRawL2`
  (`cutoffBumpSplit` = 1 near `0`, pulled back along the continuous `split`). The sub-step the eventual
  S6 stands on (lets the LDU identity be proved against the honest rational Ψ, not the cutoff).
- **FINAL `deepest_diffeo_bridge_L2_impl`** — fully WIRED via the banked `rlctAtOn_diffeo_bridge_of`
  (germ-locality + `rlctAtOn_comp_localDiffeo`), consuming S2 + S4 (`e = ContinuousLinearEquiv.refl`,
  defeq the `id` deriv) + S3 + S6. Compiles; the only `sorryAx` it inherits is S6's.

## The one remaining gap (S6 `comp_identity_L2`)
`Φcore ∘ psiL2 =ᶠ[𝓝 wstar] Φscore`. UNPROVABLE with the placeholder `psiSplitRawL2 = id` (it would need
`Score = coreΦ∘coreAbsorb∘split`, the real identity). Requires: (1) fill `psiSplitRawL2` with the
certified `W⁻¹·[…]` joint action through `paramsEquivFlat`-reencode (core) + `regGaugeSlotEquiv.symm`-
reencode (Y1) + `Function.update`; (2) the LDU core chain `coreΦ(Ψx) = frobSq(S0·(I−K)·S1) = Score`
(`deepestCoreF_coreAbsorb_eq_prodSchur` + `DeepestCompositionE1.prod_absorbed_eq_rcore` +
`rcore_schur_factor_of_corner_split`); (3) the reg term via S5 (`e2_regPreserve`) connected through
`regStraighten`/`deepestEFull`. Cert estimate: 1–2 tides of encoding plumbing; the cast-quirk (CLAUDE.md
opaque-width note) is the live risk on the `lastLayer.castSucc`/`.succ` block dimensions.

## Typed scaffold for the S6 fill (banked in-file)
`coreLast` (the `T1` block read off `q.2.1`), `coreLastNew` (the `T1'` target type — placeholder body),
`wstarL2`, `cutoffBumpSplit` — pin the exact target types for the `psiSplitRawL2` fill.

## Files
`lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean` (526 LoC). Design certs:
`threads/31-pin2-comparability/h2-diffeo-bridge-cert.md`, `h2-joint-psi-cert.md`. Codex def-shape
consult: `threads/31-pin2-comparability/codex/psi-l2-def-{prompt,answer}.md`.
