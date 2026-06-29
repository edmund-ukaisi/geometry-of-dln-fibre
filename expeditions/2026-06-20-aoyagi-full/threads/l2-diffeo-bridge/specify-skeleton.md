# SPECIFY — `deepest_diffeo_bridge_L2` (the L=2 gauge-slice diffeo bridge)

Skeleton + sub-lemma signatures, for controller approval BEFORE filling. Builds from the g146
design certs (`../31-pin2-comparability/h2-diffeo-bridge-cert.md`,
`h2-joint-psi-cert.md`). L=2 ONLY; does NOT touch 3289.

## Target

The bare `sorry` at `DeepestGaugeConstruction.lean:2915` is the body of
`deepest_diffeo_bridge_L2` (header 2853): for the joint `(T1,Y1)` Ψ at `L=2`,
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, where
`Φscore x = ∑(regStraighten(split x)).1² + Score x`,
`Φcore x = ∑(regStraighten(split x)).1² + deepestCoreF H r (coreAbsorb (split x)).2.1`.

## Module placement

NEW module `DeepestDiffeoBridgeL2.lean` (imports `DeepestGaugeConstruction` + my
`DeepestLeadingBlock`). The bridge CONTENT is built here as `deepest_diffeo_bridge_L2_impl`
with the IDENTICAL signature to `deepest_diffeo_bridge_L2`. The controller then replaces
2915's `sorry` with `exact DeepestDiffeoBridgeL2.deepest_diffeo_bridge_L2_impl H r B …`
(single-writer producer — I do not edit it). The `_impl` lemma is independently
`#print axioms`-verifiable.

OPEN QUESTION for controller: alternatively, do you want the bridge body filled IN PLACE at
2915 (you paste my proof term)? The `_impl` route keeps the producer single-writer and gives
independent axiom-verification; I default to it unless you prefer in-place.

## The Ψ (from the design cert, verified exact ~1e-17)

Act on the last-layer core `T1` AND last-layer reg read `Y1`; fix everything else:

    K   := Z1 · ⅟P00 · Y0                         (M1×M1, = O(read²))
    W   := I_{M1} + Z1·A1⁻¹·A0⁻¹·Y0               (M1×M1 unit near wstar)
    S1  := T1 − Z1·A1⁻¹·Y1
    T1' := W⁻¹·[ (I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1 ]
    Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')

`A0 = 1+X0`, `A1 = 1+X1` (the per-layer reg reads, units near wstar). `A0⁻¹` is where my KC1
`deepestPoint_leadingBlock_isUnit` / the regular-block invertibility supplies `[Invertible A0]`.

## Skeleton (sub-lemmas, sorry-each, in dependency order)

### S0 — the raw Ψ map on flat coords (def, no proof)
`psiRawL2 : (Fin (flatDim H) → ℝ) → (Fin (flatDim H) → ℝ)` — `split⁻¹ ∘ (joint (T1,Y1) action on
DeepestSplit) ∘ split`. The action reads the core/reg slots of `DeepestSplit H r (deepestNGauge H r)`,
applies the closed form, writes back. Built via the `DeepestPsiLens` read-lenses + `Function.update`.
RISK: the slot-encoding bookkeeping (which `DeepestSplit` fields are T1/Y1/Z1/A_s) — the cert §(2)
names them via `framedParamsPivot` blocks; I confirm the exact field maps in-build against
`DeepestPsiLens` (`readX/readY/readZ_regGaugeSlotEquiv_symm`).

### S1 — the cutoff Ψ (def, no proof): `psiL2 := wstar + χ·(psiRawL2 − wstar)`
Reuse the banked `cutoffBump`/`schurCutoffShift` pattern (`DeepestSchurShift:270/310`): χ a
`ContDiffBump`, χ=1 on a ball ⊂ the common invertibility locus `U_inv = {det A0,det A1,det W,det P00 ≠ 0}`,
`tsupport χ ⊂ U_inv`. `psiL2 = psiRawL2` on χ=1, `= id` off `tsupport χ`.

### S2 — `psiL2_contDiff : ContDiff ℝ ⊤ psiL2`   [HEAVIEST]
The two NEW composite-inverse smoothness lemmas (`W⁻¹`, `⅟P00`) ContDiff-on-`U_inv` via
`contDiffAt_matrix_inv_entry_of_det_ne_zero` (banked) + `ContDiff.mul` of the banked per-layer
`(1+X_s)⁻¹` (`DeepestSchurSmooth:117`); then χ-cutoff to global (the `contDiff_schurCutoffShift`
pattern, `:208`). Consumes: `split` smoothness `contDiff_deepestSplit` (BANKED).

### S3 — `psiL2_fixpoint : psiL2 wstar = wstar`
At wstar all reads → 0 ⟹ K=0, S1=0, the (T1,Y1)-correction = 0; χ(wstar)=1. Light.

### S4 — `psiL2_hasStrictFDerivAt : HasStrictFDerivAt psiL2 (ContinuousLinearMap.id ℝ _) wstar`
The correction is O(read³) ⟹ D(psiRawL2 − id)(wstar) = 0; χ=1 near wstar; `split` deriv is the
`≃L` L, conjugates to id. Mirror `hasStrictFDerivAt_coreShearHomeo_symm_zero` (BANKED) +
`hasStrictFDerivAt_deepestSplit` (BANKED). Moderate.

### S5 — `e2_regPreserve : deepestEFull H r hr hL J Pf Qf ∘ (Ψ_split) = deepestEFull …`   [my KC1 brick]
The EXACT `A0·A0⁻¹=I` cancel (cert §(b), ~tens LoC). P00,P10 are T1,Y1-free (fixed by `rfl`/`congr`);
P01'−P01 = A0(Y1'−Y1)+Y0(T1'−T1) = Y0(T1−T1')+Y0(T1'−T1) = 0 via `[Invertible A0]` (my brick) +
`Matrix.mul_inv_cancel`/`mul_add`. Packs through `deepestEFull`'s `regResidualPack` (the
P00/P01/P10 block-read).

### S6 — `comp_identity : (fun x => Φcore (psiL2 x)) =ᶠ[nhds wstar] Φscore`   [composition plumbing]
On the inner ball (χ=1): the reg term `∑(regStraighten(split x)).1²` is `deepestEFull`-based and
FIXED by S5; the core term `coreΦ(Ψx) = frobSq(S0·(I−K)·S1) = Score(x)` via banked
`deepestCoreF_coreAbsorb_eq_prodSchur` (`:1945`) + the LDU `rcore_schur_factor_of_corner_split`
(`DeepestBlockDecomp:208`). The fiddly part: threading the joint action through
`split`/`coreAbsorb`/`paramsEquivFlat`/`framedParamsPivot` encodings (cert §(2) steps 1-6).

### FINAL — `deepest_diffeo_bridge_L2_impl` (the signature-matching assembly)
`rw [← rlctAtOn_germ_local _ _ wstar (comp_identity …)]` then
`exact rlctAtOn_comp_localDiffeo Φcore wstar psiL2 (.id ℝ _) (S2) (S4) (S3)`
— i.e. EXACTLY the banked `rlctAtOn_diffeo_bridge_of` body (S2/S4/S3/S6 are its four antecedents).

## Banked dependencies (all re-verified present)
- `rlctAtOn_comp_localDiffeo` / `rlctAtOn_diffeo_bridge_of` / `rlctAtOn_germ_local` — abstract bridge.
- `contDiff_deepestSplit` / `hasStrictFDerivAt_deepestSplit` (+symm) — split smooth-affine (DONE).
- `cutoffBump` / `schurCutoffShift` / `contDiff_schurCutoffShift` / `hasStrictFDerivAt_schurCutoffShift_zero` — cutoff.
- `contDiffAt_matrix_inv_entry_of_det_ne_zero` — matrix-inverse smoothness; `DeepestSchurSmooth:117` per-layer (1+X)⁻¹.
- `deepestCoreF_coreAbsorb_eq_prodSchur` (:1945) + `rcore_schur_factor_of_corner_split` (DeepestBlockDecomp:208) — composition.
- `hasStrictFDerivAt_coreShearHomeo_symm_zero` — fderiv-id pattern.
- `DeepestPsiLens` (readX/Y/Z lenses) — the slot read/write.
- `deepestEFull` / `regResidualPack` / `framedParamsPivot_coreZero` — the reg-block read.
- `deepestPoint_leadingBlock_isUnit` (MINE) — `[Invertible A0]` for S5.

## Difficulty ranking (revised, split-promotion DONE)
S2 (composite-inverse cutoff smoothness) > S6 (composition encoding-plumbing) > S4 (fderiv) >
S0/S1 (Ψ defs + slot bookkeeping) > S5 (E2, easy via my brick) > S3 (fixpoint). ~2 tides.

## Risks (honest)
- S0/S6 slot-encoding bookkeeping: which `DeepestSplit` fields ↔ T1/Y1/Z1/A_s. The cert names them
  via `framedParamsPivot` + `DeepestPsiLens`; if the field map is more tangled than the cert's clean
  closed form, S6 balloons. MITIGATION: confirm the field map FIRST (a `#check`/`example` probe against
  `DeepestPsiLens` lenses) before committing to S0's def.
- S2 the `⅟P00` / `W⁻¹` composite-inverse ContDiff: the per-layer is banked; these EXTEND it (product-
  pivot (1,1)-block + the W composite). If `contDiffAt_matrix_inv` doesn't compose cleanly over the
  product-block at v4.29, S2 is the wall — would consult Codex.
- The product-order convention (`prod = S0·S1` vs `S1·S0`) — confirm `prodAux` fold vs LDU `S0·(…)·S1`
  in-build (cert flags it, low risk at L=2 two-factor).

## What I send the controller now
This skeleton + the OPEN QUESTION (_impl vs in-place). On approval I write the Lean skeleton
(defs + 6 sub-lemma signatures, sorry-each, typechecking against the banked interface) and send THAT
diff before filling. Then fill S3→S5→S4→S2→S6→FINAL (light-first to de-risk the assembly early),
diff-gated per soundness-region sub-lemma (esp. S5/S6).

---

# A2 ADDENDUM — the L=2-specialised producer bypass (controller decision: CHARGE A2)

A2 = the bridge (above) + the `_L2` producer bypass that makes the L2 LEG sorryAx-free at L=2.
The headline routes through the GENERIC `deepest_gauge_construction` (2925), which textually
contains 3118/3123 (L≥3 hinterface) + 3289 (L≥3 hstep2) + the 2915 bridge-call. Even with the
bridge built, the generic producer stays sorryAx-poisoned by 3118/3123/3289. The bypass routes
the L=2 headline through an L=2-clean producer instead.

## The 3 producer sorries the bypass must discharge at L=2
- **2915** (hstep2 L=2 branch): the bridge — built by `deepest_diffeo_bridge_L2_impl` (above).
- **3118** (hinterface, interior `Qf s`): `hspos : 1 ≤ s.val` ∧ `hs : s.val+1 < L`. At L=2 ⟹
  `s.val < 1` ∧ `s.val ≥ 1`, contradiction ⟹ `omega`.
- **3123** (hinterface, interior `Pf (s+1)`): `hint : s.val+1 < L−1`. At L=2 ⟹ `s.val+1 < 1`,
  impossible ⟹ `omega`.
- **3289** (hstep2 L≥3 branch): UNREACHABLE at L=2 (`rcases Nat.lt_or_ge L 3` takes the `<3` arm).
  The `_L2` body keeps only the L=2 arm.

## ARCHITECTURE DECISION (for controller — single-writer of the producer)
`deepest_gauge_construction`'s body is 367 lines, almost all L-generic plumbing; only the 3
sorry-branches differ at L=2. Two routes to the `_L2`-clean producer:

- **(R-clone) clone the body** into `deepest_gauge_construction_L2` (new, in my module) with
  `hL2eq : L = 2` added, the 3 branches discharged. COST: ~360-line copy-paste that DRIFTS from
  the original on any future producer edit. Poor bedrock (duplication). I do NOT recommend this.

- **(R-param) parameterize the 3 discharges as hypotheses on the EXISTING
  `deepest_gauge_construction`** (a MINIMAL producer edit, controller's hand): add 3 hypotheses
  `(hbridge : <2915 conclusion>) (hint_qf : <3118 goal>) (hint_pf : <3123 goal>)` and replace the
  3 `sorry`s with `exact hbridge / hint_qf / hint_pf` (the 3289 hstep2 L≥3 branch stays its own
  sorry, OR also becomes a hypothesis `(hstep2_ge3 : <3289 goal>)`). Then:
  - the GENERIC caller (`deepest_gauge_chart_construct`, status quo) passes `sorry` for each — no
    change to its sorryAx status (unchanged behaviour);
  - a NEW `deepest_gauge_chart_construct_L2` (my module) passes the bridge `_impl` + `omega` +
    `omega` (+ for 3289, an `absurd`/`omega` under `hL2eq`), yielding a sorryAx-FREE chart at L=2.
  COST: a ~6-line producer signature edit (controller's hand, single-writer) + the new `_L2`
  wrappers in my module. Clean, no duplication, no drift. **RECOMMENDED.**

Under R-param the producer edit is small and the controller makes it (single-writer); I provide
the exact hypothesis statements + the `_L2` wrappers. Under R-clone I'd own the clone but it's
ugly. **My recommendation: R-param.** Controller decides (it's the producer owner).

## The `_L2` re-thread (my module, either route)
- `deepest_gauge_chart_construct_L2 (… hL2eq : L = 2 …) : Nonempty (DeepestGaugeChart …)` —
  destructures `deepest_gauge_construction(_L2)` with the L=2 discharges, builds the structure
  (verbatim the 3296 wrapper).
- `deepest_gauge_squeeze_exists_frontPivot_L2` — the DeepestNormalFormFrontPivot:52 analogue,
  calling `_chart_construct_L2` (this is in DeepestNormalFormFrontPivot's file, NOT the producer;
  a clean ~3-line wrapper — but that file is also not mine to durably edit if single-writer; flag
  to controller whether I add the `_L2` squeeze there or in my new module).
- Then the headline chain's front-pivot reduction/normal-form consume the `_L2` squeeze at L=2.

## A2 sub-task list (line-count estimate, no wall-clock)
1. Bridge `deepest_diffeo_bridge_L2_impl` (S0-S6 + FINAL above): the bulk, ~2 tides.
2. Producer R-param edit (controller's hand): ~6 lines signature + 3-4 `exact`-swaps.
3. `_L2` chart-construct + squeeze re-thread wrappers: ~30-60 LoC.
4. The headline-chain `_L2` consumption (which Skeleton:1131 / DeepestNormalFormFrontPivot
   theorems route through `_L2` at L=2): controller-orchestrated wiring, flag the touch-points.

## What I send the controller now (A2)
This addendum + the bridge skeleton + the ARCHITECTURE DECISION (R-param vs R-clone) + the
single-writer question (who adds the `_L2` squeeze in DeepestNormalFormFrontPivot). On approval +
route choice, I write the bridge skeleton first (defs + 6 sigs, sorry-each), then fill.
