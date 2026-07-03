# genm-hdomprod — the rectangular two-peel D1 ≥-leg (item-5 closed, hDom reduced to 3 gates)

Front-loaded the reviewer-flagged item-(5) C¹-vs-C² regularity risk (assessed BOUNDED, then CLOSED in
Lean), then built the rectangular value arithmetic + the two-peel producer, sharpening the prior
`D1L2ProducerReduction` single-`hDom` residual into a legible two-peel C² chain whose remaining debt is
THREE precisely-named per-`v` geometric gates. Reviewed (fidelity + soundness) + decorrelated Codex:
**SURVIVED — honest, integration-ready, nothing laundered.**

## Deliverables (branch `genm-hdomprod`, off `origin/genm-d1l2prod`)

Four modules, all sorry-free, all clean-three `[propext, Classical.choice, Quot.sound]` (forced
`#print axioms`). No name clashes with siblings. NOT yet in the aggregator (controller wires).

---

> **Item (5) — the first-peel residual at C² + slice-vanishing (the flagged risk, CLOSED).**
>
> - **Lean:** `DLNFibre.DLN.RLCT.dln_hchart_residual_c2`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1HChartResidualC2.lean`)
> - **Gloss.** Same hypotheses as the banked `dln_hchart_residual` (optimal `v`, `rank B = r`,
>   injective `er`/`ec`, invertible flat-Jacobian minor); conclusion STRENGTHENED to a GLOBAL
>   `ContDiff ℝ 2 q` (up from C¹) AND `q (0, t0) = 0`, with the RLCT chart-transfer verbatim the banked
>   one. Feeds the second peel's `hslice`/`hslice0`.
> - **Proved.** The C² is real — the bump `exists_contDiff_eventuallyEq_of_contDiffOn` is called at
>   `(n := 2)` on a `ContDiffOn ℝ 2` composite (no `.of_le` downgrade in the C² chain). `q(0,t0)=0`
>   proved via `rawResidVec_zero_of_optimal` (fed `Ψsymm 0 = 0`, exposed by the new
>   `rlctAtOn_eq_of_contDiff_chart_rinv_fix`) + `lossEntry_zero_of_optimal`.
> - **Assessment (item 5 = STATED-CEILING, not obstruction).** Decorrelated Codex xhigh
>   (`codex/item5-regularity-*`) + source-read: the whole chart chain is C^∞ (`contDiff_chartΦ` proves
>   each coord `ContDiff ℝ ⊤`); `ContDiffAt.to_localInverse` preserves C^n; the only C¹ drop in the
>   banked producer was the `(n := 1)` bump call. No new analytic content — pure `n`-plumbing.
> - **Cited.** none. **Status.** sorry-free, clean-three.

---

> **Item (2) — the rectangular value arithmetic (cross-paired extra).**
>
> - **Lean:** `DLNFibre.DLN.RLCT.coreRect_le_extraRect_half_add_lambdaCore_Mprime`
>   (+ `Mval_MprimeRect_add_extra_eq`, `cand_mem_Adm_rect`,
>   `lambdaCore_le_extraRect_half_add_lambdaCore_Mprime`, `extraCountRect`, `MprimeRect`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1RectValueArith.lean`)
> - **Gloss.** `ofReal(lambdaCore M) ≤ (extraCountRect (M 0) (M 2) a b : ℝ≥0∞)/2 +
>   ofReal(lambdaCore (MprimeRect M a b))` for `M : Fin 3 → ℕ`, under `a ≤ M0`, `a+b ≤ M1`, `b ≤ M2`,
>   with `extraCountRect M0 M2 a b := a·M2 + b·M0 − a·b` (CROSS-paired) and
>   `MprimeRect M a b := ![M0−a, M1−a−b, M2−b]`.
> - **Proved.** Unconditionally over the honest-subtraction constraints. The `M'`-minimiser maps under
>   the ℤ telescope `Mval_MprimeRect_add_extra_eq` (shift `s = a`) to an admissible `M`-exponent
>   (`cand_mem_Adm_rect`) dominating the `M`-infimum.
> - **Soundness (cross vs straight, decorrelated).** Two p&p seats + Codex, 0 violations box 16: the
>   CROSS-paired `a·M2 + b·M0 − ab` is the ONLY extra making the inequality hold off `M0 = M2`; the
>   straight-paired `a·M0 + b·M2 − ab` FAILS on a realizable family. Square specialization
>   `extraCountRect m m a b = extraCount m a b` (regression-checked). Non-vacuity: `(5,6,3,2,1)` gives
>   `7 ≤ 9/2 + 5/2 = 7` (tight — exactly calibrated).
> - **Cited.** none. **Status.** sorry-free, clean-three.

---

> **The rectangular case-(B) `hCore` (item 2 rect + the second peel).**
>
> - **Lean:** `DLNFibre.DLN.RLCT.hCoreRect_of_slice_data`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1RectSecondPeel.lean`)
> - **Gloss.** For `M : Fin 3 → ℕ`, `a ≤ M0`, `a+b ≤ M1`, `b ≤ M2`: from the first-peel slice residual
>   `h` `C²` (`hh`) vanishing at `t0` (`hh0`), the second-peel Jacobian RANK bound
>   `extraCountRect (M 0) (M 2) a b ≤ (jacResid h t0).rank` (`hrank₂`), and the R1 interface at
>   `M' = MprimeRect M a b` (`hInterface`, on the BUILT second-peel residual), concludes
>   `ofReal(lambdaCore M) ≤ rlctAtOn (∑ h i²) t0`.
> - **Proved.** The second peel is BUILT (`exists_secondPeel_minor` from `hrank₂` +
>   `secondPeel_hchart_residual`); value close is the rectangular arithmetic + the banked
>   `rlct_quasiSplit_ge`. The `extra/2` gap is supplied by the quasi-split ENGINE, not `hInterface`
>   (⟹ not circular).
> - **Assumed (named-open gates).** `hrank₂`, `hInterface` (the genuine per-`v` content). **Status.**
>   sorry-free, clean-three.

---

> **The two-peel D1 `≥`-leg at a general optimal `v` (the `hDom` reduction).**
>
> - **Lean:** `DLNFibre.DLN.RLCT.d1ge_L2_rect_two_peel`
>   (`lean/DLNFibre/DLN/RLCT/Validate/D1RectHDomProducer.lean`)
> - **Gloss.** At `v` optimal (`prod H v = B`, `rank B = r`), `H : Fin 3 → ℕ`, with the deepest-side
>   value `hDeepest` (Route-A form, `coreDeepest = ofReal(lambdaCore (H − r))`), the middle-stratum
>   layer-rank data `(a, b)` (`a ≤ H0−r`, `a+b ≤ H1−r`, `b ≤ H2−r`), and the THREE per-`v` gates
>   `hrank₂` (second-peel Jacobian rank bound at cross-paired `extraCountRect (H0−r) (H2−r) a b`),
>   `hRne` (slice non-vanishing), `hInterface` (R1 at `M' = MprimeRect (H−r) a b`), concludes
>   `rlctAt deepest ≤ rlctAt v`.
> - **Proved.** The reduction, threading the item-5 C² first peel (built inside) + the rect `hCore` +
>   `deepest_le_of_optimal_via_L2_ge`. The three gates are fed the chart's OWN facts as antecedents
>   (the established non-laundering `∀`-over-residuals idiom, cf. `hDom` in `D1L2ProducerReduction`);
>   satisfiability of all three antecedents is witnessed inside by `dln_hchart_residual_c2` (⟹ not
>   vacuous). Reviewer + Codex: genuine reduction, none of the three gates a disguised wall or a
>   restatement of the conclusion.
> - **Assumed (named-open gates — the genuine residual, NOT laundered).**
>   1. `hrank₂` — the second-peel Jacobian rank bound. The DLN excess IS the cross-paired count
>      (`rank D = (r+b)H0 + (r+a)H2 − (r+a)(r+b)`, H1-independent, decorrelated-certified); the OPEN
>      part is tying that excess to the BUMP-globalised residual's Jacobian via the chart-unwind.
>   2. `hInterface` — R1 at the rectangular `M'`. R1's VALUE is banked (`r1ResolutionInterface_L2`);
>      the OPEN part is the R₂-to-`M'`-core identification (the second-peel residual IS the `M'`-core).
>   3. the `(a, b)` middle-stratum extraction at a general `v` (`a = rank(layer1) − r`, etc.).
> - **CONTENT-BEARING only at a genuine middle stratum** (`extra > 0`); `a = b = 0` is sound-but-vacuous
>   (caveat co-located in the docstring).
> - **Cited.** none (R1 threaded as `hInterface`). **Status.** sorry-free, clean-three.

---

## What remains for the FULL LEAF-2 close (the precise residual — NOT laundered)

The three named gates of `d1ge_L2_rect_two_peel` are the genuine per-`v` middle-stratum residual —
confirming the prior triply-corroborated UPDATE-607 finding (the full `∀ v` LEAF 2 is NOT wireable from
the current bank). What this thread ADDED, decorrelated-certified:
- item (5) CLOSED in Lean (the flagged risk is a stated-ceiling, now discharged);
- item (2) the rectangular value arithmetic CLOSED at the correct CROSS-paired extra;
- the SOUNDNESS of the whole reduction: the value extra and the DLN Jacobian excess are BOTH the
  cross-paired `a·(H2−r) + b·(H0−r) − ab`, and they AGREE ⟹ the `rlct ≤ extra/2 + core` step closes
  unconditionally (no sign condition), removing the live confound the straight-pairing would have hidden.

The remaining debt is the geometry: `hrank₂` (chart-unwind rank bound), `hInterface` (R₂-to-`M'`-core),
and the `(a,b)` extraction at general `v` — the tracked analytic content, unchanged in scope from the
prior hand but now sitting on a validated C² two-peel chain with certified value arithmetic.

LEAF 2 (`HeadlineL2Assembly.lean:107`) was NOT touched (its sorry stands; closing it needs the three
gates). `Skeleton.lean` general-L sorries untouched.
