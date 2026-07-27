# Statement cards — `aoyagi-engine` close (the `(3,3,4)` landing)

Three cards, one per landed theorem: the EQUALITY, the V-LOWER, the V-UPPER. All pinned to branch
`expedition/aoyagi-r2ov-integration` @ `4399f4c7a`. Throughout, `dvec = ![3,3,4]`
(`Corank2CoreGenWrap.lean:39`); `0` is the zero matrix `Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ`.

All three are gated **clean-three** — `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`, no `@[cited]` axiom — by `#assert_banked_clean_batch` in `DLN/RLCT/AxCheck.lean` (a forced
`collectAxioms` over each registered root, so this is kernel truth, not a docstring claim).

---

## Card 1 — the `(3,3,4)` `rlct = ½·codim` EQUALITY (cite-free)

> **Claim.** For the deep-linear-network dimension vector `d = (3,3,4)` at the base point `B = 0`, the
> RLCT of the square-Frobenius loss equals half the codimension of its real zero-product fibre:
> `rlct = ½·codim = 4`. No cited bound, no resolution monument.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.dln_rlct334_eq_half_codim`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2Equality334.lean` @ `4399f4c7a`)
>   ```
>   theorem dln_rlct334_eq_half_codim :
>       RLCT.Global.rlctGlobal (lossDLN dvec 0)
>         = ((codimRealFibre dvec 0).toNat : ℝ) / 2
>   ```
>   Companions in the same file: `dln_rlct334_eq_four` (`… = 4`) and, in `Corank2Equality334`,
>   `rlctAt_coreGen334_eq_four` (the core loss `= 4`).
> - **Gloss.** The global RLCT of the DLN square-Frobenius loss `lossDLN ![3,3,4] 0` equals
>   `(codimRealFibre ![3,3,4] 0).toNat / 2`. The geometric codimension is `8`
>   (`codimRealFibre_334_zero_toNat`, from `minAdm ![3,3,4] = 8` via the banked `minAdm_eq_cCodim` and the
>   base-change transfer), so the value is `4`.
> - **Proved.** The full equality, `le_antisymm` of Card 3 (the cite-free single-chart upper, unconditional
>   after `measurePreserving_eWrap`) and Card 2 (the geometric V-lower), plus the codimension evaluation
>   `= 8`. Both halves are built geometry.
> - **Assumed.** None (the `MeasurePreserving eWrap` hypothesis of the conditional upper is discharged
>   in-cone by `measurePreserving_eWrap`).
> - **Cited.** None. The Watanabe universal upper is REPLACED by a built single-chart change-of-variables
>   (`cited_watanabe_upper_ax` is not in the cone); the Aoyagi exact value is replaced by the geometric
>   V-lower. Verified by the clean-three batch gate.
> - **Deferred.** The general-`d` equality. This card is `d = (3,3,4)`, `B = 0` only — one coupled
>   instance (`minAdm = 8` is coupled-only). The general resolution `exists_coreResolution` is NOT
>   consumed here and remains `sorryAx` elsewhere.
> - **Does NOT claim.** Not the general-`d` headline; not that Object B (the coupled resolution) is built
>   at full generality; not `aoyagi_learning_coefficient` (the general-name payoff) cite-free-and-sorry-free
>   — that still carries the `exists_coreResolution` `sorryAx`.
> - **Status.** sorry-free + clean-three (kernel-gated) + reviewed (whole-cone + equality fidelity reviews
>   SURVIVED, Codex-corroborated, independent `codim = 8`).

---

## Card 2 — the `(3,3,4)` DLN square-Frobenius V-LOWER (`rlct ≥ 4`, cite-free)

> **Claim.** The RLCT of the `(3,3,4)`, `B = 0` DLN square-Frobenius loss is `≥ 4`, from the built
> geometry (the whole-conjugate folded fan), unconditional and cite-free.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.dln_rlct334_ge_four`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2DLNRlct334.lean` @ `4399f4c7a`)
>   ```
>   theorem dln_rlct334_ge_four :
>       (4 : ℝ) ≤ RLCT.Global.rlctGlobal (lossDLN dvec 0)
>   ```
>   Core-loss form (the mathematical content): `OverVanishHeadline334.rlctAt_coreGen334_ge_four`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2OverVanishHeadline334.lean`)
>   ```
>   theorem rlctAt_coreGen334_ge_four :
>       (4 : ℝ) ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ)
>   ```
> - **Gloss.** `4 ≤ rlctGlobal (lossDLN ![3,3,4] 0)`. The deepest-point + measure-preserving-flatten
>   reduction `coreReduction` (fed `measurePreserving_eWrap` + `eWrap_zero`) identifies the DLN loss RLCT
>   with the core-loss RLCT `rlctAt (∑(coreGen ![3,3,4] eWrap)ᵢ²) 0`, which the folded-fan headline caps
>   below by `4`.
> - **Proved.** Unconditionally, `4 ≤` the DLN loss RLCT. The core headline applies the mechanism-agnostic
>   membership spine `rlctAt_coreGen334_ge_four_of_perchart_integrable` to the 288-chart folded family
>   `gFold` (whole-conjugate born-native fan covering a neighbourhood of `0`); per chart the weighted
>   pulled-back loss is integrable for every exponent `< 4` (clean-144 via the single-entry survivor + the
>   divisibility-chain engine → `≥ 9/2`; over-vanishing-144 via the SoS/Tonelli product engine → `= 4`).
> - **Assumed.** None (`measurePreserving_eWrap` discharged in-cone).
> - **Cited.** None (replaces the Aoyagi exact-value cite). Clean-three batch-verified.
> - **Deferred.** The general-`d` V-lower. The over-vanishing sum-of-squares mechanism generalises
>   (compass F10/F13) but is inferred, not built — gated behind the composition + α-uniformity probes.
> - **Does NOT claim.** Not a two-sided principal normal form (the lower bound needs only the from-below
>   sandwich with a kept survivor `R(0) = 1`, NOT the two-sided principality); not general-`d`.
> - **Structure & ideas observed.** The `r/2` term at the over-vanishing leaves lives entirely in the
>   nondegenerate sum-of-squares block, disjoint from the monomial support — invisible to the chain
>   engine. This is the reusable insight banked as `Core.Aoyagi.MonomialSumSqRLCT`.
> - **Status.** sorry-free + clean-three (kernel-gated) + reviewed (whole-cone fidelity SURVIVED).

---

## Card 3 — the `(3,3,4)` V-UPPER (`rlct ≤ ½·codim`, single-chart, cite-free)

> **Claim.** The RLCT of the `(3,3,4)`, `B = 0` DLN square-Frobenius loss is `≤ ½·codim = 4`, from ONE
> certified change-of-variables chart — the Watanabe universal upper for the built object, without the
> cited bound.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.dln_rlct334_le_half_codim`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2Equality334.lean` @ `4399f4c7a`)
>   ```
>   theorem dln_rlct334_le_half_codim :
>       RLCT.Global.rlctGlobal (lossDLN dvec 0)
>         ≤ ((codimRealFibre dvec 0).toNat : ℝ) / 2
>   ```
>   Core-loss form: `rlctAt_coreGen334_le_four`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2UpperBound334.lean`)
>   ```
>   theorem rlctAt_coreGen334_le_four :
>       rlctAt (sumSqFam (coreGen dvec eWrap)) (0 : Fin 21 → ℝ) ≤ 4
>   ```
>   General single-chart lemma (same file, reusable): `rlctAt_sumSqFam_le_chartMin_half` —
>   `rlctAt (∑Fᵢ²) x₀ ≤ c.chartMin / 2` from any one `Chart F x₀`.
> - **Gloss.** `rlctGlobal (lossDLN ![3,3,4] 0) ≤ (codimRealFibre ![3,3,4] 0).toNat / 2 = 4`. The
>   conditional single-chart upper `rlctGlobal_lossDLN_334_zero_le_half_codimRealFibre` (`Corank2CiteFree334`)
>   with its sole `MeasurePreserving eWrap` hypothesis discharged by `measurePreserving_eWrap`. One chart
>   `chart334`: `rlctAt ≤ chartMin/2`, and `chartMin ≤ jac E + 1 = 8`.
> - **Proved.** Unconditionally, `rlctGlobal ≤ 4`. The elementary CoV direction (per-chart change of
>   variables) needs only ONE certified `Chart` — no atlas, no cover, no `θ`.
> - **Assumed.** None (`measurePreserving_eWrap` discharged in-cone).
> - **Cited.** None. This is the cite-free REPLACEMENT for `cited_watanabe_upper_ax` at this instance
>   (the Watanabe universal bound, proved for the built object from a single chart). Clean-three
>   batch-verified.
> - **Deferred.** The general-`d` upper via the full resolution atlas is not here; a single chart suffices
>   for the upper direction (the lower direction genuinely needs the whole-neighbourhood cover — Card 2).
> - **Does NOT claim.** Not the resolution atlas; not general-`d`. The forward-only variant
>   `rlctAt_coreGen334_le_four_forward` additionally witnesses that the upper needs only `chart334`'s
>   FORWARD ideal inclusion (not the reverse principality), so V-upper lifts to general `d` on the forward
>   atom alone — recorded as an observation, not a general-`d` claim.
> - **Status.** sorry-free + clean-three (kernel-gated) + reviewed (`Q2` single-chart CoV soundness +
>   `Q3` no-overclaim checks passed; whole-cone fidelity SURVIVED).

---

### Supporting landed facts (not separate cards, cited above)

- `measurePreserving_eWrap` (`Corank2EwrapMeasure.lean`) — `MeasurePreserving eWrap (volume → volume)`;
  the transpose flatten is a coordinate permutation (`piSymm`, `Bijective` by `decide`); route B avoids the
  opaque `Fintype.equivFin`. Discharges the sole un-banked reduction input; clean-three.
- `codimRealFibre_334_zero_toNat` (`Corank2CiteFree334.lean`) — `(codimRealFibre ![3,3,4] 0).toNat = 8`,
  field-independent `C = 8`, via `minAdm ![3,3,4] = 8` (`decide`) + `minAdm_eq_cCodim` + the base-change
  transfer.
- `Core.Aoyagi.MonomialSumSqRLCT.monoSumSq_integrableAtFilter_of_lt` (`Core/Aoyagi/MonomialSumSqRLCT.lean`)
  — the reusable network-free SoS/Tonelli product-RLCT engine that supplies the over-vanishing leaves'
  `r/2` threshold; clean-three.
