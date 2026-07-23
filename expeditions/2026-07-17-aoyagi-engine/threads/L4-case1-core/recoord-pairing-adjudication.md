# Recoord-pairing adjudication (seat-L4D, def-side) — the 12th catch, in the N_p bake's own def

**Charge (controller):** pnp's faithful harness found the baked `canonNormalizationOf` applies the
deeper recoord (branch ii) UNPAIRED — the layer-S pivot-column clear is missing. Adjudicate at the def
(sensor calibration both ways), and if confirmed, specify the fix + impact on the 5 N_p-bake pins.
Verify: `verify/recoord_pairing_adjudication.py` (exact sympy, exit 0).

## VERDICT: CONFIRMED (real defect) — AND the fix breaks hshear (a model-level obstruction)

### 1. Calibration — pnp's transcription is CORRECT (checked against MonumentAtlas:867-882)
`canonNormalizationOf` branch (i) guard is `(q.1.2) ≠ (qp.1.2) ∧ (q.2) ≠ (qp.2)` — i.e. row ≠ a AND
**col ≠ b**, so it genuinely EXCLUDES the pivot column (col = b). Branch (ii) is layer S+1. So the
layer-S pivot column (col = b, row ≠ a) is NOT in the shear's write-set (displacement 0 there). NOT a
mis-transcription — the def omits the column clear.

### 2. Algebra — re-derived independently (sympy), (2,2,2,2) ed1, corner pivot a=b=0
| shear | (A₁·A₀)[0][0] | running-frame (w₁₀₀ = u₁₀₀+u₀₁₀·u₁₀₁) |
|---|---|---|
| BAKED N_p (i + ii, no col clear) | u₁₀₀ + **2**·u₀₁₀·u₁₀₁ | w₁₀₀ + u₀₁₀·u₁₀₁ (leftover) |
| canonShearOf (i only) | u₁₀₀ + u₀₁₀·u₁₀₁ | — |
| FULL clear (i + ii + col clear) | w₁₀₀ | **w₁₀₀ (clean)** |

The unpaired recoord `A₁·Q₁⁻¹` (branch ii) without its pair `Q₁·A₀` (column clear) does not cancel — it
**DOUBLES** the defect (canonShearOf coeff 1 → baked coeff 2). In BOTH frames the extra-block coord u₁₀₁
carries u₀₁₀ (the wrong coord, NOT the pivot), so BoostSplit is FALSE in both. pnp's mechanism + numbers
are exactly right; full `coreGen[0][0]` matches pnp's `resid[0]`.

### 3. The fix obstruction (the load-bearing new finding — def-side call)
The pivot-column clear CANNOT be added as a unipotent shear. To clear A₀'s column-b entry to 0,
`blockShear = u + φ` needs `φ(S,i,b) = −u(S,i,b)` — a SELF-READ. Verified jacDets:
- naive column clear `φ = −u(S,i,b)`: **jacDet = 0** (hshear needs 1).
- extend branch (i)'s formula to col=b (`φ = −u(S,i,b)·u(S,a,b)`): **jacDet = 1 − u₀₀₀** (needs 1).

Any shear that clears a coordinate to 0 is rank-reducing (non-unipotent); no `blockShear` can do it
without breaking `hshear` (`jacDet blockShear = 1`), the shear-pin field the monument rides. So the
faithful clear (needed for running-frame boost-readiness) is NOT representable as a 3rd `canonNormalizationOf`
branch. This is a fold-MODEL fidelity question, not a def edit.

### 4. Options (for controller + elder; + a decorrelated Codex/pen-and-paper pass on the blow-up chart)
- **(R1)** the recoord (branch ii) is the WRONG fix — drop it, revert to `canonShearOf`, and source
  boost-readiness differently. (canonShearOf's extra-block also carries u₀₁₀ not the pivot — must check
  whether u₀₁₀ IS a valid earlier-divisor coord for the case11 reuse, i.e. whether canonShearOf's
  b-chain is the right one after all.)
- **(R2)** the δ=1 blow-up handling (`blockBlowupCoordQuot`: pivot→1, else→value) is INCOMPLETE — the
  strict transform should reparametrize the whole center, which clears the column via the CHART (not a
  shear), realizing Aoyagi's clear at the correct Jacobian. A fold-model change (Core `BlockDivision`).
- **(R3)** a unipotent realization not yet seen.
This questions the N_p bake's fold-model fidelity, and is decision-relevant to whether fork B (the
carried b-chain) is reachable at all (the invariant carries what is TRUE, and running-frame
boost-readiness is only TRUE once the column clear is in the fold).

### 5. Impact on the 5 N_p-bake pins
- **hshear (Jacobian-1): THE blocker** — any column-clear-as-shear violates it (§3). Load-bearing.
- **canonNormalizationOf_support**: STATEMENT changes (a col=b locus added) IF a fix adds it.
- **canonNormalizationOf_apply_interior** (guard row≠a ∧ col≠b): unchanged by a separate branch.
- **realBranch_canonNormalization_eq**: tracks the def by name (projection; proof unchanged).
- **PivotPreservation corner**: a col=b write at a diagonal corner (S,b,b), b≠a, could touch a ledger
  corner — needs a check IF a shear-form fix landed; but §3 says none does cleanly.

**RECOMMENDATION: arch-C HOLD DEF EDIT 2 + any recoord-dependent bake.** Route the R1/R2/R3 model
question to the elder + controller (+ Codex). seat-L4D def-trace + sympy ready to fire the Codex consult
on demand.
