# §-note: the faithful Lean harness — STOP-ON-SUSPECT (baked canonNormalizationOf not boost-ready)

**What this is.** The pre-stage harness for the re-bake acceptance battery (team-lead sanctioned): compute
the fold from the ACTUAL baked Lean defs (`canonNormalizationOf`/`readEntry`/`blockEntryFlat`,
`MonumentAtlas.lean:832–882`), transcribed verbatim — NOT a hand model — to close pnp-transport's standing
epistemic caveat (hand model vs baked defs). Script: `verify/faithful_lean_harness.py` (exact sympy, exit 0).

**It surfaced a concrete discrepancy between the baked `canonNormalizationOf` and the full clear my
`npivot-certificate` §1 specified — a factor-of-2 double-count. Flagged for seat-L4D (def-side owner) /
the elder (frame-pin); NOT declared a bug, because the running-chart-frame b-chain design (fork B) may be
the intended handling — see the FRAME CAVEAT below.**

**FRAME CAVEAT (read first — it bounds the claim).** Boost-readiness in the ORIGINAL flat coords `u` does
NOT hold for ANY shear: `canonShearOf` gives the `F=x+yz` term `u₀₁₀·(extra)` (coeff 1), and even the full
clear (`honest_clear`), re-expressed in `u`, is coeff 1 — because the recoord `w₁₀₀ = u₁₀₀ + u₀₁₀·u₁₀₁` is
a coordinate change, and `honest_clear`'s boost-readiness was measured in the recoordinatized (running-chart)
frame `w`, not `u`. The elder's "vanishing locus = the Schur pivot in the running chart frame" is exactly
this. So "not boost-ready in original `u`" is EXPECTED, not the finding. **The finding is the factor of 2**
(below): the recoord leaves an extra defect even in the running-chart frame `w`.

## What the baked def does (transcribed, confirmed against the source)
`canonNormalizationOf d s p` (pivot `p` decodes to row `a`, col `b`) writes two supports:
- **(i)** layer-`s.layer` interior, guarded `row ≠ a ∧ col ≠ b ∧ cleared ≤ row ∧ cleared ≤ col`:
  `−w_{row,b}·w_{a,col}` (the Schur cross-term).
- **(ii)** layer-`(s.layer+1)`, col `= a`: the deeper recoord `A_{S+1}·Q₁⁻¹ − A_{S+1} = ∑_{i≠a} w_{i,b}·A_{row,i}`.

**The recoord direction is confirmed** (resolving my standing uncertainty): (ii) writes layer-`(S+1)` col `= a`
(the pivot ROW), `A_1 col-a += ∑_{i≠a} w_{i,b}·(col i)` — exactly `honest_clear`. So all my PRIOR findings
(boost-readiness of `honest_clear`, cap-escape, hedge) stand against the actual def.

## The defect (isolated to `ed1` alone; hand-verified)
On `(2,2,2,2)`, `foldResid` at the case11 boost parent has (slot 0):

    resid[0] = u₁₀₀·u₂₀₀ + u₁₁₀·u₂₀₁  +  2·u₀₁₀·u₁₀₁·u₂₀₀ + 2·u₀₁₀·u₁₁₁·u₂₀₁

The extra-block coord `u₁₀₁` appears with coefficient `2·u₀₁₀·u₂₀₀` — the `F=x+yz` defect coord `u₀₁₀`
(NOT the pivot `u₀₁₁`), and with coefficient **2**. Boost-readiness `A1/A2/A3 = (False, False, False)`.

**Mechanism.** The `ed1` recoord (ii) sets `A_1[0][0] = u₁₀₀ + u₀₁₀·u₁₀₁`. But `A_0[1][0] = u₀₁₀` (the pivot
COLUMN) is NOT cleared — guard (i) `col ≠ b` excludes it. So `(A_1·A_0)[0][0] = (u₁₀₀+u₀₁₀·u₁₀₁)·1 +
u₁₀₁·u₀₁₀ = u₁₀₀ + 2·u₀₁₀·u₁₀₁`. Aoyagi's clear is `A_1·A_0 = (A_1·Q₁⁻¹)·(Q₁·A_0)`: the recoord `A_1·Q₁⁻¹`
must be PAIRED with `Q₁·A_0` (which clears `A_0`'s pivot column) so the two CANCEL. The baked def applies the
recoord WITHOUT the `A_0`-clearing, so instead of cancelling they **DOUBLE** — coeff 2 (`canonShearOf`, with
no recoord at all, gives coeff 1).

## This is a genuine omission, not a modelling artifact
- **Aoyagi requires the clearing.** worked.tex:453: `Q''_1 = [[E,O],[−∏C·A'_3·(C'_1A'_1)⁻¹, E]]` "to clear
  the bottom-left" — the pivot-column clearing IS an explicit step of the faithful clear.
- **My `npivot-certificate` §1 specified it:** "`N_p` = Q₁ clears the pivot column `b` (row-op), Q₂ clears
  the pivot row `a` (col-op), giving block = `u·(pivot→1, row/col→0, Schur)` + deeper recoord." The
  **`row/col→0` (pivot-row/column clearing) was DROPPED in the render**: baked (i) writes only the interior
  Schur (`row≠a ∧ col≠b`), never the pivot row (`row=a`) or column (`col=b`).
- **The recoord makes it strictly worse.** `canonShearOf` (Schur interior only, no recoord): coeff 1 (the
  honest `F=x+yz`, needing the carried b-chain). Baked `canonNormalizationOf` (recoord, no `A_0`-clearing):
  coeff 2 (the recoord doubles the defect). `honest_clear` (full clear + recoord): boost-ready. So the recoord
  is only correct WHEN PAIRED with the `A_0`-clearing.

## The factor of 2 SURVIVES the running-chart frame (the actual finding)
Re-express the baked residual in the running-chart frame `w₁₀₀ = u₁₀₀ + u₀₁₀·u₁₀₁` (`u₁₀₀ = w₁₀₀ −
u₀₁₀·u₁₀₁`): the baked `(A_1·A_0)[0][0] = u₁₀₀ + 2·u₀₁₀·u₁₀₁ = w₁₀₀ + u₀₁₀·u₁₀₁` — a **coeff-1 leftover
`u₀₁₀·u₁₀₁`** in the `w`-frame. The full clear (`honest_clear`) gives exactly `w₁₀₀` — **coeff 0**, clean.
So in the running-chart frame: full clear → 0 (boost-ready), baked recoord → 1 (an extra `u₀₁₀·u₁₀₁`, where
the extra-block `u₁₀₁` carries `u₀₁₀`, NOT the pivot — so `BoostSplit` fails in EITHER frame). The recoord
`A_1·Q₁⁻¹` needs the paired `Q₁·A_0` (pivot-column clearing) to cancel; the bake omits the pairing, leaving
the leftover.

## Consequences (for seat-L4D / arch-C / the elder's ruling)
1. **The case11 boost split appears NOT reachable from the current baked `foldResid` in EITHER frame** (the
   recoord leaves a `u₀₁₀·u₁₀₁` leftover carrying the wrong factor). This is a discrepancy from the full
   clear my certificate §1 specified (`Q₁ clears the pivot column`), NOT from `canonShearOf`'s known
   deficiency. Seat-L4D owns the def-level confirmation — I flag it, not declare it.
2. **The fix is to restore the pivot-row/column clearing** in `canonNormalizationOf` (extend (i) to the pivot
   cross `col=b` / `row=a`), so the recoord's `A_1·Q₁⁻¹` is paired with `Q₁·A_0`. CAVEAT (a real subtlety, not
   adjudicated here): the flat-fold order is `blockBlowupCoordQuot ∘ edgeShear` (shear BEFORE the quotient
   sets pivot→1), and Aoyagi's `γ = A_0[row][b]/A_0[a][b]` needs the pivot inverted / normalized — so the
   pivot-column clearing may not be cleanly a pre-quotient shear displacement. Whether it is representable, or
   whether the fold order/model needs rethinking, is seat-L4D's def-level call.
3. **Bearing on the ruling's fork.** If the fold's recoord cannot cleanly realize the paired clear, then
   boost-readiness cannot come from the FOLD and MUST be carried by the invariant (fork B, the path-inductive
   b-chain) — with the caveat that the invariant carries what is TRUE, and boost-readiness is only true once
   the `A_0`-clearing is in the fold. So this finding is decision-relevant to whether fork B is even reachable
   on the current defs.

## Epistemic note
Exact sympy, verbatim transcription of the baked def, defect isolated to `ed1` alone and hand-verified
(`(A_1·A_0)[0][0] = u₁₀₀ + 2u₀₁₀u₁₀₁`). This is a big claim (the bake, rendered from my own certificate, is
not boost-ready) — I flag it for **seat-L4D confirmation at the def level** (the owner of the def-side). But
the evidence is a clean, reproducible factor-of-2 double-count, and it matches the known `honest_clear`-vs-
`canonShearOf` triangle (0 / 1 / 2 defect coefficients for full-clear / no-recoord / recoord-without-clear).
