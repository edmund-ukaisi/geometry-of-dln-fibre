import DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridgeL2

/-!
# The hLDUtie readback-tie (standalone, the producer's named "UNBUILT Rcore ↔ deepestCoreF" bridge)

This file isolates the ONE genuinely-delicate L=2 sub-4 residual — the matrix readback-tie
`hLDUtie` that `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` (sub-4) consumes — as a single
standalone `sorry`, so it can be filled in isolation without colliding with the rest of the L2 wiring.

## The statement

`prod_deepestM_eq_schur_ldu_readback` says: the reduced two-layer core product
`prod (deepestM H r) C` over the CLEANED absorbed-core tuple `C` (the per-layer Schur cores
`decode(q) + schurCorrection(q)`, last-layer overridden to `(1 − l2K)·l2S1`) equals the Score
`(1,1)`-Schur integrand `Rcore` over the framed reindexed product
`endpointP0 · (prod(decode x) − B) · endpointQL` with pivot `(·₁₁ + 1)⁻¹`.

## ⚠ FIDELITY FINDING (2026-06-28, genm-l2wire — BEFORE filling, READ THIS)

The tie as stated below is **NUMERICALLY FALSE for the BARE-read `l2*` dictionary** (triple-confirmed:
my numerics, two decorrelated Codex consults, the Lean defs). Concretely (r=1, H=[2,2,2], deepest
leading block `A11 = 3 ≠ 1`): the LHS `prod(deepestM) C` = `frobSq(S0·(1−K)·S1)` with `l2A_s = 1 + readX_s`
evaluates to `0.0942`, while the RHS framed-Score Schur evaluates to `0.0741` — because the framed Schur
(by `schur_frame_transform`, `DP = DQ = 1`) = `Schur(reindex prod(decode x))`, whose layer-0 `(1,1)`-block
is `A11 + readX_0`, **not** `1 + readX_0`. They agree ONLY when the deepest boundary layer is pure `corM`
(`A11 = 1 ∧ A21 = 0`).

So this statement needs a FIX before it can be proven sorry-free — one of:
* **(3a) frame-conjugated reads**: the absorbed-core dictionary (`schurCorrection` / `l2A_s`) must read
  off the FRAMED layer `endpointP0 · decode · endpointQL` (so `1 + readX_s` becomes the framed `(1,1)`),
  a change to the producer's core definition that ripples the S4 derivative work; OR
* **re-state the Score** to be the bare-read core Schur (but then `Score ≠` the loss's `Sreg`-coupled
  Schur, breaking the loss-identity downstream).

The discriminator + the two Codex consults are banked at
`expeditions/2026-06-20-aoyagi-full/threads/{31-pin2-comparability,l2fill}/codex/`. Do NOT fill this with
a green-but-wrong proof — the boundary `A11 ≠ 1` is real. The signature is committed so the fix can be
scoped against a concrete contract; the body stays `sorry` with this finding until the dictionary
question is adjudicated.

The reusable algebraic pieces (sorry-free, landed): `framedSchur_eq_unframedSchur_L2` (the frame-strip,
`DP = DQ = 1`), `reindex_decodeDev_eq_fromBlocks_reads` (the per-layer readback foundation),
`rcore_schur_factor_of_corner_split` / `rcore_eq_schur_of_corner_split` (the corner split + two-factor
LDU), `prod_deepestM_eq_two_of_L2` (the L=2 two-factor unfold), `prod_absorbed_eq_schur_ldu` (the block
LDU). They compose to the CORRECTED bridge once the dictionary is frame-conjugated.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The hLDUtie readback-tie** (standalone, sub-4's matrix-equality residual). The reduced two-layer
core product over the cleaned absorbed-core tuple equals the Score `(1,1)`-Schur integrand over the
framed reindexed product. **STATEMENT IS CURRENTLY MIS-DICTIONARIED** — see the fidelity finding in this
file's module docstring; the fix (frame-conjugated reads) is pending adjudication. The body is `sorry`
pending that fix; `deepestCoreF_coreAbsorb_psiSplitRawL2_eq_score` (sub-4) consumes this exact shape. -/
theorem prod_deepestM_eq_schur_ldu_readback (H : Fin (L + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) (hL2 : L = 2)
    (J : Fin r ↪ Fin (H (Fin.last L)))
    (Pf : (s : Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ)
    (Qf : (s : Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ)
    (hPtri : (Matrix.reindex (rThresholdSplit r (H 0) (hr 0)) (rThresholdSplit r (H 0) (hr 0))
        (endpointP0 H hL Pf)).toBlocks₁₂ = 0)
    (hQtri : (Matrix.reindex (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
        (endpointQL H hL Qf)).toBlocks₂₁ = 0)
    -- (The frames' IDENTITY ₂₂-blocks `DP = DQ = 1`, which the frame-strip needs, are DERIVABLE inside
    -- from the explicit normalizers — the filler re-derives them rather than taking them as inputs, to
    -- keep this signature exactly what the sub-4 call site supplies cleanly.)
    (x : Fin (flatDim H) → ℝ)
    (q : DeepestSplit H r (deepestNGauge H r))
    (hq : q = deepestSplit H r hr hL ((paramsEquivFlat H) (deepestPoint H r B hB hr hL)) x)
    (hWdet : (l2W H r hr hL hL2 q).det ≠ 0) :
    prod (deepestM H r)
        (Function.update
          (fun s => (paramsEquivFlat (deepestM H r)).symm q.2.1 s
            + schurCorrection H r hr hL (q.1, q.2.2) s)
          (lastLayer hL)
          ((1 - l2K H r hr hL hL2 q) * l2S1 H r hr hL hL2 q))
      = Matrix.of (fun i j => ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
            (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
            (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
              * endpointQL H hL Qf)).toBlocks₂₂
          - (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
              (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
              (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                * endpointQL H hL Qf)).toBlocks₂₁
            * ((Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₁ + 1)⁻¹
            * (Matrix.reindex (rThresholdSplit r (H 0) (hr 0))
                (pivotThresholdSplit r (H (Fin.last L)) (hr (Fin.last L)) J)
                (endpointP0 H hL Pf * (prod H ((paramsEquivFlat H).symm x) - B)
                  * endpointQL H hL Qf)).toBlocks₁₂) i j) := by
  -- ⚠ MIS-DICTIONARIED — FALSE for the bare-read `l2*` dictionary (boundary `A11 ≠ 1`); see the module
  -- docstring + the banked Codex/discriminator artefacts. Awaiting the frame-conjugated-read fix.
  sorry

end DLNFibre.DLN.RLCT
