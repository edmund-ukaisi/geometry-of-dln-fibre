# §-note: recoord adjudication — N_p ratified claims re-verified on the BAKED def (compute half)

Elder §7 gate (compute half; seat-L4D adjudicates). Re-verify the N_p bake's three ratified claims on the
BAKED `canonNormalizationOf` (the unpaired recoord). Script: `verify/recoord_adjudication.py` (exit 0).
Witnesses: `(2,2,2,2)` ed1 (isolated) + `(2,3,2,2)` (wide).

## Bottom line: the blast radius is CONTAINED to the STRUCTURAL clean-form claims (field + monomialisation).
The RLCT-value/variety and `M_{s,k}` are SAFE; the field boost-readiness and the clean-block monomialisation
FAIL — both from the SAME missing `A_0` pivot-column clearing (def-edit-3). One fix restores both.

> **CORRECTION (see `recoord-ideal-matched-note.md`).** The `(1b)` Gröbner comparison below is
> NODE-MISMATCHED (baked = 3 edges vs `honest_residual` = 1 edge), so its "both inclusions FALSE" is
> not clean. The matched-node comparison (same node, common ring, `verify/recoord_ideal_matched.py`)
> supersedes it: `⟨baked⟩ ≠ ⟨faithful⟩` holds cleanly (difference = the `u₀₁₀` pivot-column leakage), AND
> the radicals differ — but the baked step still PRESERVES the RLCT of the original (every shear is
> globally invertible, not merely det-1), so it is VALID-BUT-DIFFERENT, not broken. `(1a)`, `(2)`, `(3)`
> below stand.

## (1) IDEAL-PRESERVATION — HOLDS at the variety level; the ratified generator-ideal differs (frame)
- **(1a) The baked shear `ψ = u + canonNormalizationOf` is UNIPOTENT** — `det Jacobian ≡ 1`, `J(0) = I`,
  verified on `(2,2,2,2)` and `(2,3,2,2)`. So the step is an INVERTIBLE coordinate change (composed with the
  blow-up strict-transform), hence it PRESERVES the variety of `⟨∏C⟩`. The StepInv's ideal content — the
  RLCT-relevant zero-locus — is preserved. **The unpaired recoord does NOT break the resolution's validity.**
- **(1b) Gröbner: `⟨baked child residual⟩ ≠ ⟨honest paired-clear residual⟩`** (both inclusions FALSE, `(2,2,2,2)`
  case11 parent). This is NOT a variety break: baked and honest differ by the invertible `A_0`-clear `Q₁,U`
  (the honest clears the pivot row/col; the baked leaves them), so they are DIFFERENT coordinate presentations
  of the SAME variety (variety-isomorphic via `Q₁,U`). The literal generator-ideal differs because `Q₁,U` do
  not fix the ideal — the baked residual carries the uncleared off-diagonals `u₀₀₁,u₀₁₀`. So the RATIFIED
  clean generator structure (Aoyagi's `diag(b)`) is NOT the baked residual's structure, but the VARIETY (and
  thus the RLCT) is preserved. (F4 note: Gröbner ideal-equality run, not coefficient-matching; the inequality
  is the generator-frame difference, the unipotency is the variety-preservation certificate.)

## (2) MONOMIALISATION — FAILS on the baked def (report-immediately item)
The ratified claim (npivot §4a): the cleared block reduces to `u·[[1,O],[O,D']]` (clean diagonal, off the
pivot cross). On the baked def, ed1's cleared layer-0 block is

    [[1, β],[γ, δ−γβ]]   (β = u₀₀₁, γ = u₀₁₀, δ−γβ = the Schur e₂)

— the Schur `(1,1)` entry is formed, but the pivot row/column off-diagonals `β,γ` are NOT cleared (guard (i)
`row≠a ∧ col≠b` EXCLUDES the pivot cross). So the block is `[[1,β],[γ,e₂]]`, NOT the clean `[[1,O],[O,e₂]]`.
The clean form is reachable only via the additional `Q₁,U` (= def-edit-3). So **`canonNormalizationOf` as
baked does NOT produce the monomialised (clean-diagonal) block** — same root cause as the field failure.
(The honest paired clear gives `diag(1,e₂)`, the clean form.)

## (3) M_{s,k} — HOLDS
The baked shear is det-1 (1a), so it adds NOTHING to the `blockBlowupMap` Jacobian `u^{|center|−1}`. The
exceptional coordinate's exponent `M_{s,k}=|center|` is unchanged (the exponent ledger is shear-independent).

## Synthesis for seat-L4D's adjudication + the elder
- **SAFE (variety-level):** ideal-preservation `(1a)` / RLCT-value, and `M_{s,k}` `(3)`. The recoord defect
  is a coordinate-change-level structural issue, NOT a variety/value break — so the payoff-value path is not
  at risk from this gap.
- **FAILS (structural clean-form):** the FIELD (boost-readiness, `c_i = e₂·β`, the earlier battery) and
  MONOMIALISATION (clean-diagonal block) — BOTH from the one missing `A_0` pivot-column clearing.
- **`⟨baked⟩ ≠ ⟨honest⟩` (1b):** the baked and honest are different (variety-isomorphic) presentations; the
  RATIFIED Aoyagi `diag(b)`/b-chain generator structure is the HONEST one, not the baked one.

**Prediction for def-edit-3 (the completed candidate, when seat-L4D specifies it):** adding the `A_0`
pivot-column clearing (`Q₁`) + pivot-row clearing (`U`) to `canonNormalizationOf` restores the clean block
`diag(1,e₂)`, makes `⟨completed⟩ = ⟨honest⟩` (Gröbner ideal-equal), and makes the field hold (`c_i = e₂·β`).
I re-run all three on the completed candidate — they must come back GREEN (the fidelity-restoration cert).

## Epistemic note
Exact sympy + Gröbner (grevlex). Unipotency `det J ≡ 1` is a certificate (variety-preservation). The Gröbner
`⟨baked⟩≠⟨honest⟩` is a computed fact whose INTERPRETATION (frame difference, not variety break) rests on the
unipotency + the `Q₁,U`-relation of baked and honest; seat-L4D owns the def-level adjudication (including
diffing my `canonNormalizationOf` transcription, `verify/recoord_adjudication.py:22-33`, against `:867-882`).
