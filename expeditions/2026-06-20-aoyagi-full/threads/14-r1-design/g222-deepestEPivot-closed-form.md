# deepestEPivot closed form — the shared PIN1↔PIN2 coupling object (crux2, #115, 2026-06-23)

**Task #115 (team-lead live front).** cobuild needs the exact closed form of `deepestEPivot`
(`DeepestGaugeConstruction.lean:313`) + its three props (`_contdiff`, `_deriv`, `_base`). Decorrelated:
crux2 derives the exact algebra, cobuild formalises. Grounded on the #91 cert (`dE(0)=(Σ_s X_s, Y_L, Z_1)`,
all coeffs `I_r`) + the g125 deepest-split witness (`d(P−B)|_0 = [[Σ_s X_s, Y_L],[Z_1, 0]]`).

## The object

The deepest layers are block-normal `C^(s) = [[I_r + X_s, Y_s],[Z_s, T_s]]` (the `deepestPoint_exists`
identity-corner form). The gauge-normalised product is `P = C^(1)·C^(2)···C^(L)`, a
`Matrix (Fin (H 0)) (Fin (H (last)))` partitioned `[[P_11, P_12],[P_21, P_22]]` with `P_11 : r×r`,
`P_12 : r×(M^{L+1})`, `P_21 : (M^1)×r`, `P_22` the core block.

`deepestEPivot (reg, gauge)` is the **regular-block residual of `P`** — the map that reconstructs the
layers `C^(s)` from the slots (reg carries the `nReg = r(M^1+M^{L+1}) − r²` boundary generators
`X_s/Y_L/Z_1`; spectator carries the interior `X_s/Y_s/Z_s`, s ∉ boundary), forms `P = ∏_s C^(s)`, and
reads off

    deepestEPivot (reg, gauge) = pack( P_11 − I_r,  P_12,  P_21 ) : Fin (deepestNReg) → ℝ

where `pack` is the `regGaugeSlotEquiv`-style flatten of the three regular blocks into the `nReg` reg
coordinates. The bottom-right `P_22` is the HOMOGENEOUS core — NOT part of `deepestEPivot` (it is
`coreAbsorb`'s domain, the Schur `R` block).

**Answer to the team-lead's question (`∏(I+X_s)−I` vs full E):** it is the THREE-block regular residual
`(P_11−I_r, P_12, P_21)`, NOT just `∏(I+X_s)−I`. The `∏(I+X_s)−I` is the (0,0)-corner PART (`P_11−I_r`'s
leading structure); the full `deepestEPivot` also carries the `P_12` (Y) and `P_21` (Z) boundary blocks.
The full E (the loss residual PIN2's Φ uses) is exactly this regular-block residual — confirmed: it reads
all slots incl the interior X_s (the idempotent sandwich keeps the (0,0) X-sum), so `regStraighten.1 = E`.

## The three props

**`_base` (`deepestEPivot 0 = 0`).** At reg=gauge=0: every `X_s=Y_s=Z_s=T_s=0`, so each
`C^(s) = blockdiag[I_r, 0]`. The idempotent `blockdiag[I_r,0]^L = blockdiag[I_r,0]`, so `P = blockdiag[I_r,0]`:
`P_11 = I_r`, `P_12 = 0`, `P_21 = 0`. Hence `(P_11−I_r, P_12, P_21) = 0`. ✓ The mechanised version is the
`prodAux`-telescoping `prod_framedParamsReg_zero` (the dependent-Fin cast IS the work — recipe below; not
"pure evaluation").

**`_contdiff` (`ContDiff ℝ ⊤`).** `P = ∏_s C^(s)` is a polynomial in the matrix entries (iterated matrix
multiplication is multilinear → polynomial); the reg-block-residual is a linear read-off of `P`'s entries
minus the constant `I_r`. A polynomial map ℝⁿ → ℝᵐ is `ContDiff ℝ ⊤`. ✓ (`Matrix.mul` is bilinear;
`ContDiff.matrix_mul`-style + `ContDiff.sub_const`.)

**`_deriv` — CORRECTED (2026-06-23, controller-blessed): the obligation is `HasStrictFDerivAt
regStraighten (shear-CLE) 0` for an explicit INVERTIBLE shear CLE, NOT `= ContinuousLinearMap.fst`.**
The earlier `= fst` was an OVER-statement (mine); name=content — the actual derivative is a shear, not a
reg-projection. Why the correction (the #120 reg-slot analysis):

By #91 (general-L, idempotent sandwich), `d(P−B)|_0 = [[Σ_s X_s, Y_L],[Z_1, 0]]` — the regular-block
residual's X-corner derivative is the SUM `Σ_s X_s` over ALL L layers. But the reg slot `Fin nReg` carries
ONE r×r X-block; the L−1 interior X_s live in the GAUGE slot (and `regStraighten` FIXES the spectator —
`regStraighten_spectator` — so they stay FREE in the output). So `d(regStraighten)(0)` reads the reg-X +
the gauge-X's, summing into the reg-X output, while KEEPING the gauge-X's: the unitriangular SHEAR

    d(regStraighten)(0) = [[I, Σ],[0, I]]   (reg-out = reg-X + Σ gauge-X's; gauge-out = gauge-X's, unchanged)

— det 1, INVERTIBLE (inverse subtracts the gauge-X's back). It is NOT `fst` (fst would zero the gauge,
i.e. require the gauge to BE ker(summing); with the opaque `regGaugeIdxSplit`, gauge ≠ ker, so the
gauge-X's are NOT zeroed — they shear into reg and stay free).

This is SUFFICIENT for PIN1: the peel `rlctAtOn_comp_localDiffeo` (DeepestRegAbsorbIFT:220/§) decl-takes
`(e : M ≃L[ℝ] M) (hf : HasStrictFDerivAt f (e : M →L M) wstar)` — it needs the derivative to be SOME
INVERTIBLE CLE, NOT `fst`. The shear `[[I,Σ],[0,I]]` is invertible, so PIN1 closes with `_deriv = e`
(the shear CLE). No `fst`, no gauge-kill, no reg-slot image/kernel restructure. (Triple-confirmed:
decl peel-takes-`e` + `regStraighten_spectator`-fixes-gauge + Codex-xhigh decorrelated; shear-invertibility
elementary, det 1. See `codex/regslot-resolution-answer.md`.)

**#91 reconciliation.** #91's `dE(0) = (Σ_s X_s, Y_L, Z_1)`-all-coeffs-`I_r` IS the shear's action on
reg×gauge (reg-X gets `I` + the gauge-X's get summed in via `Σ`; Y_L/Z_1 the `I` on their blocks). The
"=id" of #91 = "the derivative is an invertible unit (det 1)", which the shear is — NOT the reg-projection
`fst`. The over-statement conflated "invertible unit" with "fst"; the shear is the precise form.

## What cobuild formalises (the three sorries at DeepestGaugeConstruction:313–331)

**IMPLEMENTATION RECONCILE (2026-06-23, against cobuild sub34 @11899a7).** The realised object is NOT
the "fixed explicit block product, no cast" the earlier draft predicted — cobuild built it on the genuine
dependent-Fin `prod H (framedParamsReg H r hr hL p)`:

    deepestEPivot p i = (match regResidualPack i with
      | inl (a,b)        => (P.toBlocks₁₁ − 1) a b
      | inr (inl (a,b))  => P.toBlocks₁₂ a b
      | inr (inr (a,b))  => P.toBlocks₂₁ a b)
    where P := reindex (rThresholdSplit r (H 0) _) (rThresholdSplit r (H last) _) (prod H (framedParamsReg p))

`framedParamsReg p s = framedLayer (readX/Y/Z p s) 0` — the deepest layers in the `(reg,gauge)` slots;
`framedParamsReg_zero` (DeepestFramedProduct:132) gives `framedParamsReg 0 s = reindex e_s.symm e_{s+1}.symm
(fromBlocks 1 0 0 0)`. So the product DOES carry the `prodAux` `e1/e2` width-casts (the #111 friction).

- `deepestEPivot`: DONE (the three-block `regResidualPack`-flatten of `P`). `_contdiff`: PROVED @11899a7
  (`contDiff_prod_entry` + per-entry block read-off + `sub_const`).
- `_base` (`deepestEPivot 0 = 0`): the cast-aware recipe (handed to cobuild — their file, their write).
  Crux helper, host in DeepestFramedProduct.lean:

      theorem prod_framedParamsReg_zero :
        prod H (framedParamsReg H r hr hL 0)
          = reindex (rThresholdSplit r (H 0) (hr 0)).symm
              (rThresholdSplit r (H (Fin.last L)) (hr (Fin.last L))).symm
              (fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 0 0)

  Proof = `prodAux` induction (k : 0→L), IH `prodAux ... k = reindex e₀.symm (rThresholdSplit r (H ⟨k,_⟩) _).symm
  (fromBlocks 1 0 0 0)`. Step: `prodAux(k+1) = prodAux(k) * framedParamsReg 0 ⟨k,_⟩`, rewrite the factor by
  `framedParamsReg_zero`. Two Mathlib lemmas close the reindex×reindex of two `fromBlocks`:
  `Matrix.submatrix_mul_equiv` (Mul.lean:1151, @[simp]) cancels the MIDDLE interface (`reindex e.symm =
  submatrix e`; the layer-k.succ rThresholdSplit = layer-(k+1).castSucc, defeq via prodAux's e1/e2, so the
  two middle equivs MERGE), then `Matrix.fromBlocks_multiply` (Block.lean:214) gives the corner idempotent
  `[1,0;0,0]·[1,0;0,0] = [1,0;0,0]`. Then `deepestEPivot_base`: `funext i; rw prod_framedParamsReg_zero`; `P =
  reindex e₀ eL (reindex e₀.symm eL.symm (fromBlocks 1 0 0 0))` collapses (reindex_reindex cancels) to
  `fromBlocks 1 0 0 0`; per `regResidualPack` arm: inl `(1−1)=0`, inr-inl `0`, inr-inr `0`. ~25–35 LoC incl
  the helper. (The earlier "pure simp/decide block algebra" was correct in spirit but under-specified the
  dependent-Fin telescoping — that is the load-bearing part.)
- `_contdiff`: polynomial (`ContDiff.matrix_mul` chain + `sub_const`).
- `_deriv` (CORRECTED): `HasStrictFDerivAt regStraighten (shear-CLE) 0` for the explicit invertible shear
  `e = [[I, Σ],[0, I]]` (det 1) — NOT `fst`. cobuild: (ii) package `e` as a GENUINE invertible CLE
  (unitriangular + its inverse `[[I, −Σ],[0, I]]`, det 1, the `ContinuousLinearEquiv` — not asserted-invertible);
  then `HasStrictFDerivAt regStraighten (e : M →L M) 0` via the #91 block-derivative (origin/g213-pin1-de0
  @09475f2: the (0,0) X-sum + (0,1)-last + (1,0)-first = the shear's action). The peel
  `rlctAtOn_comp_localDiffeo` consumes `(e, hf)` directly (guard (i): don't weaken past what the peel takes —
  it takes `e : ≃L`, the shear IS that). Compile arbitrates.

CAVEAT (scope-honest, g125): this is the regular-GENERATOR residual (unit-pivot equivalence), the
squeeze-load-bearing object — NOT a literal Euclidean equality. That is exactly what PIN1's IFT-peel
(form-agnostic, needs only `dE(0)` an INVERTIBLE CLE — the shear `[[I,Σ],[0,I]]`, NOT `fst` — plus
ContDiff + 0↦0) and PIN2's Φ-component consume.
