import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegSliceId` — gauge-zero reg-slice derivative (#82-deriv)

The last open analytic piece of cobuild's `deepestEPivot_deriv` assembly: the gauge-zero
regular-slice derivative of `deepestEPivot` at `0`, claimed to be the identity continuous
linear map,

    HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0)) (ContinuousLinearMap.id ℝ _) 0.

Stated EXACTLY as cobuild's consumer `deepestEPivot_regSlice_fderiv_id` expects; cobuild would
wire `exact deepestRegSlice_fderiv_id …` into its `_deriv` assembly on landing. We do not edit
cobuild's `DeepestGaugeConstruction.lean`.

## Status — WALLED at the opaque-packing obstruction (not provable as stated)

The `regResidualPack`↔pivot-coord correspondence cannot be exposed with the current definitions,
so the statement is NOT provable as written; one `sorry` remains, documented below. See the
thread report for the full verdict and the requested fix (a definitional change in cobuild's
files, or a pp2 cert that pins the orderings — both require redefining the two opaque equivs).

### The mathematics (the derivative VALUE) — this part is correct

At `reg = 0` every framed layer is the idempotent corner `blockdiag[I_r, 0]`. By Leibniz with
idempotent prefix/suffix products (empty product = full identity at the two boundary layers,
corner in the interior),

    dP|_0 = ( P11' = Σ_{s=1}^L dX_s,   P12' = dY_L,   P21' = dZ_1 )

— the reg-residual derivative reads the layer-1 `Z`, the layer-`L` `Y`, and the SUM of every
layer's `X`. This is the #91 idempotent-sandwich fact (g213-pin1-de0).

### Why `= id` is not reachable from the present definitions

`deepestEPivot (r0, 0)`'s reg input `r0 : Fin nReg → ℝ` is distributed over the per-layer
`X_s/Y_s/Z_s` blocks (`RegGaugeIdx = Σ_s (X_s ⊕ Y_s ⊕ Z_s)`, ALL `L` layers) via
`regGaugeSlotEquiv`, i.e. via the OPAQUE `regGaugeIdxSplit.symm ∘ Sum.inl`
(`regGaugeIdxSplit := Fintype.equivFin (RegGaugeIdx) ∘ …`). The output is packed by
`regResidualPack := … ∘ (Fintype.equivFin _).symm` — an INDEPENDENT opaque bijection onto the
three BOUNDARY blocks `(X-corner r×r) ⊕ (Y_last r×(H_last−r)) ⊕ (Z_first (H_0−r)×r)`.

So the reg-slice derivative, as a `Fin nReg → ℝ` self-map, is

    r0 ↦ regResidualPack_pack( Σ_s X_s(r0),  Y_L(r0),  Z_1(r0) ),

a composite of two unrelated `Fintype.equivFin` permutations around a middle step that SUMS the
per-layer `X`-blocks and DROPS the interior `Y_s` (`s ≠ L`) and `Z_s` (`s ≠ 1`). Equality with
`id` would require `regGaugeIdxSplit` to map the reg slot EXACTLY onto the boundary generators
(no reg coordinate landing on a dropped interior block) AND `regResidualPack` to be the matching
inverse packing. Neither is implied: `Fintype.equivFin` is a structure-blind ordering with NO
computation rule (no equation lemma exposes `regGaugeIdxSplit idx` or `regResidualPack i`), and
there is no compatibility lemma between the two. A `simp`/`rw` cannot reduce either; if a reg
coordinate lands on an interior `Y`/`Z` it is dropped and the map is rank-deficient — so the
statement is not even generically true under the current opaque defs.

The dimensions DO match by design (`deepestNReg = r(H_0+H_last−r) = r² + r(H_last−r) + (H_0−r)r`,
the boundary-generator count), so the intended object exists — but the two `Fintype.equivFin`
packings do not realise the intended boundary correspondence. The fix lives in cobuild's files:
replace the two opaque `Fintype.equivFin` packings (`regGaugeIdxSplit` in `DeepestSplitReindex`,
`regResidualPack` in `DeepestGaugeConstruction`) with ONE structured boundary-block bijection that
explicitly sends the reg slot to `(X-corner, Y_last, Z_first)` and the interior `X_s/Y_s/Z_s` to
the gauge slot.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The gauge-zero reg-slice derivative of `deepestEPivot` at `0`** — the standalone form of
cobuild's `deepestEPivot_regSlice_fderiv_id`. WALLED: not provable as stated; the
`regResidualPack`↔`regGaugeIdxSplit` boundary correspondence is unexposable for the opaque
`Fintype.equivFin` packings (see module docstring). -/
theorem deepestRegSlice_fderiv_id (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) (hL : 1 ≤ L) :
    HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ =>
        deepestEPivot H r hr hL (r0, 0))
      (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0 := by
  -- WALL: per-coordinate (`hasStrictFDerivAt_pi'`) the goal reduces to the derivative of one block
  -- entry of `P = reindex (prod (framedParamsReg (r0,0)))`, whose value is the #91 collapse
  -- `(Σ_s dX_s, dY_L, dZ_1)`. Matching that to `r0 i` (= `proj i`) needs the
  -- `regGaugeIdxSplit`↔`regResidualPack` correspondence, which the opaque `Fintype.equivFin`
  -- packings do not expose (no equation lemma; `simp` cannot reduce `regGaugeIdxSplit idx`).
  -- Needs the cobuild-side definitional change (structured boundary-block bijection) or a pp2 cert.
  sorry

end DLNFibre.DLN.RLCT
