# #82-deriv wiring-spec — the #120 explicit-pack refactor that makes `deepestEPivot_regSlice_fderiv_id` provable

**deriv-fm, 2026-06-23, read-only on base `fm2/deepest-gauge-chart-sub34` @22719fb.** The single open
obligation of `deepestEPivot_deriv` is

    deepestEPivot_regSlice_fderiv_id :
      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0, 0))
        (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0

which is TRUE-by-the-math but **unprovable as defined** (two independent opaque `Fintype.equivFin`:
`regResidualPack` and `regGaugeIdxSplit`). This spec is the value-preserving transparency refactor that
makes it `id` BY CONSTRUCTION. Output of the NOW-phase (read-only); the drop-in is AFTER cobuild hands
off `DeepestGaugeConstruction.lean`.

---

## 1. The coordinate accounting (why `= id` needs aligned reg coords)

`nReg = r(H₀ + H_L − r) = r·r + r·M_L + M₀·r` (with `M₀ = H₀−r`, `M_L = H_L−r`). The reg-slice
derivative composite at gauge-zero is

    d[r0 ↦ deepestEPivot(r0,0)]|₀  =  regResidualPack-CLM ∘ (idempotent sandwich) ∘ regGaugeSlotRead|_reg

with the sandwich (g213/#91) keeping the surviving blocks:

    d(P11) = Σ_s δX_s        (sum over ALL L layers' X_s blocks, each r×r)
    d(P12) = δY_L            (only the LAST layer's Y survives)
    d(P21) = δZ_1            (only the FIRST layer's Z survives)

**Key point.** At gauge-zero, every X_s/Y_s/Z_s NOT carried by the reg slot is held at `0` (it lives in
the gauge slot). So `Σ_s δX_s` collapses to JUST the X-block(s) the reg slot feeds. For the composite to
be `id` on `Fin nReg`, the reg slot must carry exactly ONE private coordinate per output coordinate:

- the `r·r` `(0,0)`-block coords → a SINGLE layer's X (canonically `X_first`, i.e. `s = 0`); the other
  X_s (s≠0) sit in the gauge slot = 0, so `Σ_s δX_s = δX_first = the reg (0,0)-coords`;
- the `r·M_L` coords → `Y_last` (the only surviving Y); other Y_s in gauge = 0;
- the `M₀·r` coords → `Z_first` (the only surviving Z); other Z_s in gauge = 0.

Then `regResidualPack` packs `(δX_first, δY_last, δZ_first)` back to `Fin nReg` IDENTICALLY ⟹ reg-block
= `id`. This is exactly g213's "pivot coords": the boundary generators `(X_first, Y_last, Z_first)`, one
private pivot each, coefficient `I_r`.

**Both opaque equivs must be coordinated** (not just one): `regGaugeIdxSplit`'s reg-half must route
`Fin nReg` to the boundary-generator `RegGaugeIdx` entries `{⟨0, inl(inl(i,j))⟩} ∪ {⟨last, inl(inr)⟩} ∪
{⟨0, inr⟩}`, and `regResidualPack` must use the matching enumeration. The interior X_s (s≠0), Y_s
(s≠last), Z_s (s≠0) go to the gauge half.

## 2. The explicit boundary-generator equiv (the value-preserving replacement)

Replace BOTH opaque `Fintype.equivFin` with an explicit `regBoundaryEquiv` built from the SAME canonical
enumeration. Define the **boundary-pivot index type**

    BoundaryPivotIdx H r := (Fin r × Fin r) ⊕ ((Fin r × Fin (H_L − r)) ⊕ (Fin (H₀ − r) × Fin r))

(`= deepestNReg`-cardinality, the residual-block sum type `regResidualPack` already targets). The
explicit equiv sends each boundary block to the matching `RegGaugeIdx` entry:

    regBoundaryToRegGauge : BoundaryPivotIdx H r ↪ RegGaugeIdx H r
      | inl (i,j)          ↦ ⟨0,        inl (inl (i,j))⟩    -- X_first
      | inr (inl (i,j))    ↦ ⟨Fin.last, inl (inr (i,j))⟩    -- Y_last
      | inr (inr (i,j))    ↦ ⟨0,        inr (i,j)⟩          -- Z_first

The gauge half is `RegGaugeIdx \ image(regBoundaryToRegGauge)` (the interior/non-boundary X/Y/Z). The
two replacements:

- **`regGaugeIdxSplit`** (`DeepestSplitReindex.lean:235`): `RegGaugeIdx ≃ Fin nReg ⊕ Fin nGauge` built so
  the `inl`/reg half is `regBoundaryToRegGauge`'s image, `inr`/gauge half the complement. Concretely:
  use the `Equiv` that partitions `RegGaugeIdx` by the boundary predicate, then `Fintype.equivFin` on
  EACH PART (not the whole) — the reg part is `BoundaryPivotIdx`-shaped via the explicit enumeration.
- **`regResidualPack`** (`DeepestGaugeConstruction.lean:357`): `Fin nReg ≃ BoundaryPivotIdx` the EXACT
  INVERSE of the reg-half `Fin`-enumeration used in `regGaugeIdxSplit`. So `regResidualPack` and
  `regGaugeIdxSplit|_reg` use the SAME `Fin nReg ≃ BoundaryPivotIdx` witness ⟹ they cancel.

Cleanest Lean realization: define ONE `regPivotFinEquiv : Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r`
(an honest enumeration — `finCongr` over the `r·r + r·M_L + M₀·r` arithmetic + `finSumFinEquiv`/
`finProdFinEquiv`, NOT `Fintype.equivFin`), and DEFINE both:
  - `regResidualPack := regPivotFinEquiv`
  - `regGaugeIdxSplit`'s reg half := `regBoundaryToRegGauge ∘ regPivotFinEquiv`
so the composite `regResidualPack ∘ (sandwich picks boundary) ∘ (regGaugeIdxSplit|_reg read) = id` holds
definitionally / by `regPivotFinEquiv.symm_apply_apply`.

## 3. The alignment lemma (the new provable target)

    theorem deepestEPivot_regSlice_fderiv_id … :
      HasStrictFDerivAt (fun r0 => deepestEPivot H r hr hL (r0,0))
        (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0

PROVED via: (a) the entry-wise product `HasFDerivAt` fold at `0` (cobuild's banked
`hasStrictFDerivAt_prod_entry` @2bf7065, OR my plain-`HasFDerivAt` fold), giving
`d(P)|₀ = Σ_s corner·δC_s·corner`; (b) the idempotent-sandwich collapse (`prodAux_framedParamsReg_zero` +
`fromBlocks` idempotency) to `(Σ_s δX_s, δY_L, δZ_1)`; (c) the gauge-zero collapse: with gauge = 0, the
interior reads vanish, so `Σ_s δX_s = δX_first`, `δY_L = δY_last`, `δZ_1 = δZ_first`, each `= regPivotFinEquiv`'s
reg-coord (via the explicit `regBoundaryToRegGauge` enumeration); (d) `regResidualPack = regPivotFinEquiv`
packs them back identically ⟹ the coordinate map is `id`. Strict-deriv FREE via
`ContDiff.hasStrictFDerivAt` on `deepestEPivot_contdiff` (my finding) — only the plain `HasFDerivAt`
value-id is needed, then upgrade.

Supporting lemma to STATE (the by-construction cancel):

    theorem regResidualPack_regGaugeIdxSplit_reg_cancel … :
      ∀ i : Fin nReg, regGaugeSlotRead-of (regResidualPack.symm-pivot i) = (the i-th reg basis read)

(the explicit form depends on the final `regPivotFinEquiv`; pin in the drop-in.)

## 4. The re-proof surface (value-preservation map)

`regResidualPack` uses (all in the single-writer `DeepestGaugeConstruction.lean`):
- `deepestEPivot` def (:382) — `match regResidualPack … with` (value: which block each `Fin nReg` coord
  reads). CHANGING `regResidualPack`'s value CHANGES `deepestEPivot`'s value → ripples to ALL #80 lemmas
  that reference `deepestEPivot`'s value (the `hregval` identification in `deepest_loss_squeeze`).
- `deepestEPivot_contdiff` (:407,412) — `rcases regResidualPack` then per-arm `ContDiff`. Equiv-agnostic
  (any bijection works); SAFE.
- `deepestEPivot_base` (:496) — `rcases regResidualPack` then per-arm `fromBlocks 1 0 0 0` residual = 0.
  Equiv-agnostic (every block of the corner gives 0); SAFE.

`regGaugeIdxSplit` uses:
- `regGaugeSlotEquiv` (:253) / `regGaugeSlotCLE` (DeepestFramedProduct.lean:47) — `piCongrLeft`; relabel,
  equiv-agnostic for ContDiff/Homeomorph; SAFE structurally but CHANGES the read VALUE (which slot entry
  is which X/Y/Z) → ripples to `readX/Y/Z` VALUES → `framedParamsReg`/`deepestEPivot` VALUES.
- `regGaugeSlotEquiv_zero` (DeepestSchurShift.lean:98) — `cases (regGaugeIdxSplit …)`; equiv-agnostic; SAFE.
- `deepestRoleIndexEquiv` (DeepestSplitReindex.lean:214, embeds the `eReg = regGaugeIdxSplit` pattern) →
  `deepestSplit_exists` MP proof. **MP is equiv-AGNOSTIC**: `volume_measurePreserving_piCongrLeft` holds
  for ANY `Equiv` (relabel is det=±1). So a semantic `regGaugeIdxSplit`/`deepestRoleIndexEquiv` does NOT
  break the MP `split`. SAFE for MP; but the SLOT SEMANTICS change (which is the POINT).

**The genuine ripple** (the value-changing edges): `deepestEPivot`'s value (via both `regResidualPack` and
`regGaugeSlotEquiv`) feeds cobuild's #80 `deepest_loss_squeeze` through the `hregval` hypothesis
(`(regStraighten q).1 = deepestEPivot (q.1, q.2.2)`). Since the squeeze takes `hregval` as a HYPOTHESIS
(not the concrete value), and the assembly `deepest_gauge_construction` threads it, the squeeze proof is
INSULATED IF it uses `deepestEPivot` only through `hregval` + `deepestEPivot_base` (value at 0 = 0, which
is preserved). **CHECK AT HANDOFF**: does cobuild's #80 `deepest_loss_squeeze` proof unfold
`deepestEPivot`/`regResidualPack` to a CONCRETE per-coordinate value anywhere? If yes → those steps
re-prove against the new enumeration (the residual-block reads are the same blocks, just re-indexed, so
the re-proof is a relabel, cheap). If it only uses `_base` + `hregval` + block-structure → ZERO re-proof.

## 5. Plan + gating recommendation

DEFINITION refactor (AFTER cobuild's #80 handoff), in dependency order:
1. `BoundaryPivotIdx` + `regPivotFinEquiv` (explicit enumeration) — DeepestSplitReindex.lean, ~40-60 LoC.
2. `regBoundaryToRegGauge` + the partition `regGaugeIdxSplit` (semantic) — replace :235, ~50-80 LoC,
   re-prove `card_regGaugeIdx` (unchanged value), `regGaugeSlotEquiv_zero` (equiv-agnostic, ~rfl).
3. `regResidualPack := regPivotFinEquiv` — replace :357, re-prove `_contdiff`/`_base` (equiv-agnostic).
4. `deepestEPivot_regSlice_fderiv_id` — the #91 sandwich + the by-construction cancel, ~150-200 LoC
   (strict-deriv free; plain HasFDerivAt fold + gauge-zero collapse).
5. Re-prove the #80 value-touching steps (surface from §4 at handoff) — cheap if relabel-only.

**GATING RECOMMENDATION**: this is the exact-index-bijection design — the `regPivotFinEquiv` enumeration
+ the `regBoundaryToRegGauge` map + the sandwich-collapse correspondence. Getting the enumeration wrong
wastes the ~200-line formalisation. **Recommend a decorrelated pp2 "coordinate-correspondence cert"
FIRST** (controller's option C): pin the EXACT `Fin nReg ≃ BoundaryPivotIdx` enumeration + the
`regBoundaryToRegGauge` routing + the per-coordinate `Σ_s δX_s = δX_first` collapse, sympy/sage-checked at
a few `(H, r)` (e.g. r=1 M=(1,1,1), r=2 M=(1,0,1,2)). Then the Lean drop-in is mechanical.

## Banked infra (applies in step 4)
`fm/deriv-pin1` @fb174f0 — `DeepestFramedDeriv.lean`: `ContDiff.hasStrictFDerivAt` strict-deriv-free
finding + the square-zero shear-`≃L` algebra (`regShearN`/`regShearEquiv`/`regShearEquiv_coe`, clean-three,
reviewer-PASS). The shear lemmas apply if the assembly is re-expressed in `fst+G∘snd` form; cobuild's
`regStraightenTotalCLM_equiv_of_regBlock_id` is the analogue already in `DeepestRegAbsorbIFT.lean`.
