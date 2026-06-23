# #82-deriv turnkey tactic cert — the alignment + #91 sandwich close (deriv-fm, 2026-06-23)

For cobuild's in-place close of `deepestEPivot_regSlice_fderiv_id` AFTER the def-change (regResidualPack
:= regPivotFinEquiv, regGaugeIdxSplit's reg-half := regBoundaryToRegGauge ∘ regPivotFinEquiv). The
strict-deriv is FREE (`ContDiff.hasStrictFDerivAt` on `deepestEPivot_contdiff`); the content is the VALUE
identification `= id`. This cert gives the concrete tactic route + the load-bearing intermediate lemmas.

## The target (post def-change)

    theorem deepestEPivot_regSlice_fderiv_id … :
      HasStrictFDerivAt (fun r0 : Fin (deepestNReg H r) → ℝ => deepestEPivot H r hr hL (r0, 0))
        (ContinuousLinearMap.id ℝ (Fin (deepestNReg H r) → ℝ)) 0

## Route — per-coordinate, NOT via cobuild's existential `D`

`hasStrictFDerivAt_prod_entry` returns `∃ D, HasStrictFDerivAt (prod entry) D x` — D is an OPAQUE
`∑ m, D_m`, NOT the explicit `(Σ_s δX_s, δY_L, δZ_1)`. So do NOT try to match cobuild's existential D to
`id`. Instead go per-coordinate on the OUTPUT and prove each output coordinate's derivative is the
matching input projection, via `hasStrictFDerivAt_pi`:

    rw [show (ContinuousLinearMap.id ℝ _) = ContinuousLinearMap.pi (fun i => proj i) from …]
    refine hasStrictFDerivAt_pi.2 (fun i => ?_)
    -- goal: HasStrictFDerivAt (fun r0 => deepestEPivot (r0,0) i) (proj i) 0
    --       where proj i = ContinuousLinearMap.proj i (the i-th coordinate read)

For each output coord `i : Fin nReg`, `regResidualPack i = regPivotFinEquiv i ∈ BoundaryPivotIdx` (now
TRANSPARENT — reduces by the finCongr/finSumFinEquiv/finProdFinEquiv `_apply` lemmas, NOT opaque). Case
on the boundary arm (`rcases regPivotFinEquiv i with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩`):

### Arm 1 — `inl (a,b)` (the (0,0)-corner / X-pivot)
Output coord = `(P.toBlocks₁₁ − 1) a b` where `P = reindex (prod (framedParamsReg (r0,0)))`. By the #91
sandwich (below), `d/dr0 [(P11−1) a b]|_0 = (Σ_s δX_s) a b`, and with gauge = 0 the only X in the reg
image is `X_first` (the injective routing — `regBoundaryToRegGauge_injective`), so `Σ_s δX_s = δX_first`,
and `δX_first a b = (the reg coord regPivotFinEquiv.symm (inl (a,b)))` — i.e. `= proj i`. KEY identity:
`(framedParamsReg (r0,0)) reads readX_first (r0) a b = regGaugeSlotEquiv (r0,0) ⟨0, inl(inl(a,b))⟩`,
and post-def-change `regGaugeSlotEquiv (r0,0) ⟨0,inl(inl(a,b))⟩ = r0 (regPivotFinEquiv.symm (inl(a,b)))`
(= `r0 i`) BY CONSTRUCTION (the reg-half routes via regBoundaryToRegGauge ∘ regPivotFinEquiv, so the
inverse round-trips). So the coord IS `r0 i + O(r0²)`, derivative `proj i`. ✓

### Arm 2 — `inr (inl (a,b))` (Y_last) / Arm 3 — `inr (inr (a,b))` (Z_first)
Same, simpler (no Σ — Y_L/Z_1 are single-layer): `d[P12 a b]|_0 = δY_last a b = r0 i`,
`d[P21 a b]|_0 = δZ_first a b = r0 i`. ✓

## The #91 sandwich lemma (the load-bearing intermediate — STATE + PROVE once)

    -- d(prod (framedParamsReg (r0,0)))|_0 = Σ_s (corner prefix) · δC_s · (corner suffix), and the
    -- corner prefix/suffix products are blockdiag[I_r,0] (idempotent), so:
    lemma framedProd_regSlice_fderiv (… i j) :
      HasFDerivAt (fun r0 => (reindex (prod (framedParamsReg (r0,0)))) i j)
        (D_block i j) 0
    -- where D_block reads: (0,0)→Σ_s δX_s, (0,1)→δY_L, (1,0)→δZ_1, (1,1)→0.

PROOF SKELETON (the ~30-50 lines):
1. `prod_framedParamsReg_zero` (banked): at r0=0, `prod (framedParamsReg 0) = reindex (fromBlocks 1 0 0 0)`
   — the corner. So the base point value is the corner.
2. The product derivative at 0 (Leibniz, cobuild's `hasStrictFDerivAt_prodAux_entry` VALUE, or a direct
   `prodAux` induction): `dP|_0 = Σ_s prodAux_prefix(0) · δC_s · prodAux_suffix(0)`. The prefix/suffix
   AT r0=0 are the idempotent corner (by `prodAux_framedParamsReg_zero_aux` — the partial products at 0
   are all the corner).
3. The corner sandwich `corner · δC_s · corner` keeps: (0,0)-block of δC_s for ALL s (corner·X·corner =
   X on the (0,0)), (0,1)-block only for the LAST layer (suffix empty → corner·[0 Y;0 0]·1 form), (1,0)
   only for the FIRST. The `fromBlocks_multiply` / `corner_reindex_mul` kernels (banked in
   DeepestTelescoping) do the block algebra.
4. `δC_s = framedLayer` derivative = `fromBlocks (δreadX) (δreadY) (δreadZ) 0` (T=0), and readX/Y/Z are
   LINEAR in r0 (regGaugeSlotEquiv is a CLE — `regGaugeSlotCLE`), so `δreadX_s = readX_s` etc. (a linear
   map's derivative is itself). So `Σ_s δX_s = Σ_s readX_s(r0)`.

## The alignment lemma (the rfl/decide reduction — the EARLY-CHECK)

    lemma regSlice_read_pack_id (i : Fin (deepestNReg H r)) :
      -- post def-change: the reg-coord round-trips
      regGaugeSlotEquiv (r0, 0) (regBoundaryToRegGauge (regPivotFinEquiv i))
        = r0 i  -- (for the surviving boundary arm)

This should be `rfl`/`simp [regGaugeSlotEquiv, regGaugeIdxSplit, regBoundaryToRegGauge, regPivotFinEquiv,
Equiv.symm_apply_apply]` ONCE regGaugeIdxSplit's reg-half is `regBoundaryToRegGauge ∘ regPivotFinEquiv`
— because then `regGaugeSlotEquiv`'s read of the boundary entry inverts the routing. This is the
"cancel by symm_apply_apply" — the WHOLE POINT of using ONE shared regPivotFinEquiv for both defs. If it
does NOT reduce, the def-change wiring is wrong (the early-check catches it here, cheap).

## Tactics inventory (all banked / Mathlib)
- `hasStrictFDerivAt_pi` (Mathlib, Pi.lean) — per-output-coordinate.
- `ContinuousLinearMap.proj` / `.pi` — the `id` as a pi of projections.
- `prod_framedParamsReg_zero`, `prodAux_framedParamsReg_zero_aux`, `corner_reindex_mul`,
  `fromBlocks_multiply` (banked, DeepestTelescoping).
- `regGaugeSlotCLE` (DeepestFramedProduct) — readX/Y/Z linearity (δread = read).
- `hasStrictFDerivAt_prodAux_entry` (cobuild @2bf7065) — IF a Leibniz value is wanted; else direct induction.
- `ContDiff.hasStrictFDerivAt` (Mathlib RCLike) — the FREE strict upgrade.
- The transparent `finProdFinEquiv_apply` / `finSumFinEquiv_apply_*` / `finCongr` `_apply` lemmas — make
  `regPivotFinEquiv i` and `regBoundaryToRegGauge` REDUCE (the property the opaque Fintype.equivFin lacked).

## Risk / where it could wall
- The `Fin.last` cast in `regBoundaryToRegGauge` (Y_last layer-tag) — the `(Fin.last Lm).succ =
  Fin.last (Lm+1)` finCongr may need `Fin.succ_last` + a `cast_eq`/`finCongr_apply` simp to discharge in
  the alignment reduction. Iterate in live env.
- The Σ_s collapse to δX_first needs `readX_s (r0,0) = 0` for s ≠ 0 (interior X in the GAUGE slot, held
  at 0). Post-def-change this is `regGaugeSlotEquiv (r0,0) ⟨s≠0, inl(inl)⟩ = 0` — because the interior
  entries are in the gauge half (the complement), and gauge = 0. STATE this as `readX_interior_zero`.
- If the per-coordinate derivative-of-(P11−1) doesn't directly give `Σ_s readX_s`, fall back to the
  explicit `framedProd_regSlice_fderiv` lemma (step 1-4 above) as the bridge.

Bank: this cert + the decls @0dce81e + wiring-spec v2 @fd32713. deriv-fm available to pair on any wall.
