# Statement card — `RouteMSchurFiring` (the generic per-corank `SchurRecStep` firing)

**Status:** `sorry-free` (the build is green; ZERO `sorry`/`axiom`/`native_decide` in the file — the
carving heart `schurRatioResidGen_mid` is CLOSED). Awaiting reviewer fidelity check.

**File:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean` (branch `genm-capstone`
@ `3e26a171`; bump on change).

## The headline

```lean
theorem schurRecStep_four : SchurRecStep 4 schurLambda
```

— the SOLE remaining R1-UPPER input to `RouteMSchurGeneral.schurGen_lt_top_modulo_recStep`. `SchurRecStep`
is the per-corank analytic step (`RouteMSchurGeneral`): given the threshold contract and the abstract lower
IH `SchurLowerIH 4 schurLambda r`, the corank-`r` Schur core `SchurCore 4 r c' T` is finite for
`0 < c' < schurLambda r`, every `T > 0`.

**English gloss.** For arbitrary corank `r`, the radial-Schur recursion fires: cover the `Δ`-box by its
`r²` max-modulus-entry charts, radial-blow-up each, peel the top `Fin 4` Morse block at threshold `2`, and
recurse on the lower corank-`(r−1)` Schur core via the abstract IH — yielding `∫_{Δ∈[−T,T]^{r×r}}
∫_{S∈[−T,T]^{r×4}} ‖Δ·S‖_F^{−c'} < ⊤` for `c' < λ_{r,4} = 2r−2` (`r ≥ 2`).

## Dispatch (all sorry-free except the carving heart)

| corank | route | status |
|---|---|---|
| `r = 0` | vacuous (`c' < λ_0 = 0` contra `0 < c'`) | sorry-free |
| `r = 1` | `schurCore4_one` — Morse leaf (`Δ₀₀`-axis divisor × `Fin 4` Morse block) | **sorry-free, axiom-clean** |
| `r = 2` | `schurCore4_two` (the banked corank-2 base, general `T`) | sorry-free |
| `r ≥ 3` | `schurCoreGen_firing` — the genuine firing | **sorry-free** (carving closed) |

## What is PROVED sorry-free (the firing skeleton + all plumbing)

- `schurCore4_one` — the r=1 Morse-leaf base. **axiom-clean** `[propext, Classical.choice, Quot.sound]`.
- the generic flatten + `r²`-chart radial cover: `matToFlatG`, `flatBoxG`, `matBoxG_outer_flat`,
  `gFlatG_cover_sum`, `RmatG`, `gFlatG_blowup_radial`.
- the pivot-axis ↔ ratios reshape `piRatioG` (via `arrowCongr'` + `piFinSuccAbove`, eq_rec-free symm) +
  its `measurePreserving` + the full characterization (`piRatioG_symm_apply/_pivot/_offpivot`,
  `_apply_fst/_snd`, `ratioIdx_ne`).
- `chart_integrand_factorG` (Jacobian `|y p|^{r²−1}`) + `schur_matBoxG_chart_lt_top` (the per-chart
  finiteness — a-axis divisor `c' < r²/2` × the ratio residual) — **fully proven**.
- `schurRatioResidGen` (the subcritical fold `c' ≤ 2 → c'' = 3` via `ofReal_rpow_neg_le_one_addG`).
- the generic perm helpers `frobSq_rmatMul_permG`, `matBox_rowperm_lintegralG` (pivot → (0,0)).
- the generic flatten + `r²`-chart cover REUSES the canonical `RouteMSchurGenCover` (at `p = 4`);
  only `RmatG` / `gFlatG_blowup_radial` (the radial pull-out) are local.
- **all the carving's ANALYTIC prerequisites, each axiom-clean:** `core_T_peel_le_ae_G` (generic
  Morse-peel-under-integral), `matBoxSq_translate_le`, the IH-invoking `schurResidG_translate_lt_top`
  (`< ⊤`), and the `Sh`-UNIFORM `_le` form `coreSchurGenVal` + `coreSchurGenVal_lt_top` +
  `schurResidG_translate_le` (the boundary-integrable bound the carve-first outer `rest`-integral consumes).

`#print axioms` (force-recompiled on the olean-DELETED target, per the olean-masking gate):
`schurRatioResidGen_mid`, `schurRatioResidGen`, `innerSGenCarve_le`, `stepShearG_r`,
`frobSqTopRow_eq_shear`, `ScCarve_eq` are ALL `[propext, Classical.choice, Quot.sound]` — clean-three,
**no `sorryAx`, no `monomial_rlct` (S2-FREE), no `native_decide`**.

## The carving — `schurRatioResidGen_mid` — CLOSED

```lean
theorem schurRatioResidGen_mid (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))) < ⊤
```

The JOINT ratio-residual (over the `r²−1` angular ratios `z` AND `S`), proven sorry-free by WIRING the
landed bricks in the Codex-confirmed carve-first order. The proof and its five new helpers:

- **`innerSGenCarve_le`** (the per-`(M,v)` heart, `M` free): for the carved angular matrix
  `R = RmatGnorm (zEG.symm (M,v))`, the inner-`S` integral is `≤ ofReal(c₀^{−c'})` times the per-`M`
  resolved slice (`S_bot`/`T'` boxes at radius `K = max 1 (r·T)`, shift `Sh = bgShiftG v`).
- **N2b** (`schur_minorPivot_split` `j=1`): the lower leg `c₀·(frobSq row0 + frobSq(Sc·S_bot)) ≤
  frobSq(R·S)` feeds `ofReal_rpow_le_const_mul` (pivot minor `M11 = [1]`, so `hpivot`/`hne` are trivial,
  and the zero-coincidence comes from the N2b UPPER leg).
- **`frobSqTopRow_eq_shear`** (the N2b↔shear bridge): the `j=1` top block `frobSq((R·S) row0)` expands to
  `∑_q (S₀q + ∑_a R₀,ₐ₊₁·Sₐ₊₁,q)²` via `Fin.sum_univ_one` + `fin_sum_block_split 1` + the pivot
  `R₀₀ = 1`.
- **`stepShearG_r`** (the width-`r` shear wrapper): `finCongr` row-reindex of `stepShearG` to N2b's
  `Fin r` `⟨1+a⟩`/`⟨0⟩` index conventions; peels the `Fin 4` Morse spectator.
- **`ScCarve_eq`** (the carve-`Sc` readback): N2b's `Sc = M22 − M21·M11⁻¹·M12` reads off the carve as
  `M(a,b) − v(inl a)·v(inr b) = (matOf M − bgShiftG v)`.
- **`zEG_fst_apply`/`zEG_snd_apply`** (forward `zEG` slot read-backs): close the box preimage
  `[−1,1]^N = zEG⁻¹(Mbox ×ˢ vbox)`.
- **assembly:** `innerSGen_eq_norm` (pivot-WLOG) → CoV `z ↦ (M,v)` via `measurePreserving_zEG` + Tonelli
  (`v` outer) → per-`(M,v)` `innerSGenCarve_le` → curry `M ↦ Δ` (a `piCurry`/`arrowCongr'` MP equiv) +
  enlarge `Mbox` (radius 1 ⊆ K) → `resolvedShiftRG_le` (`B = 1`, `|bgShiftG v| ≤ 1`) → the abstract IH
  `coreSchurGenVal_lt_top` (`c'−2 < schurLambda (r−1)`) → the bounded `v`-box volume.

## Fidelity notes (for the reviewer)

- The firing invokes the lower-corank IH **abstractly** (`SchurLowerIH`), NOT a concrete general-T
  `core_schur3` — the genm-recstep decoupling. ✓
- The fixed-`R` inner-`S` finiteness would be FALSE (diverges at singular `R`/`Sc`); the heart is correctly
  the JOINT ratio-residual (integrating `z` carries the free `M22`). ✓
- Threshold arithmetic (numerically + Codex verified): `λ_{r,4} = 2r−2` (`r ≥ 2`); the firing's mid window
  `2 < c' < λ_r` gives `c'' = c'−2 ∈ (0, λ_{r−1})`; the subcritical `c'' = 3` target sits in `(2, λ_r)` for
  all `r ≥ 3`. ✓
- NOT yet aggregated into `DLNFibre.lean` (single-writer; the controller wires it). No sibling name clashes
  (comprehensive grep over the tree; the six new helpers each defined in exactly one file;
  `ofReal_rpow_neg_le_one_addG` renamed to dodge the Corank3 clash).
- The carve close reuses the (3,3,4) anchor's TEMPLATE structure but NOT its `r=3`-specific
  `angularR_reconstruct`/`frobSq_angularR_ge` (a `nlinarith`-clean explicit comparability that does not
  generalize); the generic route goes through the N2b two-sided comparison `schur_minorPivot_split`. ✓
- The per-`(M,v)` bound leaves `M` FREE (it is the carved `M22` cube); the outer `∫_M` is the SAME as
  `resolvedShiftRG_le`'s `∫_Δ` after the curry `M ↦ Δ` — the `M`-integration is NOT hidden in a constant. ✓
