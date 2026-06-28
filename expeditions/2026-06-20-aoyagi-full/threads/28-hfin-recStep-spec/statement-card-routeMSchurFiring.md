# Statement card — `RouteMSchurFiring` (the generic per-corank `SchurRecStep` firing)

**Status:** `1-sorry` (the build is green; exactly ONE named `sorry`, under a correct statement, confined
to the carving heart `schurRatioResidGen_mid`). All surrounding firing pieces are sorry-free.

**File:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean` (branch `genm-firing`).

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
| `r ≥ 3` | `schurCoreGen_firing` — the genuine firing | sorry-free *modulo* the carving |

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
- the IH-invoking carving CORE `schurResidG_translate_lt_top` (`matBoxSq_translate_le` + the abstract
  `SchurLowerIH`). **axiom-clean**.

`#print axioms` (force-recompiled, per the olean-masking gate): `schurCore4_one`,
`schurResidG_translate_lt_top` are `[propext, Classical.choice, Quot.sound]` (clean); the chain through
`schur_matBoxG_chart_lt_top` / `schurRatioResidGen` / `schurCoreGen_firing` correctly shows `sorryAx`,
confined to the single `schurRatioResidGen_mid`.

## The ONE remaining sorry — `schurRatioResidGen_mid` (the carving)

```lean
theorem schurRatioResidGen_mid (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))) < ⊤
```

The JOINT ratio-residual (over the `r²−1` angular ratios `z` AND `S`). Codex (xhigh, decorrelated, twice)
confirmed the route is REACHABLE-PLUMBING, ROUTE A, **no design wall** — `~200` generic-`r` lines.
ORDER **carve-first**; HARDEST sub-step = the generic readback `Sc = M22 − Sh(rest)` (the
`zE_G` reshape carving the `(r−1)²` M22-coords + the `2(r−1)` M21/M12 shift-coords out of the ratios).
The plan (recorded in-file at the sorry): pivot-WLOG → carve `z = (M22 ⊕ rest)` → pointwise N2b/split →
shear → Tonelli → a.e. Morse peel over the FREE `(M22, S_bot)` joint core → `schurResidG_translate_lt_top`
per fixed `rest` at exponent `c'−2`, radius `K = max 1 T` → bounded-`rest`-box volume.

## Fidelity notes (for the reviewer)

- The firing invokes the lower-corank IH **abstractly** (`SchurLowerIH`), NOT a concrete general-T
  `core_schur3` — the genm-recstep decoupling. ✓
- The fixed-`R` inner-`S` finiteness would be FALSE (diverges at singular `R`/`Sc`); the heart is correctly
  the JOINT ratio-residual (integrating `z` carries the free `M22`). ✓
- Threshold arithmetic (numerically + Codex verified): `λ_{r,4} = 2r−2` (`r ≥ 2`); the firing's mid window
  `2 < c' < λ_r` gives `c'' = c'−2 ∈ (0, λ_{r−1})`; the subcritical `c'' = 3` target sits in `(2, λ_r)` for
  all `r ≥ 3`. ✓
- NOT yet aggregated into `DLNFibre.lean` (single-writer; the controller wires it). No sibling name clashes
  (comprehensive grep over the tree; `ofReal_rpow_neg_le_one_addG` renamed to dodge the Corank3 clash).
