# Handoff brief — the carving (`schurRatioResidGen_mid`), the SOLE remaining R1-UPPER sorry

**Branch:** `genm-firing` (HEAD `0dfd3641`, pushed). **File:**
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean`. Build green, exactly ONE sorry
(`schurRatioResidGen_mid`). All prereqs below are PROVED + axiom-clean. Build via `lean/scripts/lb`;
**force-recompile the olean before trusting green** (two stale-olean-masked errors caught this tide).

## The target (the sorry, statement is CORRECT + reviewed-PASS)

```lean
theorem schurRatioResidGen_mid (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r)
    (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))) < ⊤
```
where `innerSGen r c' T p y = ∫_{S∈matBox r 4 T} frobSq (RmatG r p y · S)^{−c'}` and `RmatG r p y` is the
`r×r` angular matrix with pivot entry `1` at matrix-cell `(eG r).symm p`, the other `r²−1` cells read off
`y` (the ratio vector; all `|·| ≤ 1` on the ratio box). This is the JOINT ratio-residual — integrating over
`z` is what carries the free `M22` block the IH consumes (NOT a fixed-R inner-S, which is FALSE).

## PROVED prereqs in-file (all axiom-clean — build ON these)

- `schurResidG_translate_lt_top (r) (hr) (hIH) (Sh) (B) (|Sh|≤B) (c'') (0<c'') (c''<schurLambda (r-1)) (K)
  (0<K)` : `∫_{Δ∈matBox(r-1)(r-1) K}∫_{S∈matBox(r-1) 4 K} frobSq((Δ−Sh)·S)^{−c''} < ⊤` — the IH-invoking
  carving CORE (translate Δ↦Δ−Sh into radius K+B, invoke the abstract `SchurLowerIH` at corank r−1).
- `schurResidG_translate_le (r) (hr) (Sh) (B) (|Sh|≤B) (c'') (K)` : same integral `≤ coreSchurGenVal r c''
  (K+B)` — the **Sh-UNIFORM** bound (the carve-first outer `rest`-integral needs Sh-independence).
  `coreSchurGenVal_lt_top` gives `< ⊤` for `c'' < schurLambda (r-1)`.
- `core_T_peel_le_ae_G {m}{Ω} (μ) (c') ((m+1)/2<c') (Tw) (0<Tw) (w) (Z) (hwpos a.e.)` : the generic
  Morse-peel-under-integral `∫_z ∫_T (∑T²+w z)^{−c'} ≤ Cresid·∫_z (w z)^{−(c'−(m+1)/2)}` (m=3, thr 2).
- `matBoxSq_translate_le`, `frobSq_rmatMul_permG`, `matBox_rowperm_lintegralG` (pivot→(0,0)), the radial
  pull-out `gFlatG_blowup_radial`, the full `piRatioG` characterization (`_symm_pivot/_offpivot`,
  `_apply_fst/_snd`, `ratioIdx_ne`).
- `ofReal_rpow_neg_le_one_addG`, the subcritical fold `schurRatioResidGen` (the `c'≤2→c''=3` reduction —
  ALREADY wired to consume `schurRatioResidGen_mid`, so closing `_mid` closes everything).

## The plan (ORDER: carve-first — Codex xhigh ×3 + reviewer-Codex confirmed, NO design wall)

Per `z`: pivot-WLOG (`frobSq_rmatMul_permG` + `matBox_rowperm_lintegralG`, pivot→(0,0)) → carve
`z = (M22 ⊕ rest)` via a generic measure-preserving reshape `zEG : (Fin N → ℝ) ≃ᵐ ((Fin(r-1)×Fin(r-1)→ℝ)
× (Fin (2(r-1))→ℝ))` with readback `Sc = M22 − Sh(rest)` (M11=[1] since pivot=1, so `Sc = M22 − M21·M12`,
`|Sh_ab|=|M21_a·M12_b|≤1`, B=1) → pointwise N2b/split (`schur_minorPivot_split` j=1, the **two-sided
uniform-constant** comparison `c₀(frobSq row0 + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁(…)`) → top-row shear
→ Tonelli → a.e. Morse-peel over the FREE `(M22, S_bot)` joint core (`core_T_peel_le_ae_G`; a.e.-positive by
the nonzero-poly argument AFTER carving — peel-after-carve, so positivity is clean) → `schurResidG_translate_le`
per fixed `rest` at exponent `c'−2`, **radius `K = max 1 T`** (M22 box radius 1, S_bot box radius T — Codex
radius fix) → the outer bounded-`rest`-box volume is a finite constant.

## The three sub-bricks (tasks #134, #135, #136 → #137 assembly)

1. **#134 a.e.-positivity** `frobSqShiftG_ne_zero_ae`: generalize `RouteMSchurCorank3.frobSqR2c3_ne_zero_ae`
   (explicit `MvPolynomial (Fin 12)` + hardwired `!![…]` + flatten `flatR2c3`) to `Fin ((r-1)²+4(r-1))`
   with generic-r matrices. The witness Δ=I, S=e₁ ⟹ core=1. (Cast-intensive: the MvPolynomial matrices
   can't be `!![…]` generically — build them as `Matrix.of (fun i k => X (flatten-idx))` and the witness via
   `Pi.single`s.) NEEDED for the peel's `0 < w` a.e.
2. **#135 the carving reshape** `zEG` + readback `Sc = M22 − Sh(rest)`: generalize corank-3's
   `zσ`/`zE`/`bgShift`/`Δof`/`Δof_eq_zE` (`RouteM334Ratiofin.lean` lines 466-770, ~150 bespoke `Fin 9`/`Fin 8`
   lines keyed to `Rmat334norm`). THE HARDEST. The M22-cells are `{1..r-1}×{1..r-1}` of the pivot-(0,0) R';
   M21 = `{1..r-1}×{0}`, M12 = `{0}×{1..r-1}`. Build `(Fin(r-1)×Fin(r-1)) ⊕ Fin(2(r-1)) ≃ (non-pivot cells)`
   then `MeasurableEquiv.sumPiEquivProdPi`/`piCongrLeft` (the corank-3 `combine48c3` pattern, generic).
   **Carrier-design question (M22-slot identification / JOINT recognition) → genm-recstep on-call.**
3. **#136 per-z N2b+shear+peel** `resolvedShiftRG_le`: generalize `RouteMSchurCorank3.resolvedShiftR2c3_le`
   (lines 601-649) — the shifted resolved-form, swapping its `core_T_peel_le_ae_c3` → `core_T_peel_le_ae_G`,
   `schurResid2_translate_le` → `schurResidG_translate_le`, `coreSchur2Val` → `coreSchurGenVal`.
4. **#137 assembly** `schurRatioResidGen_mid`: pivot-WLOG + carve (zEG) + chain #136 + the outer rest-box
   volume bound. Mirror corank-3's `matBox3_chart_lt_top` inner half but generic.

## Mathlib idioms (banked, apply here)
- `MeasurableEquiv.sumPiEquivProdPi`/`piCongrLeft`/`arrowCongr'` + `volume_measurePreserving_*` for the
  carving reshape (CONFIRMED v4.29; the canonical `RouteMSchurGenCover` uses the same).
- The opaque-`Fin (r-1)`-width `have`+`exact` recipe (`lean/CLAUDE.md`) for entrywise identities at
  dependent widths; `⟨0, by omega⟩` (with `hr : 3 ≤ r`) for `Fin (r-1)` indices.
- `MvPolynomial.ae_eval_ne_zero` + `MvPolynomial.measurableSet_zeroSet` for #134.

## Closure
Closing `schurRatioResidGen_mid` → `schurRatioResidGen` → `schurRatioResidGen_mid`'s consumers
(`schur_matBoxG_chart_lt_top` → `schurCoreGen_firing` → `schurRecStep_four`) all go sorry-free →
`schurGen_lt_top_modulo_recStep` closes R1-UPPER entirely. Then AUDIT (force `#print axioms`
clean-three, statement-card → `reviewed`).
