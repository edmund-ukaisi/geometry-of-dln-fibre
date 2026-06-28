# corank-3 `core_schur3_lt_top` — per-chart assembly wiring design (genm-c3wire tide)

Goal: `core_schur3_lt_top (c' : ℝ) (0<c') (c'<4) (T) (0<T)` :
`∫_{Δ∈matBox 3 3 T} ∫_{S∈matBox 3 4 T} frobSq(Δ·S)^{−c'} < ⊤`.

Banked foundation (RouteMSchurCorank3.lean, sorry-free): the 9-chart cover (`gFlat3_cover_sum`,
`matToFlat3`, `Rmat3`, `gFlat3_blowup_radial`), per-chart support (`innerS3`,
`chart_integrand_factor3`, `flatBox3_blowup_mem_iff`), and the JOINT residual-domination
(`schurResid2_translate_lt_top` : ∀ fixed Sh with |Sh|≤B, `∫_{Δ∈matBox 2 2 T}∫_{S∈matBox 2 4 T}
frobSq((Δ−Sh)·S)^{−c''} < ⊤` for c''<2; `matBox2_translate_le`).

## Route (Codex xhigh-confirmed 2026-06-28; mirrors RouteM334Hfin `resolved334_lt_top` keystone)

`matBox3_chart_lt_top` = mirror of `matBox2_chart_lt_top` for steps 1-2 (radial CoV, Jac |a|^8,
a-axis threshold 9/2), but the `hratiofin` part DIFFERS: cannot factor innerS3 as a uniform
R-independent const (innerS3 is INFINITE for singular Sc, so finiteness is genuinely JOINT over R+S).

`hratiofin` corank-3: `∫_{z∈[−1,1]^8} innerS3 c' T p (e.symm(0,z)) < ⊤` via:
1. N2b flip (`schur_minorPivot_split r=3 j=1` + `schurSplit_integrand_le`/`_lintegral_le`) UNDER ∫_z:
   `∫_z innerS3 ≤ ofReal(c₀^{−c'}) · ∫_z ∫_S D(R(z),S)^{−c'}`,
   D = frobSq((R·S)_row0) + frobSq(Sc(z)·S_bot), Sc(z)=M22(z)−Sh(z) (pivot (0,0): M11=R₀₀=1,
   Sh=M21·M12), S_bot = rows {1,2} of S.
2. JOINT peel (combine (z, S_bot) outer; like resolved334 combines (Δ,S)): translate S_row0 by the
   shear shift, then `core_T_peel_le_ae` (m=3, threshold (3+1)/2=2<c') over joint (z,S_bot):
   `∫_{(z,S_bot)} ∫_{S_row0} (∑P²+w)^{−c'} ≤ ofReal(Cresid 4 c')·∫_{(z,S_bot)} w^{−(c'−2)}`,
   w = frobSq(Sc(z)·S_bot). Needs a.e. `w>0` (R2).
3. JOINT residual recognition: `∫_{(z,S_bot)} w^{−c''}` (c''=c'−2<2), Tonelli-split z into
   (M22 4-coords)×(boundary 4-coords); per fixed boundary apply `schurResid2_translate_le` (the
   UNIFORM `_le` form, R1) ≤ const; then `∫_boundary const = const·vol`.

## RISKS (rank)
- R1 (HIGHEST): `schurResid2_translate_lt_top` is only `<⊤`. To integrate over the boundary coords
  need a UNIFORM `_le` bound. → Build `schurResid2_translate_le` : LHS ≤ `coreSchur2Val c'' (T+B)`
  (a named, Sh-independent finite constant = the value of `core_schur2`'s integral at radius T+B).
  Mirror of corank-2 `schurInner_S_bound` vs `_le`.
- R2 (MED): a.e. `frobSq(Sc(z)·S_bot) > 0`. Sc(z) nonlinear in z. → polynomial-nonvanishing
  (`MvPolynomial.ae_eval_ne_zero`) like `frobSq_core334_ne_zero_ae`, but core poly = `frobSq(Sc·S_bot)`
  in (z,S_bot) coords. Sc = M22 − M21·M12 is a degree-≤2 poly in z; nonzero at a witness slice.
  ALTERNATIVE: don't peel jointly; instead recognize FIRST (Tonelli z=(M22,bdry)) bringing it to the
  shifted form, THEN within each fixed-bdry slice the (M22,S_bot,S_row0) integral IS resolved334-shaped
  with shift — handle with schurResid2 (which internally rides core_schur2, already a.e.-clean). This
  avoids re-proving a.e.-positivity (it's inside the banked lemmas). PREFER this if R2 thrashes.
- R3 (MED): Fin 8 ≃ (Fin 4)×(Fin 4) slot bookkeeping + recognizing M22 = Rmat3 {1,2}×{1,2} sub-block
  under e.symm(0,·)∘matToFlat3.symm. → single measurable equiv `zE`, avoid ad-hoc projections.

## Key constants/thresholds
- c' ∈ (2,4) is the binding branch; c'≤2 handled by exponent monotonicity (or: the whole route works
  for 0<c'<4 if peel threshold guarded — but peel needs c'>2; for c'≤2 use core334-style direct).
  Actually simplest: the a-axis needs c'<9/2 (OK), the peel needs c'>(3+1)/2=2, the residual needs
  c'−2<2 ⟺ c'<4. For c'≤2 the inner is EASIER (Morse-dominated). Branch at c'=2 like core334_lt_top.

## LANDED (2026-06-28, genm-c3wire)

`core_schur3_lt_top (c' : ℝ)(0<c')(c'<4) : ∫_{Δ∈matBox 3 3 1}∫_{S∈matBox 3 4 1} frobSq(Δ·S)^{−c'} < ⊤`
PROVED sorry-free, `#print axioms = [propext, Classical.choice, Quot.sound]` (forced, olean-fresh).

**KEY SIMPLIFICATION vs the original design.** The genuinely-new corank-3 JOINT recognition
(N2b j=1 split → row-0 shear → M22↦Δ−Sh recognition → resolved residual) was ALREADY BANKED, sorry-free,
by the (3,3,4) anchor `RouteM334Ratiofin` (`ginnerZ_lt_top`/`resolvedZ_lt_top`/`ratioResidual_lt_top`,
the `zE`/`bgShift`/`Δof_eq_zE` slot identification feeding `resolved334_box_lt_top`). Since `Rmat3` and
`Rmat334` are DEFEQ (both `matToFlatEquiv 3 3`), `innerS3 c' 1 p y = angA1Int c' p y`, so the inner heart
`schurInner3_ratiofin_mid` at T=1 IS `ratioResidual_lt_top` verbatim (a 1-line reuse). The bespoke
infrastructure I built (`schurResid2_translate_le`, `resolvedShiftR2c3_le`, `frobSqShiftR2c3_ne_zero_ae`,
`core_T_peel_le_ae_c3`, the `…R2c3` polynomial-null machinery) is a SELF-CONTAINED N2b-route alternative,
banked sorry-free but NOT on the live `core_schur3_lt_top` path (the (3,3,4)-reuse path is shorter).
Imported `RouteM334Ratiofin` (now sorry-free; its file-level sorries in Skeleton/RouteMSchur/RouteMRecursion
do NOT taint `core_schur3_lt_top` — `#print axioms` confirms).

**CAVEAT (named honestly): the result is at the UNIT box (T = 1), not general T.** The corank-2
`core_schur2_lt_top` is general-T; this is T=1 (the operative `routeMBaseNbhd = (−1,1)` radius). General-T
= `T^{21−4c'}·(T=1)` by box-scaling, but Mathlib v4.29 has NO `lintegral_comp_smul` for the matrix space,
and the (3,3,4) reuse (`ratioResidual_lt_top`) is radius-1-baked (the angular z-box is always [−1,1]^8; only
the S-box radius differs). ROADMAP: build the matrix-space `lintegral_comp_smul` (or radius-T versions of
the (3,3,4) `Jint`/`Ginner` route) to lift to general T. The c'≤2 range IS covered (exponent-bump to c''=3).

## GENERAL-T LIFT LANDED (2026-06-28, genm-c3wire)

The T=1 caveat is now CLOSED. Added (all sorry-free, `#print axioms = [propext, Classical.choice, Quot.sound]`):
- `lintegral_matBox_smul (r n)(T)(0<T)(g)(hg) : ∫_{matBox r n T} g = ofReal(T^(r*n)) · ∫_{matBox r n 1} g(T•·)`
  — the REUSABLE matrix-space radius change-of-variables. Built from `Measure.map_addHaar_smul` (volume on
  `Fin r → Fin n → ℝ` is addHaar, `finrank = r*n`) + `lintegral_map` + `lintegral_smul_measure`, via the
  indicator form. The shared dependency genm-recstep consumes for its own radius lifts.
- `smul_mem_matBox_iff` (T•Y ∈ matBox r n T ↔ Y ∈ matBox r n 1), `frobSq_rmatMul_smul_both`
  (degree-4 homogeneity `frobSq((T•Δ)·(T•S)) = T⁴·frobSq(Δ·S)`).
- `core_schur3_lt_top (c')(0<c')(c'<4)(T)(0<T)` — the BARE name is now GENERAL-T (symmetry with
  `core_schur2_lt_top`); the former unit-box is demoted to `core_schur3_lt_top_unitBox`. General-T
  `= ofReal(T^{21−4c'})·(unit box)`: scale the Δ-box (outer, Jac T^9) then the S-box (inner, Jac T^12) via
  the primitive, pull `T^{−4c'}` out of the integrand by the degree-4 homogeneity, the radius factor
  `T^{21−4c'}` is a finite constant ⟹ finiteness from the unit box.
