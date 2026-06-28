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
