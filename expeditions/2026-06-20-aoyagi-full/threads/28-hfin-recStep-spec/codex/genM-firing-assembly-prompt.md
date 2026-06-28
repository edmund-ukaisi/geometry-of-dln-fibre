<task>
Lean 4 + Mathlib v4.29. I am assembling the FINAL lemma of a generic-corank matrix-integral firing. All
surrounding plumbing is GREEN; this is the one remaining sorry. I have ALREADY proven the IH-invoking
"carving core". I need the cleanest decomposition of the per-`z` assembly connecting N2b + a Morse peel to
that carving core, to avoid thrashing on intricate measure-theory.

## What I must prove (the sorry)
```
schurRatioResidGen_mid (r N : ℕ) (hN : r*r = N+1) (hr : 3 ≤ r) (hIH : SchurLowerIH 4 schurLambda r)
  (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r) (p : Fin (r*r)) (T : ℝ) (hT : 0 < T) :
  ∫_{z ∈ [-1,1]^N} innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))  < ⊤
```
where `innerSGen r c' T p y = ∫_{S ∈ matBox r 4 T} frobSq(RmatG r p y · S)^{-c'}`, and
`RmatG r p y` is the r×r angular matrix with pivot entry 1 (at matrix index `(eG r).symm p`) and the other
r²-1 entries read off the ratio vector y (all |entries| ≤ 1 since y is in the ratio box [-1,1]^N).

## Ingredients I have PROVEN (green)
- `schurResidG_translate_lt_top (r) (3≤r) (hIH) (Sh : Fin(r-1)→Fin(r-1)→ℝ) (B) (|Sh|≤B) (c'')
   (0<c'') (c''<schurLambda (r-1)) (K) (0<K) :
   ∫_{Δ∈matBox(r-1)(r-1) K}∫_{S∈matBox(r-1) 4 K} frobSq((Δ-Sh)·S)^{-c''} < ⊤`.
  (THE carving core: translation-dominates the free Δ=M22 block into the IH at radius K+B. THIS invokes hIH.)
- N2b: `schur_minorPivot_split {r p} (j) (j≤r) : ∃ c₀ c₁>0, ∀ R S, [|R|≤1]→[pivot-max j×j minor]→
   [det M11≠0] → ∃ Sc=(M22-M21 M11⁻¹ M12), det R=det M11·det Sc, c₀(frobSq(top)+frobSq(Sc·S_bot)) ≤
   frobSq(R·S) ≤ c₁(...)`. (top = (R·S) row 0..j-1; S_bot = S rows j..r-1. j=1 here.)
- `schurSplit_lintegral_le (μ) (c₀ c₁) (0<c₀) (D F : Ω→ℝ) (Z) (D,F≥0) (c₀ D≤F) (F≤c₁ D) (c') (0<c') :
   ∫_Z F^{-c'} ≤ ofReal(c₀^{-c'})·∫_Z D^{-c'}`. (the inverse-power reduction core → split form)
- `radial_morse_residual_power_le (m) (c') ((m+1)/2<c') (T) (0<T) (w) (0<w) :
   ∫_{P∈morseBox(m+1) T} (∑P_i²+w)^{-c'} ≤ ofReal(Cresid(m+1) c' · w^{-(c'-(m+1)/2)})`. (Fin 4 = m+1, m=3, thr 2)
- `frobSq_rmatMul_permG (R) (S) (σr σc : Fin r ≃ Fin r) : frobSq(R·S) = frobSq((R∘σr∘σc)·(S∘σc))`.
- `matBox_rowperm_lintegralG (T) (σc) (f) : ∫_{S∈matBox r 4 T} f S = ∫_S f(S∘σc)`. (row-perm MP on S-box)
- `MvPolynomial.ae_eval_ne_zero` + a measure-preserving flatten (for the a.e.-positivity of frobSq(Sc·S_bot)).
- `lintegral_translate_le_local`, `matBoxSq_translate_le`, Tonelli (`setLIntegral_prod`,
   `lintegral_lintegral_swap`), `MeasurableEquiv.arrowCongr'/piFinSuccAbove/sumPiEquivProdPi/piCongrLeft`.

The VALIDATED corank-3 (r=3) version of THIS lemma did the per-z work by REUSING a bespoke banked (3,3,4)
anchor `ratioResidual_lt_top` that carved the 4 M22-coords out of the 8 ratios via a hand-built reshape
`zE : (Fin 8→ℝ)≃ᵐ ((Fin 2×Fin 2→ℝ)×(Fin 4→ℝ))` + `bgShift` + `Δof_eq_zE : Sc = matOf(M22) − bgShift(rest)`,
then CoV+Tonelli over the "rest" coords + per-slice translate into core_schur2. I have NO such banked anchor
for general r; I must build the generic carving.

## The per-z chain I believe is needed (CONFIRM the decomposition + flag the hardest sub-step)
For each z: pivot-normalize R(z) to R' (pivot at (0,0)) via `frobSq_rmatMul_permG` + `matBox_rowperm_lintegralG`.
N2b j=1 on R' gives Sc(z) (= (r-1)×(r-1)) and `frobSq(R'·S) ≥ c₀(frobSq(top)+frobSq(Sc(z)·S_bot))`.
`schurSplit_lintegral_le` ⟹ `∫_S frobSq(R'·S)^{-c'} ≤ c₀^{-c'} ∫_S (frobSq(top)+frobSq(Sc·S_bot))^{-c'}`.
top = (R'·S) row 0 reads S_0 + shear(S_bot); shear S_0↦top (translate, box-enlarge); Morse-peel Fin-4
top (thr 2) ⟹ `≤ Cresid ∫_{S_bot} frobSq(Sc(z)·S_bot)^{-(c'-2)}`. So
`∫_z innerSGen ≤ c₀^{-c'} Cresid · ∫_z ∫_{S_bot} frobSq(Sc(z)·S_bot)^{-(c'-2)}`.
THEN the carving: `Sc(z) = M22(z) − M21(z)·M12(z)`; carve the (r-1)² M22-coords + the 2(r-1) M21/M12-coords
out of z (a measure-preserving reshape `(Fin N→ℝ)≃ᵐ ((Fin(r-1)×Fin(r-1)→ℝ)×(Fin(2(r-1))→ℝ))`); Tonelli the
M21/M12 "rest" coords OUTERMOST; per fixed rest, `M22 ↦ Sc = M22 − Sh(rest)` is a translation, so
`∫_{M22∈[-1,1]^{(r-1)²}} ∫_{S_bot} frobSq(Sc·S_bot)^{-c''} ≤ schurResidG_translate_lt_top` (the free Δ=M22
box at K=1, B=1 since |Sh|≤1). The outer "rest" integral is over a bounded box ⟹ finite constant.

## QUESTIONS (answer each, ≤6 sentences)
Q1. Is this per-z chain the right decomposition, or is there a SHORTER route given I already have
    `schurResidG_translate_lt_top`? Specifically: can I AVOID the per-z N2b+peel entirely by lower-bounding
    `frobSq(R(z)·S) ≥ c₀·frobSq(Sc(z)·S_bot)` (drop the top block, ≥0) — NO wait, that undershoots the
    threshold (needs the +jp/2 peel). Confirm the peel is unavoidable here, OR give the shortest correct chain.
Q2. The CARVING reshape: what is the LOWEST-friction Lean construction of the measure-preserving
    `(Fin N → ℝ) ≃ᵐ ((Fin (r-1) × Fin (r-1) → ℝ) × (Fin (2*(r-1)) → ℝ))` that splits the ratios into the M22
    block ⊕ the M21/M12 shift coords? The ratios are indexed by `Fin (r*r) \ {pivot}` (after pivot-norm,
    matrix entries (i,j)≠(0,0)); M22 = {(i,j): i,j∈1..r-1}, M21 = {(i,0):i∈1..r-1}, M12 = {(0,j):j∈1..r-1}.
    Is `MeasurableEquiv.sumPiEquivProdPi` over an explicit index bijection `(Fin(r-1)×Fin(r-1)) ⊕ Fin(2(r-1))
    ≃ Fin N` the right tool (the corank-3 `combine48c3` pattern), and is building that index bijection the
    bulk of the work? Or is there a slicker route that keeps the matrix entries indexed by `Fin r × Fin r`
    throughout and never flattens to `Fin N` (e.g. carve directly on the angular matrix R's entries)?
Q3. The a.e.-positivity `frobSq(Sc(z)·S_bot) > 0` a.e. needed for `radial_morse_residual_power_le` (it
    requires `0 < w`). For FIXED Sc this can FAIL (Sc singular). But under the JOINT z+S_bot integral (or
    after the M22-translate so Sc=M22-Sh ranges freely), is it a.e.-positive? The corank-3 route used
    `frobSqShiftR2c3_ne_zero_ae` (a nonzero-MvPolynomial argument on the JOINT (M22,S_bot) coords AFTER the
    translate). Should I peel AFTER carving (so the Morse peel sees the free-M22 joint integral, a.e.-pos by
    MvPolynomial), or BEFORE (per-z, where positivity can fail)? Which ordering makes the a.e.-positivity clean?
Q4. Given Q3: is the cleanest ORDER (a) carve+translate FIRST (z→ free M22 = Δ), THEN N2b+peel on the
    free-Δ joint core — i.e. reduce `∫_z ∫_S frobSq(R(z)·S)^{-c'}` directly to
    `∫_{Δ free}∫_S (Morse + frobSq((Δ-Sh)·S_bot))^{-c'}` and peel there — reusing my
    `schurResidG_translate_lt_top` shape but with the Morse block still attached? Or (b) peel per-z first
    then carve? Which avoids the per-z a.e.-positivity failure and reuses `schurResidG_translate_lt_top`
    most directly?
Q5. Rank the top 2 Lean-friction risks in this assembly and give a one-line mitigation each.
</task>
<output_contract>
Answer Q1–Q5 in order. For Q4 give an explicit (a)/(b) recommendation. End with one line:
"ORDER: <carve-first|peel-first>" and "HARDEST: <the one sub-step to build first>".
</output_contract>
<grounding_rules>
Mark Mathlib lemma names CONFIRMED only if sure at v4.29, else INFERRED. Distinguish measure-theoretic
facts you're confident of from Lean-tactic guesses.
</grounding_rules>
