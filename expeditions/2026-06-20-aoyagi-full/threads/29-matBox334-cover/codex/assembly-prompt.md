<task>
I am closing the LAST `sorry` in a Lean 4 + Mathlib (v4.29) measure-theory proof: the per-chart
finiteness `matBox334_chart_lt_top`. I want you to VET my proposed decomposition into sub-lemmas
and find the cheapest sound assembly, BEFORE I invest in the long change-of-variables. I am NOT
asking for Lean code — I want the math architecture audited and the highest-risk step named.

## The exact goal (after I rewrite |det| = |y p|^8)

For `p : Fin 9`, `2 < c' < 4`:
```
∫⁻ y in (chartDomOn univ p \ pivotZeroOn p),
    ENNReal.ofReal (|y p|^8)
      * flatBox334.indicator (gFlat334 c') (pivotBlowupOn univ p y)
  < ⊤
```

## Definitions (all banked / proved)
- `y : Fin 9 → ℝ` is the FLATTENED 3×3 matrix A0 (`matToFlatEquiv 3 3 : (Fin 3→Fin 3→ℝ) ≃ᵐ (Fin 9→ℝ)`, MP).
- `chartDomOn univ p = {y | ∀ k ≠ p, |y k| ≤ 1}` (only the 8 off-pivot RATIOS bounded; `y p` is FREE).
- `pivotZeroOn p = {y | y p = 0}`.
- `pivotBlowupOn univ p y = fun i => if i=p then y p else y p * y i` (radial blowup; pivot coord = scale `y p`).
- `flatBox334 = {y : Fin 9→ℝ | ∀ i, |y i| ≤ 1}` (the flattened A0-box [-1,1]^9).
- `gFlat334 c' y = ∫⁻ A1 in matBox 3 4 1, ofReal (frobSq (rmatMul (unflatten y) A1)^{-c'})`
  where `unflatten = (matToFlatEquiv 3 3).symm`, `matBox 3 4 1 = [-1,1]^{3×4}`,
  `frobSq M = ∑ᵢⱼ Mᵢⱼ²`, `rmatMul X Y i j = ∑ₖ XᵢₖYₖⱼ`.

## BANKED lemmas I can use (all sorry-free):
1. `flatBox334_blowup_mem_iff p y (hy : y ∈ chartDomOn univ p)`:
   `pivotBlowupOn univ p y ∈ flatBox334 ↔ |y p| ≤ 1`. (indicator decouples to pure radial.)
2. `gFlat334_blowup_radial c' p y`:
   `gFlat334 c' (pivotBlowupOn univ p y) = ∫⁻ A1 in matBox 3 4 1, ofReal ((y p)^2 * frobSq (Rmat334 p y · A1))^{-c'})`,
   where `Rmat334 p y = unflatten (fun i => if i=p then 1 else y i)` (the 3×3 angular matrix, pivot entry = 1, other entries = the ratios `y_k`).
3. `frobSq_angularR_ge (b0 b1 g0 g1 d00 d01 d10 d11 : ℝ) (hg0: g0²≤1)(hg1: g1²≤1) (A1)`:
   `(1/5)*((∑ⱼ (A1 0 j + (b0*A1 1 j + b1*A1 2 j))²) + frobSq(rmatMul (!![d00,d01;d10,d11]) (fun k j => A1 k.succ j)))
     ≤ frobSq (rmatMul (angularR b0 b1 g0 g1 d00 d01 d10 d11) A1)`.
   Here `angularR` is the 3×3 matrix `[[1,b0,b1],[g0, d00+g0 b0, d01+g0 b1],[g1, d10+g1 b0, d11+g1 b1]]`
   — pivot (0,0)=1, top row (1,b0,b1), left col (1,g0,g1), lower-right RAW block = Δ + γβ
   (so the "de-shift" d = raw - γβ is built INTO `angularR` already: you pass d00..d11, it adds g*b).
   Crucially the RHS = `frobSq(R·A1)` for THIS pivot-(0,0) `R`.
4. `radialAxis334_lt_top c' (hc': c' < 9/2)`: `∫⁻ a in Set.Icc (-1) 1, ofReal (|a|^{8-2c'}) < ⊤`.
5. `resolved334_box_lt_top (K) (hK:0<K) (c') (2<c'<4)`:
   `∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K, ∫⁻ T in morseBox 4 K, ofReal ((∑ᵢ Tᵢ² + frobSq(rmatMul Δ S))^{-c'}) < ⊤`.
6. `rmatMul_angularR_eq`: `rmatMul (angularR ...) A1 = lgammaShear g0 g1 (schurNF b0 b1 d00 d01 d10 d11 A1)`
   (exact). `frobSq_lgammaShear_ge`: `(1/5) frobSq M ≤ frobSq (lgammaShear g0 g1 M)` for `g²≤1`.
   `frobSq_schurNF_eq`: `frobSq(schurNF ...) = (∑ⱼ Tⱼ²) + frobSq(Δ·S)` with `Tⱼ = A1 0 j + (b0 A1 1 j + b1 A1 2 j)`, `Δ=!![d00,d01;d10,d11]`, `S = A1 rows 1,2`.

## The CRITICAL math obstacle I have already found (please confirm/correct)
The pointwise bound `ofReal(frobSq(R·A1)^{-c'}) ≤ ofReal(((1/5)·Q)^{-c'})` where `Q = ∑Tⱼ²+frobSq(Δ·S)`
is FALSE at the zero set: when `Q=0` but `frobSq(R·A1)>0`, RHS = ofReal(0^{-c'}) = 0 (Real.rpow 0 neg = 0)
but LHS > 0. HOWEVER `frobSq(R·A1) = frobSq(lgammaShear g0 g1 (schurNF)) = 0 ⟺ schurNF = 0 ⟺ frobSq(schurNF) = Q = 0`
(lgammaShear is invertible / det 1). So the zero sets COINCIDE, and the ENNReal pointwise bound
`ofReal(frobSq(R·A1)^{-c'}) ≤ ofReal(((1/5)·Q)^{-c'})` HOLDS EVERYWHERE: on {Q>0} antitone-rpow, on {Q=0}
LHS = ofReal(0^{-c'}) = 0 = RHS. Is this reasoning correct? Is the cleanest Lean route a helper
`(0 ≤ B) → (B ≤ A) → (B = 0 → A = 0) → (0 < c') → ofReal(A^{-c'}) ≤ ofReal(B^{-c'})`?

## My proposed assembly (PLEASE VET each step + the box bookkeeping)
Step A (radial separation). On `D_p = chartDomOn univ p \ pivotZeroOn p`:
  integrand = `ofReal(|y p|^8) * 1_{|y p|≤1} * ∫_{A1} ofReal((y p)^2·frobSq(R·A1))^{-c'}`
            = `ofReal(|y p|^{8} · (y p²)^{-c'}) * 1_{|y p|≤1} * ∫_{A1} ofReal(frobSq(R·A1)^{-c'})`
  i.e. pull the radial `(y p²)^{-c'} = |y p|^{-2c'}` OUT of the A1-integral (homogeneity), giving
  `|y p|^{8-2c'} · 1_{|y p|≤1} · J(ratios)` where `J(ratios) = ∫_{A1} ofReal(frobSq(R(ratios)·A1)^{-c'})`.
  Then reindex `Fin 9 → ℝ ≃ ℝ × (Fin 8 → ℝ)` (pivot axis × the 8 ratios) and TONELLI:
  `I_p = (∫_{a∈[-1,1]} |a|^{8-2c'}) · (∫_{ratios ∈ [-1,1]^8} J(ratios))`.
  Q: Is this Tonelli factorization the right move, given `J` does NOT depend on `y p` (only ratios)
  and the indicator depends ONLY on `y p`? Any measurability subtlety with the reindex of `Fin 9`
  (which coordinate is `p`)? Is `MeasurableEquiv.piFinSuccAbove`/`piSplitAt` the tool, or
  `(Equiv.funSplitAt p)`? I worry the radial coordinate `p` is in the MIDDLE, not at index 0.

Step B (the ratio integral). `∫_{ratios∈[-1,1]^8} J(ratios)` where the 8 ratios are
  `(b0,b1,g0,g1,raw00,raw01,raw10,raw11)` (top-row, left-col, lower-right-raw of R). I claim:
  `J(ratios) ≤ ofReal((1/5)^{-c'}) · ∫_{A1∈matBox 3 4 1} ofReal((∑Tⱼ² + frobSq(Δ·S))^{-c'})`
  with `Δ = !![raw00 - g0 b0, raw01 - g0 b1; raw10 - g1 b0, raw11 - g1 b1]`, `T = A1row0 + β·S`, `S = A1 rows 1,2`.
  I invoke `frobSq_angularR_ge` with `d = raw - γβ`, so its `angularR ...` = my R. Confirm
  this de-shift is the right way to invoke it so its RHS is exactly `frobSq(R·A1)`.

Step C (the joint (ratios × A1) reparametrization into resolved form). After Step B:
  `∫_{ratios}∫_{A1} (∑Tⱼ²+frobSq(Δ·S))^{-c'}`. The integrand depends on: `g0,g1` NOT at all (dropped),
  `b0,b1` via `T`, `raw` via `Δ` (through d=raw-γβ), and `A1` via `T,S`. So `∫_{g0,g1∈[-1,1]^2}` is a
  FINITE measure factor (vol 4). Then for fixed `b,g`: change variables `raw ↦ Δ = raw - γβ` (translation,
  MP, `[-1,1]^4 → [-2,2]^4 ⊆ [-3,3]^4`); and in A1 change `A1row0 ↦ T = A1row0 + β S` (translation per
  fixed S, MP, `[-1,1]^4 → [-3,3]^4`), `S = A1rows1,2 ∈ [-1,1]^{2×4} ⊆ matBox 2 4 3`. Net:
  `≤ vol([-1,1]^2)·∫_{Δ∈[-2,2]}∫_{S∈[-1,1]}∫_{T∈[-3,3]} (∑Tⱼ²+frobSq(Δ·S))^{-c'} ≤ vol·resolved334_box_lt_top 3`.

## THE QUESTIONS
Q1. Is Step A's Tonelli-with-the-pivot-in-the-middle the right structure, or is there a cleaner way to
    separate the radial axis without a `Fin 9 ≃ ℝ × Fin 8` reindex headache? (e.g. integrate over the
    whole `Fin 9 → ℝ` with the indicator folded in, then a 1-coordinate marginal?)
Q2. Is the zero-set-coincidence fix (frobSq(lgammaShear M)=0 ⟺ frobSq M=0) the correct & cheapest way to
    get the everywhere ENNReal pointwise bound? Any simpler route I'm missing (e.g. bound on {Q>0} and
    show {Q=0} ratio-slice is the relevant null set — but that seems HARDER)?
Q3. Step C is the long pole: a 3-fold translation change-of-variables (raw↦Δ, A1row0↦T) nested with the
    g-factor and S. Is this the cheapest sound route? Or is there a way to do the WHOLE (ratios×A1)→(Δ,S,T)
    as ONE measure-preserving-up-to-box-enlargement map and a single domain-enlargement `lintegral_mono_set`?
    What is the single highest-risk bookkeeping error here?
Q4. Am I over-integrating or under-integrating anywhere? In particular the g0,g1 ratios: they enter R but
    NOT the resolved integrand Q — is dropping them to a finite vol-factor sound (the bound `frobSq_angularR_ge`
    is uniform in g for g²≤1, so yes the per-ratio J-bound is uniform — confirm)?
</task>

<output_contract>
Terse. Answer Q1–Q4 each in 2-5 sentences, SOUND/FLAWED verdict first. Then ONE paragraph: the single
cheapest sound overall assembly you'd recommend (which sub-lemmas, in which order), and the SINGLE
highest-risk Lean step with its cheapest guard. Do not write Lean code; name Mathlib lemmas only if you
are confident they exist at v4.29.
</output_contract>

<grounding_rules>
- Distinguish verified-from-given vs inferred. If a claimed banked lemma can't support a step, say so.
- Do not invent Mathlib lemma names. If unsure a lemma exists, say "a lemma of the shape ...".
- The goal is the CHEAPEST sound route, not the most general.
</grounding_rules>
