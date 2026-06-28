<task>
I am about to formalise (Lean 4 + Mathlib v4.29) the GENERIC per-corank firing of a matrix-integral
finiteness recursion. The corank-3 instance is CLOSED and validated; I am generalising it to arbitrary
corank r, against an ABSTRACT inductive hypothesis. I want you to red-team the proof STRUCTURE and the
DISPATCH (the case split on r and on c'), before I sink ~300 lines. Be concrete and skeptical; flag any
threshold-arithmetic error or a step that needs an ingredient I do not list.

## The contract I must inhabit (this is FIXED; I cannot change it)
```
SchurCore p r c' T :=  (∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'}) < ⊤
-- matBox r n T = [−T,T]^{r×n};  frobSq M = ∑_{i,j} M_{ij}²;  rmatMul = matrix product

SchurThreshold p lam : lam 0 = 0 ; lam r ≤ r²/2 (r≥1) ; lam r ≤ jp/2 + lam(r−j) (1≤j≤r)
SchurLowerIH p lam r :=  ∀ j, 1≤j≤r, ∀ c'', 0<c''<lam(r−j), ∀ T''>0, SchurCore p (r−j) c'' T''
SchurRecStep p lam :=
  ∀ r, SchurThreshold p lam → SchurLowerIH p lam r → ∀ c', 0<c'<lam r → ∀ T>0, SchurCore p r c' T
```
I must prove `SchurRecStep 4 schurLambda`, where `schurLambda = [0, 1/2, 2, 4, 6, 8, ...]` i.e.
`lam r = 2r−2` for r≥2 (numerically verified to satisfy SchurThreshold 4). p=4 throughout.

## Ingredients I HAVE (all proved, sorry-free, GENERIC in r unless noted)
1. `core_schur2_lt_top (c') (0<c') (c'<2) (T) (0<T) : SchurCore 4 2 c' T`  — corank-2 base, general T.
2. `schur_minorPivot_split {r p} (j) (j≤r) : ∃ c₀ c₁>0, ∀ R S, [|R_ab|≤1] → [pivot-max minor j×j] →
   [det M11 ≠ 0] → ∃ Sc:(r−j)×(r−j), Sc = M22−M21 M11⁻¹ M12 ∧ det R = det M11·det Sc ∧
   c₀·(frobSq((R·S)_top) + frobSq(Sc·S_bot)) ≤ frobSq(R·S) ≤ c₁·(…)`.
   (top = first j rows of R·S : Fin j → Fin p; S_bot = rows j..r−1 of S : Fin(r−j) → Fin p.)
3. `radial_morse_residual_power_le (m) (c') ((m+1)/2 < c') (T) (0<T) (w) (0<w) :
   ∫_{P∈morseBox(m+1) T} (∑ P_i² + w)^{−c'} ≤ ofReal(Cresid(m+1) c' · w^{−(c'−(m+1)/2)})`. (shifted Morse peel)
4. `radial_morse_dominates_absZ_lt_top {m} (μ) (c') (c'<(m+1)/2) (0≤c') (Tp) (0<Tp) (W) (W≥0) (Z) (μZ<⊤)
   : ∫_{z∈Z} ∫_{P∈morseBox(m+1) Tp} (∑ P_i² + W z)^{−c'} < ⊤`. (UNSHIFTED Morse terminal over abstract Z)
5. `radial_aAxis_divisor_lt_top (r) (1≤r) (T) (0<T) (c') (c'<r²/2) :
   ∫_{[−T,T]} |a|^{(r²−1)−2c'} < ⊤`. (radial a-axis divisor)
6. `radialDelta_loss_factor {r p} (a) (R) (S) : frobSq((a•R)·S) = a²·frobSq(R·S)`. (degree-2 homogeneity)
7. `recStep {N} (active) (p) (p∈active) (L) (measurable L) (h) :
   ∫_{x∈L} h = ∑_{q∈active} ∫_{x∈chartDomOn active q \ pivotZeroOn q} |det(pivotBlowupOnDeriv active q x)|·
   L.indicator h (pivotBlowupOn active q x)`. (the argmax-entry cover on Fin N)
8. `pivotBlowupOnDeriv_det {N} (active) (p) (p∈active) (x) : det(pivotBlowupOnDeriv active p x) =
   (x p)^{active.card − 1}`. (so on Fin(r²) with active=univ, |det| = |x p|^{r²−1}.)
9. measure-preserving flatten `(Fin r → Fin r → ℝ) ≃ᵐ (Fin(r·r) → ℝ)`, box↔box; row-perm MP on the S-box;
   `piFinSuccAbove` row/coord splits; `lintegral_translate_le_local` (translate box-enlarge); all generic.

The corank-3 CLOSED proof did exactly: flatten Δ to Fin 9 → recStep 9-chart cover → per chart radial pull-out
(|det|=|y_p|^8, radialDelta gives |y_p|^{8−2c'}) → piFinSuccAbove splits pivot axis a from the 8 ratios →
a-axis divisor finite (c'<9/2) × ratio-residual finite. The ratio residual = ∫_{ratios} innerS(c',R) where
innerS = ∫_S frobSq(R·S)^{−c'}, R the angular matrix (pivot entry 1, |entries|≤1). innerS finite via:
N2b j=1 split → top Morse(Fin p=4) peel at threshold 2 → shifted residual frobSq(Sc·S_bot) at c''=c'−2 →
translation-dominate M22↦Sc into a box → corank-2 core. The corank-3 inner heart REUSED the banked (3,3,4)
anchor; for general r I must instead invoke the ABSTRACT SchurLowerIH at corank r−1.

## My proposed GENERIC dispatch (red-team THIS)
`schurRecStep_four`: intro r, hlam, hIH, c', hc0, hclt (c'<lam r), T, hT. Then:
- **r = 0**: vacuous (c' < lam 0 = 0 contradicts 0 < c').
- **r = 1**: Morse leaf. SchurCore 4 1 c' T = ∫_{Δ∈box 1 1}∫_{S∈box 1 4} (Δ₀₀²·∑(S₀ⱼ)²)^{−c'}, c'<1/2.
  Plan: this is a product of a 1-D a-axis divisor in Δ₀₀ (degree from |Δ₀₀|^{−2c'}, integrable since
  2c'<1) times ∫_S (∑S₀ⱼ²)^{−c'} (a Fin-4 Morse block, finite since c'<1/2<2). Is this the cleanest, or
  should I fold r=1 into the generic firing (it can't — IH at corank 0 needs c''<lam 0=0)?
- **r = 2**: discharge DIRECTLY from `core_schur2_lt_top` (general T). (c'<lam 2 = 2 ✓.)
- **r ≥ 3**: the GENERIC firing. flatten Δ→Fin(r²); recStep r²-chart cover; per chart radial pull-out
  |det|=|y_p|^{r²−1}, radialDelta → |y_p|^{(r²−1)−2c'}; piFinSuccAbove splits pivot axis from r²−1 ratios;
  a-axis divisor finite (need c' < r²/2 — holds since c'<lam r=2r−2 ≤ r²/2 for r≥2); ratio residual
  = ∫_{ratios} innerS(c',R). innerS finite for the angular R (pivot 1, |·|≤1) via, ON c':
    * **mid case 2 < c' < lam r = 2r−2**: N2b j=1 → top Morse(Fin 4) peel at threshold 2 (needs c'>2) →
      shifted residual at c''=c'−2 ∈ (0, lam r − 2) = (0, 2r−4) = (0, lam(r−1)) → translation-dominate the
      (r−1)×(r−1) Sc into a fixed box of radius T+B (B = the Cramer/shear shift bound) → invoke
      `hIH 1 (1≤1) (1≤r) c'' (0<c'') (c''<lam(r−1)) T'' (0<T'')` = SchurCore 4 (r−1) c'' T''. ✓
    * **subcritical case 0 < c' ≤ 2**: dominate ofReal(F^{−c'}) ≤ 1 + ofReal(F^{−3}) pointwise (F=frobSq≥0),
      reduce to the c''=3 mid case (3 ∈ (2, lam r) = (2, 2r−2) since 2r−2 ≥ 4 for r≥3). The +1 integrates
      over the finite ratio·S box.

## QUESTIONS (answer each)
Q1. Is the dispatch r=0 / r=1 / r=2 / r≥3 correct and exhaustive, with the threshold arithmetic right at
    each boundary? In particular: is r=2 forced to come from the base (not the firing) because the
    subcritical reduction's mid target c''=3 would need 3 < lam 2 = 2 (FALSE)? Is r≥3 the right cutoff for
    the firing, and does the subcritical c''=3 target sit in (2, lam r) for ALL r≥3?
Q2. The genuinely-new generic piece vs corank-3: corank-3 reused the banked anchor; I invoke the ABSTRACT
    IH. In the mid case, the residual is frobSq(Sc·S_bot) with Sc=(r−1)×(r−1) NOT a free coordinate (it is
    M22 − M21 M11⁻¹ M12, a function of R's angular entries). To invoke `SchurCore 4 (r−1) c'' T''` (a FREE
    (r−1)×(r−1) Δ-box × free (r−1)×4 S-box), I translation-dominate M22 ↦ Sc (Jac≡1, |shift|≤B). Is the
    shift bound B genuinely FINITE and angular-uniform for general r? (Sc = M22 − M21 M11⁻¹ M12, with
    j=1 so M11⁻¹ = 1/R_pivot = 1 since pivot entry = 1, M21 is (r−1)×1, M12 is 1×(r−1), all entries ≤1 in
    abs on the angular chart — so |shift_ab| = |M21_a · M12_b| ≤ 1, B=1, uniform. Confirm, and confirm the
    j=1 case makes M11 a 1×1 = [1] so M11⁻¹ = [1] exactly, no inversion subtlety.)
Q3. The S-block disjointness for the Morse peel: N2b's top block is (R·S)_top (first j=1 row of R·S, reads
    ALL of S via row 0 of R) and the residual reads Sc·S_bot (S rows 1..r−1). After the row-0 shear
    S_0 ↦ S_0 + (shear), are the top Morse block (Fin p=4 free) and the residual genuinely Tonelli-disjoint
    so I get ∫_{S_bot}∫_{S_0-shifted}(∑(S_0)² + frobSq(Sc·S_bot))^{−c'} — i.e. does the corank-3 pattern
    (`schurSplitD_eq` + shear-peel) generalise verbatim with the top block being a Fin p Morse block and the
    residual depending only on S_bot? Or does j=1 at general r entangle more S-rows than the corank-2/3 case?
Q4. Is there a SIMPLER route for the mid case that AVOIDS the explicit shear/translation bookkeeping —
    e.g. bounding frobSq(R·S) ≥ c₀·frobSq(Sc·S_bot) (drop the top block entirely, it's ≥0) and then
    directly translation-dominating into the free IH core at exponent c' (NOT c'−2)? That would need
    c' < lam(r−1), i.e. 2r−2 < 2(r−1)−2 = 2r−4, FALSE. So dropping the top block undershoots — the +jp/2
    Morse gain is load-bearing and the shifted peel is unavoidable. Confirm this, so I don't waste a tide
    on the shortcut.
Q5. Any Mathlib v4.29 friction you foresee in the GENERIC r²-chart assembly that the hardwired Fin-9
    corank-3 proof did NOT reveal (e.g. the flatten `Fin r × Fin r ≃ Fin(r·r)` measure-preserving at
    GENERIC r, the `piFinSuccAbove` split at generic r²−1 ratio count, the N2b cell-hypothesis discharge
    `|R_ab|≤1` + pivot-max-minor at generic r)? Rank the top 2 risks.
</task>

<output_contract>
Answer Q1–Q5 in order, each ≤ 8 sentences. For Q1 give an explicit PASS/FAIL on the dispatch + corrected
boundaries if any. For Q5 rank the top 2 Lean-friction risks with a one-line mitigation each. End with a
single line: "VERDICT: REACHABLE-PLUMBING" or "VERDICT: HOLE AT <step>".
</output_contract>

<grounding_rules>
Mark any Mathlib lemma name you assert as CONFIRMED only if you are sure it exists at v4.29; otherwise
mark it INFERRED. Distinguish arithmetic you verified from arithmetic you are taking on trust.
</grounding_rules>
