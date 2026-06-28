<task>
Lean 4 + Mathlib v4.29. I am proving the per-corank inductive STEP of a finiteness
recursion (R1-UPPER). I want the cleanest PROOF ARCHITECTURE before building, given
that a validated corank-3 INSTANCE already exists (I generalize it to arbitrary
corank r). This is an architecture/sequencing question, not a tactic question.

## The target (general corank r, general box radius T, p = 4 columns)
Prove `SchurRecStep 4 schurLambda`:
  ∀ r, SchurThreshold 4 schurLambda → SchurLowerIH 4 schurLambda r →
    ∀ c', 0<c' → c'<schurLambda r → ∀ T, 0<T → SchurCore 4 r c' T
where
  SchurCore p r c' T := ∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(rmatMul Δ S)^{−c'} < ⊤
  SchurLowerIH p lam r := ∀ j, 1≤j → j≤r → ∀ c'', 0<c'' → c''<lam(r−j) → ∀ T'', 0<T'' →
                            SchurCore p (r−j) c'' T''   -- the abstract general-T lower IH (a HYPOTHESIS)
  schurLambda = closed λ_{r,4} = {0; ½; 2r−2 (r≥2)}; the peel threshold is jp/2 = 2j (p=4).

## The mechanism (the corank-3 firing, to generalize)
1. Radial-Δ cover: matBox r r T → flatten to (Fin (r²) → ℝ); cover by the r² entry-pivot
   charts (`argmaxCellOn`, general N=r², a.e. cover via `recStep`); per chart the radial
   blow-up Δ = (y_p)·R with R the angular matrix (pivot entry 1, others = y_k, |y_k|≤T),
   Jacobian |y_p|^{r²−1} (`pivotBlowupOnDeriv_det`, general N).
2. Per chart, N1 homogeneity pulls out (y_p)²: integrand = ((y_p)²·frobSq(R·S))^{−c'}.
3. N2b j=1 split (`schur_minorPivot_split {r,p} j`, GENERAL — gives c₀,c₁>0 and the
   two-sided uniform comparison frobSq(R·S) ≍ frobSq((R·S)_top, j·p entries) + frobSq(Sc·S_bot),
   Sc = M22−M21·M11⁻¹·M12, on the bounded cell |R|≤1; + det identity).
4. The radial a-axis: ∫|y_p|^{r²−1}·((y_p)²·…)^{−c'} — finite for c' < r²/2 (always, since
   c' < λ ≤ r²/2). The pivot axis factors (Tonelli) from the angular ratios.
5. Shifted Morse peel of the top j·p-block (`radial_morse_residual_power_le`, general m;
   threshold (jp)/2): leaves the residual ∫ frobSq(Sc·S_bot)^{−(c'−jp/2)}.
6. Translate M22 ↦ Sc (Jac=1, Sc into a box of radius ~T·(1+j) via the proved Cramer
   shear bound), then INVOKE THE IH: SchurLowerIH at corank (r−j), exponent c'−jp/2 <
   λ(r−j), radius ~T(1+j). The IH is abstract (a hypothesis) — I do NOT call any concrete
   lower-corank theorem.
7. Sum the r² charts (`Finset.sum` / `ENNReal.sum_lt_top`).

## What is GENERAL already (confirmed in Lean): schur_minorPivot_split {r,p,j},
argmaxCellOn {N}, recStep {N}, pivotBlowupOnDeriv_det {N}, radial_morse_residual_power_le {m}.
What is HARDWIRED to corank-3 (Fin 9, r=3, j=1): the per-chart assembly
(matBox3_chart_lt_top), the flatten (matToFlat3), the JOINT inner recognition
(ratioResidual_lt_top, reusing the unit-box (3,3,4) anchor). The corank-3 file is the
TEMPLATE; I rewrite its per-chart assembly generically in r (and general T).

## The architecture questions (rank, be decisive)
Q1. SCOPE of what I must build generically vs reuse. The corank-3 per-chart assembly
    bottoms out in the unit-box (3,3,4) anchor (ratioResidual_lt_top). In the GENERIC
    step, that bottoming-out is replaced by the ABSTRACT IH (step 6). So do I need to
    re-derive ANY of the corank-3 inner JOINT-recognition machinery, or does the generic
    step ONLY need: cover (general) + N1 pull-out + N2b (general) + a-axis monomial +
    Morse peel (general) + translate + invoke-IH? I believe the inner recognition is
    SUBSUMED by the IH. Confirm or correct.
Q2. The per-chart integrand after N2b: it's a SUM (top-block + Sc-core), and I peel the
    top block via radial_morse_residual_power_le leaving the Sc-core at shifted exponent.
    But radial_morse_residual_power_le bounds ∫(∑P² + w)^{−c'} ≤ Cresid·w^{−(c'−(m+1)/2)} —
    it needs the Sc-core `w` as a SINGLE scalar ≥0 under the Morse integral, then the
    OUTER integral over (Sc, S_bot) gives ∫ w^{−(c'−jp/2)} = the IH. Is the cleanest
    structure: Tonelli to ∫_{Sc,S_bot} [∫_{top-block} (∑P²+w)^{−c'}] ≤ ∫_{Sc,S_bot}
    Cresid·w^{−(c'−jp/2)}, then recognize the inner as SchurLowerIH? Name the Tonelli +
    measurability obligations.
Q3. The N2b two-sided comparison gives frobSq(R·S) ≍ (top + Sc-core), so
    frobSq(R·S)^{−c'} ≤ c₀^{−c'}·(top+Sc-core)^{−c'} (inverse-power flip, my
    schurSplit_integrand_le pattern). Then the (top+Sc-core)^{−c'} is what step 5/6 peel.
    Confirm this is the right entry, and whether the bounded-cell hypothesis |R|≤1 (N2b's
    precondition) holds on the argmaxCellOn chart (R = angular, pivot-normalized — entries
    ≤1 by the argmax cover?).
Q4. SEQUENCING the build: give the dependency-ordered lemma list (5–9 lemmas) for the
    generic per-corank step, each as a one-line Lean-signature sketch, marking which mirror
    a corank-3 lemma (cheap r-generalization) vs which are genuinely new. Identify the ONE
    riskiest lemma.
</task>

<output_contract>
1. Q1 verdict (one line: is the inner recognition subsumed by the IH? Y/N + why).
2. Q2: the cleanest Tonelli/peel structure + the measurability/Tonelli obligations.
3. Q3: confirm the inverse-power-flip entry + whether |R|≤1 holds on the chart.
4. Q4: the dependency-ordered lemma list (signatures), mark mirror-vs-new, name the
   riskiest. ≤ 500 words total.
</output_contract>

<grounding_rules>
Mark any Mathlib lemma name as INFERRED vs confident (I verify all). The GENERAL-vs-
hardwired facts above are OBSERVED from Lean (ground truth). If the architecture has a
genuine obstruction (e.g. the generic radial flatten at arbitrary r² is materially harder
than corank-3's Fin 9), say so explicitly rather than smoothing it.
</grounding_rules>
