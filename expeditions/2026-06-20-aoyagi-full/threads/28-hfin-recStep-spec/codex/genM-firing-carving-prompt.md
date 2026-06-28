<task>
FOLLOW-UP design question (Lean 4 + Mathlib v4.29). You confirmed the corank-r firing dispatch is
REACHABLE-PLUMBING. Now I need the cleanest GENERIC organization of ONE step that the validated corank-3
proof did BESPOKELY and which I must generalize. Pick the organization that minimizes Lean cast-friction.

## Setup
Per radial chart, the angular matrix R : Fin r → Fin r → ℝ has pivot entry R_pp = 1 (p a chosen entry),
all |R_ab| ≤ 1. R's entries OTHER than the pivot are the FREE "ratio" coordinates z ∈ [−1,1]^{r²−1}.
After N2b (j=1, pivot normalized to (0,0)) the residual core is frobSq(Sc · S_bot) where
  Sc = M22 − M21·M11⁻¹·M12,  M11=[1] (1×1, =R_00=1), M21=(r−1)×1 col, M12=1×(r−1) row, M22=(r−1)×(r−1),
all sub-blocks of R, i.e. functions of the ratios z. So Sc = M22 − (col·row), a (r−1)×(r−1) matrix whose
entries are z-coordinates minus products of z-coordinates.

To invoke the IH `SchurCore 4 (r−1) c'' T'' = ∫_{Δ∈box (r−1)(r−1)}∫_{V∈box (r−1) 4} frobSq(Δ·V)^{−c''}`
(a FREE (r−1)×(r−1) Δ-box × free (r−1)×4 V-box), I want to dominate
  ∫_{z∈[−1,1]^{r²−1}} ∫_{S_bot∈box (r−1) 4 T} frobSq(Sc(z)·S_bot)^{−c''}
by a constant × the IH integral. The corank-3 proof did this via a BESPOKE measure-preserving reshape
`zE` that carves the 4 ratio coords forming M22 out of z, plus `bgShift` (the fixed shift from the OTHER
ratios) so that, holding the non-M22 ratios fixed, `M22 ↦ Sc = M22 − bgShift` is a pure translation
(Jac≡1), then box-enlarge M22 from [−1,1]^4 to [−(1+B),1+B]^4 and apply the corank-2 base.

## The two candidate generic organizations (pick + justify the LOWER-friction one)
**(A) Generalize the `zE`/`bgShift` carving.** Build a measure-preserving equiv
`(Fin(r²−1) → ℝ) ≃ᵐ (Fin (r−1)² → ℝ) × (Fin (r²−1 − (r−1)²) → ℝ)` splitting the ratios into the M22
block and the rest; per fixed "rest", the M22↦Sc map is a translation by a shift bounded by B=1
(since M21,M12 entries ≤1, shift entry = M21_a·M12_b, |·|≤1). Then `lintegral_translate_le_local`
box-enlarges M22's [−1,1] box to [−2,2], and the IH (radius 2) closes it. The carving equiv is the
cast-heavy generic construction.

**(B) Avoid carving: dominate over the FULL free (r−1)×(r−1) Δ-box from the START.** Reorganize so that
instead of integrating Sc(z) over the ratio box, I directly bound
  ∫_{z} ∫_{S_bot} frobSq(Sc(z)·S_bot)^{−c''}  ≤  C · ∫_{Δ∈box(r−1)(r−1) Tg}∫_{S_bot} frobSq(Δ·S_bot)^{−c''}
by a SINGLE translation/inclusion argument WITHOUT first splitting z into M22 ⊕ rest. The idea: the map
sending (z, S_bot) ↦ (Sc(z), S_bot) pushes the ratio-box measure forward to something dominated by
Lebesgue on the Δ-box (since Sc = M22 − col·row and M22 is a coordinate-projection of z, the pushforward
of [−1,1]^{r²−1} under z ↦ Sc lands in [−2,2]^{(r−1)²} with bounded density ≤ 1 after integrating out the
non-M22 ratios). Is there a clean Mathlib lemma making "∫ f(Sc(z)) over z ≤ ∫ f over the Δ-box" hold
DIRECTLY (a Tonelli over the non-M22 ratios + per-slice translation), so I never build an explicit carving
equiv — I just Tonelli-order the non-M22 ratios outermost and translate the M22 ratios inside?

## QUESTIONS
Q1. Which of (A)/(B) is LOWER Lean-friction at v4.29? (B) seems to be just "(A) without naming the equiv —
    Tonelli the non-M22 ratios out, translate M22 inside per-slice". Is (B) genuinely simpler, or does the
    per-slice translate STILL need a measurable-equiv carving to even state the inner M22-integral?
Q2. The cleanest way to state "the (r−1)² M22-ratio coordinates" as a sub-tuple of the r²−1 ratios in Lean.
    Is `MeasurableEquiv.piCongrLeft` / `sumPiEquivProdPi` over an explicit `Fin (r−1)² ⊕ Fin K ≃ Fin(r²−1)`
    the right tool (the corank-3 `combine48c3` pattern), or is there a less cast-heavy approach (e.g. index
    the ratios by `Fin r × Fin r \ {pivot}` and project the M22 sub-block `{1..r−1}×{1..r−1}` directly)?
Q3. CRITICAL alternative — can I SIDESTEP the whole carving by choosing the radial cover to blow up ONLY
    the pivot ENTRY (not all r² entries), leaving M22 as a FREE block of the ORIGINAL Δ (radius T, not
    angular)? I.e. cover matBox r r T by charts where ONE entry is max-modulus, radial-blow-up makes that
    entry the pivot=1 with the rest of its ROW/COL as bounded ratios, but keep the M22 block (disjoint from
    the pivot row/col) as FREE Δ-coordinates over [−T,T]. Then M22 is already a free box and Sc = M22 −
    (bounded shift) needs only a translation, NO carving. Does this work — does N2b's uniform-constant
    bound survive when only the pivot row+col are bounded (≤1 after the ratio normalization) but M22 is
    free over [−T,T] (NOT ≤1)? Or does N2b REQUIRE all entries ≤1 (the complete-pivoting cell), forcing
    the full-Δ blow-up and hence the carving?
Q4. If Q3's partial-blow-up breaks N2b's uniform constant, is the carving (A)/(B) genuinely UNAVOIDABLE,
    making it the one real generic-construction cost (~80-120 Lean lines for the MP carving equiv + the
    box-enlarge + the translate)? Give a yes/no + the smallest sharp statement of what must be built.
</task>

<output_contract>
Answer Q1–Q4 in order, each ≤ 7 sentences. End with one line:
"ROUTE: <A|B|Q3-partial-blowup>" naming the lowest-friction route, and
"CARVING: <UNAVOIDABLE|AVOIDABLE-via-Q3>".
</output_contract>

<grounding_rules>
Mark Mathlib lemma names CONFIRMED only if sure at v4.29, else INFERRED. Distinguish a measure-theoretic
fact you are confident of from a Lean-tactic guess.
</grounding_rules>
