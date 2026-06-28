<task>
Lean 4 + Mathlib v4.29. I must reach a DECISIVE scope verdict before building a
finiteness recursion's per-corank step (`SchurRecStep`). The question is purely
about T-flow (integration-box radius), not Lean tactics.

## The objects
- `SchurCore p r c' T := ∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'} < ⊤`
  (matBox a b T = entrywise [−T,T] box; p = column count = 4; r = corank).
- Threshold `λ(r,p) = min(r²/2, min_j(jp/2 + λ(r−j,p)))`; λ(2,4)=2, λ(3,4)=4.
- The recStep at corank r: cover the Δ-box by r² radial pivot charts (Δ = a·R, a∈[−T,T]
  radial, R angular); N2b minor-pivot Schur split peels a top jp-dim Morse block
  (threshold jp/2); the residual is the corank-(r−j) core with Sc = M22 − M21·M11⁻¹·M12
  the Schur complement; translation-domination M22↦Sc (Jac=1) puts Sc into a fixed
  box; invoke the IH (lower core) at the reduced corank.

## What I have, with EXACT box radii (from the validated corank-3 file)
1. corank-2 BASE `core_schur2_lt_top (c')(0<c')(c'<2)(T)(0<T)`: **GENERAL-T**. Proven.
2. The deep inner engine `resolvedShiftR2c3_le (Sh)(B)(hB:|Sh|≤B)(K)(0<K)(c')(2<c'<4)`:
   bounds `∫_{Δ∈box 2 2 K}∫_{S∈box 2 4 K}∫_{T∈morseBox 4 K}(∑T²+frobSq((Δ−Sh)·S))^{−c'}`
   ≤ Cresid·coreSchur2Val(c'−2)(K+B). **GENERAL-K** (it invokes core_schur2 at K+B).
3. `schurResid2_translate_lt_top (Sh)(B)(hB)(c'')(0<c''<2)(T)(0<T)`: the corank-2
   residual `∫_{Δ∈box 2 2 T}∫_{S∈box 2 4 T} frobSq((Δ−Sh)·S)^{−c''}` < ⊤, via
   core_schur2 at T+B. **GENERAL-T**.
4. BUT `core_schur3_lt_top (c')(0<c')(c'<4)`: **UNIT BOX ONLY** (matBox 3 3 1,
   matBox 3 4 1, no T param). Its chain (`matBox3_chart_lt_top` hardwires T:=1;
   `ratioResidual_lt_top`; `schurInner3_ratiofin`) reuses a BANKED (3,3,4) anchor
   `resolved334_box_lt_top` at the UNIT S-box. The card says general-T is roadmapped
   (needs a matrix `lintegral_comp_smul` box-scaling).

## The decision (be decisive)
My `SchurRecStep` contract is GENERAL-T (`SchurCore p r c' T, ∀T`); the IH
(`SchurLowerIH`) supplies the lower core at general T''. Two readings:

(A) The recStep, proved GENERICALLY (radial CoV + N2b + peel + translate + IH),
    invokes the IH at a general radius (≈ T+B from the angular R-box + Cramer shift),
    and the GENERAL-T building blocks (#1,#2,#3 above) supply everything — so
    core_schur3_lt_top's T=1 pin is IRRELEVANT (it's a validation instance of the
    mechanism, NOT a lemma the recStep invokes). The recStep is buildable at
    general-T NOW, base = core_schur2 (general-T), no box-scaling sub-gap.

(B) The generic per-corank step cannot avoid re-deriving the corank-3-style
    per-chart cover (radial blow-up Jacobian, the JOINT recognition) which is only
    available at T=1 (via the (3,3,4) anchor), so a general-T recStep REQUIRES the
    deferred matrix lintegral_comp_smul box-scaling first — a genuine sub-gap to
    STOP and report.

Which reading is correct? The crux: when the recStep covers `matBox r r T` (general
T) by radial charts and peels, is the residual lower-corank core invocable through
the GENERAL-T building blocks (#1–#3), OR does the per-chart radial-CoV + JOINT
recognition machinery itself only exist at T=1 (forcing #4's box-scaling)?

Consider specifically: the radial blow-up of `matBox r r T` vs `matBox r r 1` —
does the angular-R box and the per-chart integrand factorization (the |a|^{r²−1}
Jacobian × angular inner) carry a clean T-dependence (e.g. an overall T^power × the
T=1 inner), so that a SINGLE scalar box-rescale at the TOP (Δ ↦ T·Δ, one
lintegral_comp_smul on the r×r matrix space) reduces general-T to T=1 — making the
box-scaling a ONE-TIME top-level lemma, NOT a per-corank obstruction?
</task>

<output_contract>
1. VERDICT: (A) or (B), stated in one line up front.
2. The crux argument: trace the T through ONE corank-r recStep firing — name where
   T enters the residual radius and whether #1–#3 (general-T) cover it, or whether
   the per-chart machinery is T=1-bound.
3. If (B): is the box-scaling a ONE-TIME top-level Δ↦T·Δ rescale (clean) or a
   per-corank cost? Give the cleanest reduction.
4. If (A): confirm the base case + IH suffice with no box-scaling, and name the
   general-T radius the IH is invoked at.
Be decisive. ≤ 400 words.
</output_contract>

<grounding_rules>
This is a math/scope question — reason from the structure I gave. Mark any Mathlib
lemma name you cite as INFERRED vs confident. The radii facts (#1–#4) are OBSERVED
from the Lean files (ground truth); reason from them.
</grounding_rules>
