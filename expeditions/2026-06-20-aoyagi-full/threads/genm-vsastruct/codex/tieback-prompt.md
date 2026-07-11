<task>
Scope whether the "chart construction" that derives an abstract corner-slice integral from the ACTUAL
per-chart matrix integral is buildable from banked reductions, or is a genuine new-math gap. And locate
where a key non-degeneracy (det M≠0) comes from. Exact reasoning; I withhold my lean.
</task>

<setup>
An RLCT finiteness proof for the (3,3,3,4) deep linear network, one peel at pivot cut t=1. The chain:
  gammaPeelIntegral (the raw per-chart integral)
    --[A] gammaPeelIntegral_schurShearFree_eq (BANKED): = ∫_{A'}∫_{x}∫_{Γ} freedSchurLoss(x,Γ,Q)^{-c'},
          Q = tail product, freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b), Γ the a×b=2×2 corank block
    --[B] depth-reduce + RADIAL BLOW-UPS + UNIT-CLEARS -->
          the "corner slice" cornerSlice334Integral = ∫_{[0,1]²} (u₀²·U₀ + u₁²·U₁)^{-c'} |u₀|³|u₁|² du,
          U₀ = ‖w₁A₂‖²+δ²‖w₂A₂‖², U₁ = a_piv²‖v̄A₂‖², with w₁,w₂,v̄ the resolved front rows, δ,a_piv scalars
    --[C] A₂-casting (linear CoV det[w₁;w₂;v̄]≠0) --> clean coords [BANKED finite at 7/2].
Step B is UNBUILT: cornerSlice334Integral is a DEFINED endpoint; nothing derives it from gammaPeelIntegral.
Banked/available: gammaPeelIntegral_schurShearFree_eq; frobSq_schur_block_split (the exact Schur block
identity frobSq(A₀Q)=frobSq(a·Q̃ₚ)+frobSq(C·Q̃ₚ+Γ·Q_b)); measurePreserving_shearSub (free Γ);
lintegral_radial_polar_factor / lintegral_ball_radial_polar_factor (polar CoV: ∫_{ℝ^N} = ∫_sphere ∫_radial
r^{N-1}); the corank atom. The chart restricts A₀ to a pivot chart {the t×t pivot block invertible} and the
good-chart map is injective given a pivot LEFT-inverse (LP·P=1) + W,A₂ RIGHT-inverses.
</setup>

<questions>
Q1 (is step B buildable from banked, or new-math?). Step B needs, in order: (b1) the depth reduction /
   the Schur split (frobSq_schur_block_split, banked) exposing the a×b corank block Γ and the boundary
   row v; (b2) the RADIAL blow-up of Γ (a 4-dim block → u₀ with Jacobian |u₀|³ = |u₀|^{4-1}) and of the
   boundary row v (3-dim → u₁, |u₁|²) — a polar CoV; (b3) the UNIT-CLEARS (det-1 unit-triangular
   L·Γ̂·R = diag(1,δ) reducing the normalised corank block Γ̂ to the scalar δ, absorbing R into W); (b4)
   reading off U₀,U₁,w₁,w₂,v̄. Which of (b1)-(b4) are mechanical from the banked polar-CoV + Schur pieces,
   and which (if any) is genuine new construction (a measure-CoV or an identity not banked)? Is the radial
   blow-up a standard polar CoV (banked lintegral_radial_polar_factor) or does the corank-BLOCK (matrix,
   not vector) radial need a bespoke lemma?

Q2 (det M≠0 provenance). M = [w₁;w₂;v̄] (the 3 resolved front rows). WHERE does det M≠0 come from in the
   chart? Is it a consequence of the pivot-chart restriction (pivot block invertible) + the Schur
   resolution making the three rows independent — i.e. does the good-chart full-rank front SUPPLY det M≠0
   for free, or is it an EXTRA condition that must be separately imposed/proved (and could fail on part of
   the chart)? Trace it: the resolved rows w₁,w₂,v̄ are built from the front factor A₀'s rows after the
   pivot/Schur resolution; when is [w₁;w₂;v̄] full rank?

Q3 (verdict). Is step B buildable-as-labour (assembling banked polar-CoV + Schur + shear), in ~how many
   pieces, or does it contain a genuine new-math gap? Flag the single most-likely-to-break sub-step.
</questions>

<output_contract>
For Q1–Q3: direct answer + "FACT" vs "INFERENCE". End: is the literal (3,3,3,4) one-peel body =
{B (chart) + C (casting) + banked clean-coords} buildable-as-labour, and is det M≠0 free-from-the-chart
or a separate obligation?
</output_contract>

<grounding_rules>
Distinguish a mechanical assembly of banked CoVs from a genuine new measure-CoV/identity. The matrix corank
block radial (blowing up a 2×2 block as a 4-dim radial) — check it is the standard polar CoV, not something
needing anisotropic/eigenvalue structure.
