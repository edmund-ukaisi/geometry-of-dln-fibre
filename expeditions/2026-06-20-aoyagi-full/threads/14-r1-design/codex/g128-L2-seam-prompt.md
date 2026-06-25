<task>
Adjudicate the SOUND bridge for a Lean build seam, with exact reasoning. Do NOT run code.

SETTING. L2 product_reduction: rlctAt(F) at the deepest point = nReg/2 + rlctAt(core), F = ||prod(C)-B||^2,
B rank r. A formaliser (a114e07e) needs to feed S1.5 (smooth-block additivity), which consumes the
LITERAL form ΣEᵢ² + G² (a sum of nReg regular squares + a core square). The deepest-point chart χ
(replace each regular generator's unit-pivot variable by the generator) was proposed, but does NOT give
the literal form — verified: F∘χ = E1²+E2²+E3²+(G + E·h)² with cross terms (the core generator, in χ-coords,
depends on the regular coords E). So there's a seam gap: the literal ΣEᵢ²+G² is NOT directly reached.

AVAILABLE GREEN TOOLS (and NOTHING else; no ideal-generator-invariance / Lemma-1(2) lemma exists in the
project): rlctAt_mono (g²≤f² on a nbhd + zero-set inclusion ⟹ rlctAt g ≤ rlctAt f), rlctAtOn_unit_invariant_aux
(multiply by a measurable unit bounded in [a,b], a>0, ⟹ same rlctAtOn), rlctAtOn_comp_homeomorph (MeasurePreserving
c-o-v), smoothBlockND_rlct (rlctAtOn(Σ_{i<m} xᵢ²) 0 = m/2), S1.5 smooth-block Fubini additivity.

FACTS I established by exact computation, (2,2,2) r=1 (nReg=3, core = reduced (1,1,1), rlct 1/2;
target rlctAt(F) = 3/2 + 1/2 = 2):
- F = g00²+g01²+g10²+g11² (literally a sum of 4 squares, NO overall unit factor).
- The 3 regular generators g00,g01,g10 have distinct unit pivots (w4,w5,w2); g11 (the core gen) has no
  linear part. The Schur core G = g11 on the regular-zero locus = −w3·w7/(w1·w6−1) (E-free, in vars
  w3,w7,w0,w1,w6).
- Define Phi = g00²+g01²+g10²+G². NUMERICALLY, F/Phi → 1 as the scale → 0 (min 0.9995, max 1.0007 at
  scale 0.01; min 0.946, max 1.057 at scale 0.1). So F and Phi are SQUEEZED: ∃ c1,c2>0 and a nbhd U of 0
  with c1·Phi ≤ F ≤ c2·Phi on U.
- Phi's regular generators (pivots w4,w5,w2) are DISJOINT in leading variables from G (vars w3,w7), so
  Phi = (3 regular nondeg squares) + (core G²) splits cleanly for S1.5.
</task>

<sub_question>
1. Is the SOUND bridge the SQUEEZE: c1·Phi ≤ F ≤ c2·Phi near 0 (c1,c2>0) ⟹ rlctAt(F) = rlctAt(Phi) via
   rlctAt_mono applied BOTH directions (each constant multiple is a unit, stripped by unit-invariance)?
   I.e. NOT a literal F∘χ = ΣEᵢ²+G², NOT an ideal-generator-invariance lemma — but the two-sided squeeze
   + rlctAt_mono. Then S1.5 on Phi gives nReg/2 + rlctAt(G²). Is this sound + green-tool-only?
2. Does the squeeze inequality c1·Phi ≤ F ≤ c2·Phi genuinely hold near 0 (the cross terms 2G·E·h
   dominated by the nondegenerate regular block + the G² term)? Or is there a direction where F vanishes
   faster than Phi (or vice versa) so the squeeze fails and the rlcts could differ? (The numerics suggest
   F/Phi→1, but confirm the structural reason: F − Phi = g11² − G² = (g11−G)(g11+G), and g11−G ∈ the
   regular ideal (g00,g01,g10), so F − Phi is controlled by the regular block.)
3. The two-unit concern a114e07e raised: in the FULL chain there's a measure Jacobian |det χ'| (a unit,
   from the c-o-v) AND possibly an integrand unit. Does the SQUEEZE route AVOID the measure-Jacobian
   entirely (since it compares F and Phi as integrands at the SAME point, no c-o-v needed)? Confirm the
   squeeze route needs NO c-o-v (so no measure Jacobian) — just rlctAt_mono + S1.5 — making the
   "two units" concern moot.
4. Verdict: the sound green-tool bridge for a114e07e's L2 half-(a) seam (the exact transport chain), and
   whether it avoids both the false-literal-form and the absent ideal-invariance lemma.
</sub_question>

<output_contract>
- Verdict: the sound bridge (squeeze + rlctAt_mono + S1.5, or another green-tool route), explicit chain.
- Whether the squeeze c1·Phi ≤ F ≤ c2·Phi holds near 0, with the structural reason (F−Phi in the regular ideal).
- Whether the squeeze route avoids the measure Jacobian (no c-o-v) — resolving the two-unit concern.
- FACT vs INFERENCE labels.
</output_contract>

<grounding_rules>
- Ground in the facts above + standard RLCT theory. Reason on paper ONLY; do NOT read files or run code.
- rlctAt_mono needs |g|≤|f| on a nbhd + (g=0⟹f=0). A two-sided squeeze c1·Phi≤F≤c2·Phi gives
  rlctAt(F)=rlctAt(Phi) IF both directions' zero-set inclusions hold (F and Phi have the same zero set).
- No ideal-generator-invariance lemma exists; do not assume one.
- Preserve FACT vs INFERENCE.
</grounding_rules>

<important>
You have NO file, shell, or code access. Do not call any tool. Produce only the reasoned adjudication.
</important>
