<task>
Lean 4 / Mathlib formalisation reachability question. I am formalising "Piece 3" of Aoyagi's
(S,J) boundary peel for deep-linear-network RLCT. I must decide whether a specific reduction is
SORRY-FREE reachable using ONLY already-proven ("banked") measure-theoretic + linear-algebra
lemmas, or whether it inescapably contains genuine analytic content (radial blow-up / Beta
integral / exponent shift) that a later tide must supply.

SETUP (all real matrices; frobSq X = sum of squares of entries; lintegrals over boxes).
After a banked measure-preserving front-split, the box integral is
    box = ∫_{A' ∈ tailBox} ∫_{A0 ∈ matBox(M0,M1) = [-1,1]^{M0·M1}} frobSq(A0 · Q)^{-c'}   dA0 dA',
where Q = Q(A') : M1×n is a fixed (given A') matrix product of the deeper layers, c' > 0 real.

BANKED, sorry-free, available lemmas:
 (i) schur_cov: for the block split A0 = [[A,B],[C,D]] with A (t×t) invertible,
     Q1·A0·Q2 = fromBlocks A 0 0 Γ, Γ = D − C A⁻¹ B, and det Q1 = det Q2 = 1 (unit triangular).
 (ii) measurePreserving_shearSub: the block shear (x,D) ↦ (x, D − K x) is volume-preserving for
     measurable K. (So D ↦ Γ = D − C A⁻¹ B at fixed (A,B,C) is a measure-preserving reparametrisation.)
 (iii) pivotLocus_eq_iUnion: {A0 | t ≤ rank A0} = ⋃ over finitely many (ρ,κ) row/col pivot selections
     of pivotChart(ρ,κ) = {A0 | the (ρ,κ) t×t minor is a unit}.  (finite cover of the rank-≥t locus.)

TARGET REDUCTION (what the tide asks me to prove sorry-free):
Define the Γ-EXPLICIT per-step object
    gammaPeelIntegral κ t c' := ∫_{A'} ∫_{Γ ∈ matBox((M0−t)×(M1−t))} (P_tail_κ(Q) + frobSq(Γ · Q_bκ(Q)))^{-c'}
  where P_tail_κ(Q) = squared norm of the κ-pivot-column rows of Q (the reduced tail-chain loss),
  Q_bκ(Q) = the (M1−t) NON-pivot-column rows of Q.  NOTE the exponent is −c' (NOT shifted), and Γ is
  an INTEGRATION variable over a box.
Prove:  box ≤ Σ_{t, κ} C_κ · gammaPeelIntegral κ t c'   (finite constants C_κ), SORRY-FREE.

The tide spec breaks this into 4 sub-lemmas and claims all 4 are "clean-three" (sorry-free), "pure
plumbing on banked pieces, atom-free":
 1. pivotChartCover_lintegral_le_sum: cover + finite subadditivity → box ≤ Σ_κ (chart-κ contribution).
 2. schurShear_chart_lintegral (LOAD-BEARING): on chart κ, shearSub+schur_cov "rewrite the chart
    contribution with Γ explicit (Jacobian 1), integrand (P_tail_κ + frobSq(Γ·Q_bκ))^{−c'}". Claimed an
    "exact block identity".
 3. chartRadialBlock_to_gammaPeel (LOAD-BEARING): "integrated over A' and the chart pivot variables,
    bound the chart contribution by C_κ · gammaPeelIntegral κ t c'" (INTEGRATED, not pointwise).
 4. sjBoundaryPeel_explicitGamma: assemble 1–3.

MY ANALYSIS (want you to confirm or refute, independently):
Writing A0=[[A,B],[C,D]], Q=[Q_p; Q_b] (rows split by pivot/non-pivot cols), one gets exactly
    A0·Q = [ A·Q_p + B·Q_b ;  C·Q_p + D·Q_b ],
and after the shear D↦Γ (D = Γ + C A⁻¹ B):
    A0·Q = [ A·(Q_p + A⁻¹B·Q_b) ;  C·(Q_p + A⁻¹B·Q_b) + Γ·Q_b ].
So frobSq(A0·Q) = frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b), Q̃_p := Q_p + A⁻¹B·Q_b.
This is NOT equal to (P_tail + frobSq(Γ·Q_b)): (a) the top block frobSq(A·Q̃_p) is not P_tail=‖Q_p‖²
(there is the invertible-but-possibly-near-singular factor A and the B-shear), and (b) the bottom block
retains the cross term C·Q̃_p, not eliminated. So sub-lemma 2 as an EXACT identity looks FALSE; at best
it is a comparability up to bounded conjugator norms (‖A‖,‖A⁻¹‖,‖C‖ on the chart), which is not a banked
one-liner. And sub-lemma 3's bound requires integrating a NEGATIVE power over the pivot variables
(A,B,C): since frobSq(A0·Q) vanishes on a positive-codim locus of (A,B,C), there is no uniform pointwise
lower bound frobSq(A0·Q) ≥ const·(P_tail+frobSq(Γ·Q_b)); integrating (·)^{-c'} over (A,B,C) genuinely
SHIFTS the exponent (radial blow-up c' ↦ c'−a/2), which is the analytic core, not plumbing. Independent
numerics (r1u_gram.py) confirm the per-chart inner ∫_{A0} frobSq(A0 Q)^{-c'} is finite iff c'<M0·rank(Q)/2
and DIVERGES on the null rank-deficient locus of Q — so even the integrated per-chart bound needs a.e.
/ null-set handling, not a uniform constant.

QUESTION: Is the target reduction `box ≤ Σ C_κ · gammaPeelIntegral` SORRY-FREE reachable from banked
(i)-(iii) alone (pure measure-theoretic + linear-algebra plumbing)? Specifically:
 - Can sub-lemma 2 be stated as a TRUE sorry-free statement (identity or otherwise) via shearSub+schur_cov?
 - Can sub-lemma 3's per-chart bound be obtained without a radial blow-up / exponent-shift / Beta integral,
   i.e. with a genuinely uniform finite constant C_κ independent of A'?
 - If NOT sorry-free: which of the 4 sub-lemmas carry the irreducible analytic content, and what is the
   cleanest HONEST decomposition (which lemmas ARE sorry-free banked plumbing, which must stay named
   sorries) so the def-refinement + true plumbing lands while the analytic core is quarantined?
</task>

<output_contract>
1. VERDICT: one line — is `box ≤ Σ C_κ gammaPeelIntegral` sorry-free reachable from banked (i)-(iii)? YES/NO.
2. Sub-lemma 2: TRUE-as-identity? / TRUE-only-as-comparability? / FALSE? — one short paragraph + the corrected true statement if any.
3. Sub-lemma 3: is a uniform-constant per-chart bound possible without exponent shift? one short paragraph.
4. If NOT sorry-free: the cleanest honest decomposition — list each of the 4 sub-lemmas as [SORRY-FREE plumbing] or [IRREDUCIBLE analytic, keep named sorry], and name what the two remaining sorries should be.
5. Anything in my analysis that is WRONG (flag inference vs. fact).
Keep it under ~500 words. Be decisive.
</output_contract>

<grounding_rules>
State explicitly when a claim is a mathematical fact you can verify by the block algebra above vs. an
inference about Lean-reachability. Do not invent Mathlib lemma names. If the reduction IS reachable,
give the key idea; if NOT, do not pretend a plumbing route exists.
</grounding_rules>
