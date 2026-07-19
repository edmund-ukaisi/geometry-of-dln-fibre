<task>
I am a decorrelated paper-first auditor of a Lean 4 formalization of Aoyagi (2023),
"learning coefficient (RLCT) of deep linear networks." The paper's mechanism (worked
reproduction summarized below) resolves the singularities of the square-Frobenius loss
by iterated blow-ups and reads off the real log-canonical threshold (learning
coefficient) lambda and its pole-order theta.

Aoyagi's mechanism CONTENTS (my reading of the worked reproduction):
- M1 RLCT def (rlctAt).                          [BUILT: rlctAt]
- M2 Lemma 1: RLCT depends only on the ideal (monotone under ideal inclusion). [BUILT: S1.3 ideal-invariance/germ-locality]
- M3 Monomial rule (Hironaka pullback -> min_j (h_j+1)/(2k_j)). Paper's ONLY permitted citation (S2). [Now PROVEN S2-free via monomialThreshold_eq_iInf_axisRatio; the axiom monomial_rlct was retired]
- M4 Lemma 2: block elimination / Schur complement, unipotent transforms. [BUILT: block_elimination]
- M5 Theorem 3: peel the regular rank-r part; RLCT splits = regular Morse block (-r^2+r(H1+H_{L+1}))/2 + rlct_0(core). [BUILT as value: product_reduction, via deepest_regular_core_normal_form]
- M6 Theorem 4: deepest singular point domination (homogeneity + lower-semicontinuity). [BUILT: deepest_le_of_homogeneous_core + wired D1 >= leg for general L]
- M7 The recursive blow-up (Cases 1 & 2) -- THE MOUNTAIN: monomialize the core ideal. [IN FLIGHT: the coverage theorem + region_glue = the box-finiteness "hbox" LOWER bound]
- M8 The Jacobian (each exceptional divisor u_{s,k} carries power M_{s,k}-1). [IN FLIGHT: LeafJacobian/fold-det cocycle]
- M9 candidate thresholds M_{s,k}=Mval(t)=codim S(t); rlct_core = (1/2) min_t Mval(t). [value banked: minAdm=cCodim; the geometric =(1/2)min proof is exactly hbox, IN FLIGHT]
- M10 Lemma 3: within-set balance, min A(b)=a*l*(l-a). [BUILT into lambdaCore]
- M11 Closed form lambdaCore = (1/2)(sum q_i^2 - sum m_k^2). [BUILT]
- M12 Lemmas 4-5: the ORDER theta = a(l-a)+1 (two-envelope characterisation + count). [ABSENT: only a bare def aoyagiTheta l a on GIVEN (l,a) data; no theorem computes (l,a) from widths, no count proof, no binding to the loss]
- M13 Theorems 1 & 2 (the value theorems). [L2: PROVEN clean, sorry-free, S2-free. General L>=2: proven CONDITIONAL only on hbox]
- M14 RRR / L=2 case. [BUILT]

KEY NARROWING I found: the whole learning-coefficient theorem (L1, L2, general-L)
requires hpos : forall s, r < H s  (i.e. ALL reduced widths M^(s)=H^(s)-r are STRICTLY
POSITIVE). Aoyagi's theorem covers reduced widths = 0 (a layer at exactly rank r).
The team documented that at a zero reduced width the ATTAINMENT half "minAdm in
terminalExponents" is FALSE (witness M=[2,2,0]: the minimizer stratum is never realized
by the resolution tree because a zero last-width forces immediate rollover). So the
zero-width case is scoped out and is not a trivial add.

Two theta faces: (a) the COMBINATORIAL theta = a(l-a)+1 needs no analysis, pure count on
the (l,a) selection data (Aoyagi Lemmas 4-5); (b) the ANALYTIC identity "combinatorial
count = pole multiplicity of the zeta function" needs meromorphic continuation, which the
Lean library (Mathlib) lacks -- correctly out of scope. Separately, the SAME repo already
has, on the sibling Lehalleur-Rimanyi "DLN fibre" paper, a fully-built GEOMETRIC component
count numTop (unconditional); there is NO bridge aoyagiTheta = numTop.

My DRAFT top-5 "the math wants this built" (ranked by mathematical necessity):
1. hbox = coverage theorem + region_glue (M7/M8/M9): the one genuine new proof; the (1/2)min_t
   geometric lower bound. IN FLIGHT (not avoidance). Large.
2. Aoyagi's combinatorial theta = a(l-a)+1 (M12, Lemmas 4-5): ABSENT; fully independent of the
   in-flight analytic resolution; Aoyagi's second deliverable. Medium.
3. Extend the value theorem to zero reduced widths (drop hpos>0): narrowing vs Aoyagi; value/
   arithmetic side separable, attainment side needs a zero-width-layer-collapse in the resolution.
   Medium.
4. A bridge aoyagiTheta (a(l-a)+1) = geometric numTop (the built component count): cross-paper
   consistency check of the two theta's. Uncertain -- the formulas look different (numTop is a
   binomial C(m,|delta|); Aoyagi's is a(l-a)+1); may not be a clean equality. Small-medium IF true.
5. Confirm/clean the achiever-divergence half's axiom footprint (AxCheck docstrings still name the
   retired monomial_rlct; the code routes S2-free). Hygiene, not math. Small.

My DRAFT "independently buildable lines" (no dependence on the in-flight hbox/coverage/region_glue):
- #2 combinatorial theta (strongest).
- #3 zero-width value side (arithmetic only).
- #4 aoyagiTheta = numTop bridge (a pen-and-paper truth check first).
- #5 axiom-footprint hygiene.
</task>

<output_contract>
Be terse. Four sections:
1. MISSED GAPS: any item of Aoyagi's mechanism I mis-classified as BUILT that is likely
   narrower/absent, OR any mechanism content I omitted entirely (think: fidelity of Theorem 3's
   RLCT-SPLIT at general L and r>0 vs just the value; whether Lemma 1 ideal-monotonicity is the
   full statement or a change-of-variables special case; the far-point/non-deepest leg of
   Theorem 4; the phi-independence and germ->compact-box steps of the RLCT def). For each: why
   it is likely a gap and the ONE cheapest way I could confirm it from the Lean source.
2. RANKING CHECK: do you agree with my top-5 necessity ranking? Reorder if the MATH (not Lean
   convenience) demands it. Flag any item that is actually two items or is mis-sized.
3. THETA BRIDGE: is aoyagiTheta = a(l-a)+1 plausibly EQUAL to a top-dimensional-component count
   like C(m,|delta|)? Give the cheapest concrete numeric test to decide (a specific width vector).
4. BLINDSPOT: the single most likely thing a paper-first auditor in my position would MISS.
</output_contract>

<grounding_rules>
Distinguish what you can INFER from my summary vs what would need reading the Lean source.
Do not invent Lean lemma names. If a judgment depends on a fact you cannot verify from my
summary, say so and name the cheapest check. Mathematical-necessity is the bar, not Lean cost.
</grounding_rules>
