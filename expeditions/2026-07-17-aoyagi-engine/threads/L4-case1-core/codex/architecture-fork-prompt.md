<task>
A pivotal ARCHITECTURE re-appraisal for a Lean 4 formalisation of Aoyagi (2023)'s real-log-canonical-
threshold (RLCT) result for deep-linear networks. Judge whether the code is in an ENCODING local-min.

THE GOAL (both routes reach it): prove rlctGlobal(loss) = cCodim/2, where loss = ∑(∏C)² is the sum of
squares of the entries of a product of matrices ∏C (a "coupled" corank≥2 product — the b_i below share
divisors), and cCodim is a combinatorial codimension.

FOUNDATIONS ALREADY LANDED (sorry-free):
- Object A (Aoyagi Lemma 1, "ideal-invariance"): rlctAt(∑ f_i²) depends ONLY on the ideal ⟨f_i⟩ (both
  directions). So rlctAt is an IDEAL-level invariant.
- Object C (monomial-ideal RLCT): for a MONOMIAL ideal ⟨b_i⟩ with the divisibility chain b_1|b_2|…|b_M,
  rlctAt(∑ b_i²) = ½·min (a Newton-polyhedron formula). Handles the coupled divisibility chain.
- Object D: min = cCodim (combinatorial bridge).

THE PAPER'S ROUTE (worked.tex): maintains an IDEAL IDENTITY ⟨∏C⟩ = ⟨diag(b)·[E_J⊕D_J]·∏_{s>S}C⟩ step by
step via UNIMODULAR Schur-clearing matrices Q,P (multiplying by units preserves the ideal EXACTLY); the
Schur cross-term F₃·F₂ drops because it is literally a product of two generators, so it lies IN the ideal
⟨F₂,F₃⟩ (a one-line ideal argument); exceptional/blow-up coordinates appear ONLY at the very end, where the
b_i become monomials. Net: ⟨∏C⟩ = ⟨diag(b)⟩ (monomial), then Object A + Object C give rlctAt = ½·min.
So the paper's ONLY hard step is the ideal identity ⟨∏C⟩=⟨diag(b)⟩ at coupled corank≥2 (Cases 1&2), done
by unimodular Q,P at the MATRIX/ideal level.

THE CODE'S ROUTE: does NOT maintain the matrix-ideal identity. Instead it builds a coordinate BLOW-UP
RESOLUTION as a tree of charts, encoding each blow-up step as a PER-COORDINATE SUBSTITUTION
(divide-by-pivot, "blockBlowupCoordQuot") and carrying a heavy COORDINATE SUPPORT-TRACKING invariant
(a "FoldStepInvAt" per-node: the residual is degree-1-supported on a tracked coordinate set), plus
auxiliary machinery (a "couplingClear" projection zeroing coupling coords, a "KILL" lemma that the cleared
residual ignores escaped columns, "phantom-branch" exclusions). The open KEYSTONE is the coupled corank≥2
preservation of this coordinate invariant ("the wall"); ~29 distinct fidelity bugs over ~260 commits have
ALL clustered in this coordinate-substitution + support-tracking apparatus; integration sorry-count has
been ~flat (489→495) for a long stretch (a suspected treadmill). The code's final payoff consumes a
coordinate RESOLUTION (an atlas of charts) feeding "2·rlctAt = cCodim".

THE FORK: is the code's coordinate-substitution + support-tracking encoding a NECESSITY, or a redundant
local-min relative to the paper's ideal-identity route (Object A + the matrix-ideal ⟨∏C⟩=⟨diag(b)⟩ via Q,P
+ Object C), which would need NO per-step coordinate substitution and NO support-tracking?
</task>

<output_contract>
1. VERDICT (one line + confidence): is the coordinate-substitution encoding likely a LOCAL-MIN (the ideal
   route is sufficient and far simpler) or a NECESSITY (the ideal route has a real gap)?
2. WHAT (if anything) THE IDEAL ROUTE FAILS TO GIVE that the coordinate resolution provides. Specifically:
   (a) Does going from the ideal identity ⟨∏C⟩=⟨diag(b)⟩ (monomial) + Object A + Object C to "rlctAt = ½·min"
   genuinely need a coordinate blow-up atlas, or is it a direct composition? (b) Is the blow-up/exceptional
   coordinates needed to MAKE the b_i monomial (so some coordinate change is unavoidable) — and if so, can
   that be done at the ideal level (the ideal ⟨∏C⟩ pushed forward under a monomial map = ⟨monomials⟩) rather
   than per-step substitution + support-tracking? (c) Does "cCodim via a Resolution" require a coordinate
   atlas, or can it come from Object C's monomial RLCT + Object D directly?
3. THE ONE DECISIVE CHECK that would settle necessity-vs-local-min (cheapest experiment).
4. IF local-min: the shape of the ideal-route re-architecture + its single biggest risk.
</output_contract>

<grounding_rules>
Distinguish what you can conclude from the STRUCTURE described (FACT) vs INFERENCE about the Lean encoding
you cannot verify. Flag explicitly where your judgement depends on a detail not given (e.g. whether Object C
is stated for the ideal or requires a specific coordinate form; whether the engine's "2·rlctAt=cCodim" is
ideal-level or resolution-level). Do NOT assume the coordinate route is necessary just because it is what
was built. You do not have the paper or the Lean source; reason from the structure.
</grounding_rules>
