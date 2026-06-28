<task>
Red-team a Lean-4/Mathlib formalisation DESIGN (no code yet — design diff-gate). Context: deep linear
network RLCT. We have a sorry-free, axiom-clean depth-2 "Schur core" finiteness chain at OUTPUT WIDTH p=4:

  SchurCore p r c' T  :=  ∫_{Δ∈[−T,T]^{r×r}} ∫_{S∈[−T,T]^{r×p}}  ‖Δ·S‖_F^{−2c'... actually (frobSq(Δ·S))^{−c'}}  < ⊤

(frobSq = squared Frobenius norm, c'>0). The ABSTRACT recursion framework is already ∀p-parametric:
- SchurThreshold p lam : a Prop-structure with three fields:
    lambda0   : lam 0 = 0
    radial_le : 1≤r → lam r ≤ r²/2                              [cap B: the r² radial blow-up Jacobian]
    peel_le   : 1≤j≤r → lam r ≤ j·p/2 + lam (r−j)               [cap A: peel a j·p Morse block, recurse]
- SchurLowerIH p lam r : ∀ 1≤j≤r, ∀ 0<c''<lam(r−j), ∀ T''>0, SchurCore p (r−j) c'' T''   [the IH]
- SchurRecStep p lam   : ∀r, SchurThreshold p lam → SchurLowerIH p lam r → ∀ 0<c'<lam r, ∀T>0, SchurCore p r c' T
- core_schurGen_lt_top (p lam) (SchurThreshold) (SchurRecStep) : ∀r c' T, the ∀-corank finiteness.
  [WellFounded strong-induction-on-corank wrapper, NO analytic content, axiom-clean, p-generic AS-IS.]

At p=4 we have PROVED (sorry-free): schurRecStep_four : SchurRecStep 4 schurLambda, where
schurLambda = [0, 1/2, 2, 4, 6, 8, ...] (= 2r−2 for r≥2). Its proof is a 4-way dispatch on r:
  r=0 vacuous; r=1 Morse leaf (threshold c'<1/2); r=2 base; r≥3 the "firing" engine
  schurCoreGen_firing: flatten the r² Δ-cells → r²-chart radial-Δ cover (recStep) → per-chart finiteness
  (schur_matBoxG_chart_lt_top), which uses |det Dblowup| = |y_pivot|^{r²−1} (cap B, p-FREE), the cap-B
  threshold lam r ≤ r²/2, and the angular finiteness from the IH (a "carve" lemma over the r²−1 ANGULAR
  RATIOS of the r×r matrix R — p-invariant, since p lives only in S).

GOAL: design schurRecStep_p : ∀p, SchurRecStep p (schurLambdaP p), generalizing p=4 to arbitrary p.

KEY NUMERICAL FACTS I have verified (sympy/python, p=1..8, r=0..7, ALL MATCH):
(1) The greatest solution of the SchurThreshold contract is
      lam(r) = min( r²/2 , min_{1≤j≤r}( j·p/2 + lam(r−j) ) )  =  (1/2)·minAdm(r,r,p),
    where minAdm(r,r,p) = min_{t=0..r} [ (r−t)² + p·t ]   (an INTEGER min over rank-drop strata t).
(2) The leaf lam(p,1) = 1/2 for ALL p≥1 (cap B at r=1: r²/2=1/2), NOT p/2 — confirmed by the p=4
    leaf's threshold being 1/2 (the single Δ₀₀ scalar's radial axis; the Fin p S-block is pure Morse).
(3) The BINDING cap shifts with (r,p): cap B (r²/2) binds while p≥2r; cap A (the peel) binds for larger r.
    So there is NO single closed linear ladder; lam is a genuine piecewise min. (p=4's 2r−2 is the
    coincidence that cap A always binds for r≥2 at p=4.)
(4) peel_le sub-additivity minAdm(r,r,p) ≤ j·p + minAdm(r−j,r−j,p) HOLDS (no violations, p=1..11,r=1..11),
    via the algebraic stratum-lift identity (r−(t'+j))²+p(t'+j) = (r−j−t')²+p·t'+p·j (exact).

MY DESIGN DECISIONS to red-team:
(A) WITNESS: define schurLambdaP p r := (minAdm(![r,r,p]) : ℝ)/2  [Option B], REUSING a sibling thread's
    landed `minAdm`/`minAdmRec` recursion (inf' over Finset.range), rather than a fresh recursive `min` def
    [Option A]. Claim: this makes the three SchurThreshold lemmas provable from minAdmRec, and the
    downstream threshold-match `minAdm_rrp_eq` becomes near-rfl. peel_le = the sub-additivity (4), proved
    by lifting a binding stratum t' for (r−j) to t'+j for r using the identity.
(B) The carve / engine p-lift is "mechanical width-swap 4→p" (Fin 4 S-columns → Fin p, summed opaquely;
    the r²−1 angular-ratio carve is p-free). LARGE by LoC (~600) but not hard. radial axis (cap B) is p-free
    and ALREADY built {r,p}-general in a sibling file.
(C) The r=2 base at p=4 is a hand lemma core_schur2_lt_top (NOT the firing, which needs hr:3≤r). I flag
    that at general p, r=2 may need a separate p-lift of core_schur2, OR the firing's hr:3≤r bound may be
    loosenable to 2≤r. Which is cleaner?
</task>

<output_contract>
Be terse and concrete. Sections:
1. VERDICT on Option B (minAdm/2 witness) vs Option A (fresh min-def): which is the right Lean object, and
   the single biggest risk of Option B (e.g. the inf'-over-Finset.range dependent-motive friction the sibling
   thread hit). One recommendation.
2. peel_le: is the "lift binding stratum t'→t'+j" proof sound and Lean-tractable as ONE inf'_le_of_le + the
   ring identity? Any hidden case (j=r so r−j=0 leaf; the Nat-subtraction r−(t'+j))?
3. The r=2 question (C): hand-base vs loosen hr to 2≤r — which, and why.
4. Any CONFOUND I have missed — a place where "4 → p" is NOT mechanical, or where the threshold structure
   (cap shifting with p, leaf=1/2 not p/2) breaks an assumption the p=4 proof silently relied on. This is the
   highest-value section: name the one thing most likely to bite during the build.
5. Go / no-go on diff-gating this design to the controller, and the ONE change you'd make first.
</output_contract>

<grounding_rules>
You are reviewing a DESIGN, not code. Flag explicitly when you are INFERRING Lean behavior vs stating a known
Mathlib v4.29 fact. If you don't know whether a specific lemma exists, say "verify" rather than asserting.
Do not write the full proof — diagnose the design. Mark each risk as [LOW]/[MED]/[HIGH].
</grounding_rules>
