<task>
Lean 4 + Mathlib formalisation, RLCT lower-bound gate for deep linear networks.
I am asked to discharge the R1-LOWER achiever box-divergence at network depth L=2.
The leg hangs on ONE box-integral divergence: ∫_{[-ε,ε]^N} |F(x)|^{-c'} dx = ⊤ for c' ≥ ½·minAdm,
where F = routeMCore M (a sum-of-squares loss in flat coords). The route is a change-of-variables
through a chart φ that blows up the achiever center.

There are TWO branch contracts (both proven sorry-free GIVEN their open chart fields):

(A) INTERIOR branch, via the bundle `NodeAchieverChart M` whose key field is:
    cov: ∫_{φ''(V\{u_p=0})} g = ∫_{V\{u_p=0}} (∏_j |u_j|^{leafH_j}) · g(φ u)
    i.e. the chart Jacobian MUST be a PURE MONOMIAL  |det Dφ| = ∏_j |u_j|^{leafH_j}.
  The interior contract is built on the DEAD-LEAF / structured chart  achieverPhi = phiFlatStructV
  (its unit a.e.-positivity is PROVEN via an interior-drop pivot-survival witness).

(B) A separately-landed determinant headline `interiorDet_leaf_headline_eihd` is for a DIFFERENT,
  LIVE-LEAF chart  phiFlatLiveAt , and gives a NON-monomial Jacobian:
     |det Dφ_live| = |u_p|^{minAdm-1} · |det K|^{r+c}
  where K = leafKcore (a free Schur-core block read from x, a general matrix whose det is a
  polynomial, NOT a single coordinate). The worked (3,3,3,3) anchor instead used a SEPARATE chart
  phi3333 with an LDU coordinatization Kparam3333 that STRAIGHTENS det K into a monomial, so that
  |det Dφ_3333| = |u0|^5·|u1|^4·|u4|^2·|u9|^3 (pure monomial), matching the cov form.

My STEP-0 finding (to red-team): the just-landed eihd det does NOT feed the interior cov contract,
because (i) it is the LIVE-leaf chart phiFlatLiveAt, not the dead-leaf achiever chart phiFlatStructV
the interior contract is built on; and (ii) its Jacobian |u_p|^{minAdm-1}·|det K|^{r+c} is NOT a
monomial, whereas cov demands ∏_j |u_j|^{leafH_j}. The monomial form requires the LDU-straightening
(phi3333-style), which the eihd det does not perform.

Question set:
1. Is my STEP-0 finding correct — that the eihd det is the WRONG vehicle for the interior `cov`
   field as currently stated (wrong decoder + non-monomial shape)? Or is there a sound reconciliation
   I am missing (e.g. fold |det K|^{r+c} into the unit U)?
2. For the divergence integral ∫ (∏|u_j|^{leafH_j})·|u_p²·U|^{-c'}, the divergence at c'=½·minAdm
   needs the PIVOT exponent to net to -1: leafH_p - 2·(minAdm/2) = (minAdm-1) - minAdm = -1. The
   spectator factors (k=0 axes) must have a FINITE non-divergent contribution. If I keep the chart
   live and FOLD |det K|^{r+c} into the unit U' := U·|det K|^{-(r+c)}... no — det K can be 0, U' not
   bounded. Alternatively keep cov with leafH = δ_p·(minAdm-1) (Jacobian = |u_p|^{minAdm-1} ONLY) and
   absorb |det K|^{r+c} as part of g? But cov is an EXACT Jacobian identity, so |det Dφ| must equal
   the stated monomial. Which of these is sound, if any?
3. Given the eihd det is most naturally the input to the D1 UPPER-bound (rlctAtOn ≤ ...) via the
   IFT change-of-variables route (rlctAtOn_eq_of_contDiff_chart), and NOT the R1-LOWER box-divergence,
   is the correct conclusion that the L=2 interior R1-LOWER leg needs its OWN monomial-Jacobian chart
   (phi3333-style, ∀M-L2, via LDU-straightening of leafKcore), which is a separate MAJOR build the
   eihd det does not shortcut?

Numbers for the (3,3,4) interior boundary: Text2=1, Text1=3, Wext1=3, so r=c=2, r+c=4; leafKcore is
1×1 so |det K|^4 = |K00|^4 IS a monomial there — but the phi3333 weight on that axis is exponent 2,
not 4 — so even at this small case the eihd det's exponent (4) and the phi3333/leafH monomial (2)
DISAGREE. Reconcile or confirm they are genuinely different chart geometries.
</task>

<output_contract>
1. VERDICT on Q1 (eihd det right/wrong vehicle for interior cov) — one of {WRONG-VEHICLE,
   RECONCILABLE-VIA-X, UNSURE}, ≤4 sentences justification.
2. Q2: which absorption (if any) is measure-theoretically sound; ≤4 sentences.
3. Q3: is the L=2 interior R1-LOWER a separate monomial-chart build the eihd det does not shortcut?
   {YES-SEPARATE-BUILD, NO-EIHD-SHORTCUTS-IT, UNSURE} + ≤3 sentences.
4. One-line: the single cheapest thing I should verify in the Lean source to confirm/refute.
Keep total under ~350 words. Flag any claim that is inference vs. what you can derive from the
contract shapes I gave.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason ONLY from the contract shapes and numbers I gave above. Do not
invent Mathlib lemma names. Explicitly mark each conclusion as DERIVED (from the shapes I gave) or
INFERENCE (plausible but unverified). If a question cannot be answered from the given shapes, say so.
</grounding_rules>
