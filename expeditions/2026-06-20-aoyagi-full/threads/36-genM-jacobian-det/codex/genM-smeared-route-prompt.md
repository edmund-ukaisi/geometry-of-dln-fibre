<task>
Decide the cleanest Lean 4 + Mathlib (v4.29) ROUTE to discharge the ∀M boundary-SMEARED achiever
box-divergence atom for deep-linear-network nodes, generalizing two completed concrete-width
validate-smalls to ALL 46 boundary-smeared dimension vectors M. This is a route-selection / design
decision BEFORE a multi-hundred-line build — I need the route that generalizes cleanly to PARAMETRIC
widths, not the one that was easiest at fixed width.
</task>

<context>
SETTING. For a node M = (M_0,...,M_L), the "boundary-smeared" class (46 cases over a base grid) has
r := Text(L) < m1 := M_{L-1}, c := M_L, s := m1-r, minAdm = r*c. The achiever-chart loss
F = ||P · A^{L-1}||^2 factorizes (validated EXACT 46/46 by a sympy gate) as F = z^2 * U where:
- P = A^0···A^{L-2} is the M_0 x m1 front product; P_1 = P[:, :r] (full column rank r), P_2 = P[:, r:].
- Lambda_0 := (P_1^T P_1)^{-1} P_1^T P_2  (r x s rational routing; P_1 Lambda_0 = P_2 exactly off the
  pole {det(P_1^T P_1)=0}).
- A^{L-1} = [ z·Hbar - Lambda_0·S_bot ;  S_bot ]  (top r·c rows radial+shear, bottom s·c rows free).
- |det Dphi_sm| = |z|^{minAdm-1} = |z|^{r·c-1} (radial pivotBlowupOn on the r·c top coords; the rational
  shear is unit-triangular det-1; identity front + identity spectator). Threshold = minAdm/2.

TWO COMPLETED VALIDATE-SMALLS (both sorry-free, S2-free [propext,Classical.choice,Quot.sound]):
- (1,2,1): r=1,c=1,s=1,minAdm=1. SCALAR shear (Lambda_0 is 1x1 = b/a), NO radial. Discharged via a
  reusable `routeMCore_box_diverges_of_MPChart` (weight 1): phi = Q∘shear, Q∘shear measure-preserving +
  measurable embedding (the shear is a global measurable bijection, det 1).
- (2,3,1): r=2,c=1,s=1,minAdm=2. 2x2 Gram, RADIAL |z|^1. Discharged via a reusable
  `routeMCore_box_diverges_of_RadialMPChart`: phi = psi ∘ R, psi = Q∘shear (MP + measurable embedding),
  R = pivotBlowupOn (the radial, the sole Jacobian carrier, |det|=|u_p|^{minAdm-1}), fed a WEIGHTED
  source-divergence ∫_S |u_p|^{minAdm-1}·(loss∘phi)^{-c} = ⊤ on a bounded-away sub-box.
  KEY shortcuts that DON'T obviously generalize to parametric r:
   * `lam231_explicit`: the 2x2 (P_1^T P_1)^{-1} P_1^T P_2 written as an EXPLICIT rational (via
     adjugate_fin_two / det_fin_two) → measurability by hand. At parametric r×r there is no explicit
     inverse; one needs generic Matrix.nonsingInv measurability.
   * `split231`: a hand-built Fin-9 2-core MeasurableEquiv peel (piFinSuccAbove twice) so
     `coreShear_measurable` gives the shear MP. At parametric flatDim M the core is the r·c top-A^{L-1}
     coords — a parametric split, much harder to build by piFinSuccAbove.

THE OTHER BRANCH'S PRECEDENT. The BOUNDARY-CLEAN branch (r=m1, NO smear, POLYNOMIAL chart) was already
generalized ∀M cleanly: `cleanPhi_hasFDerivAt`/`cleanPhi_abs_det` (polynomial pivotBlowupOn, so
HasFDerivAt+det are M-agnostic), `cleanPhi_cov` (polynomial change-of-variables via the banked
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`), `cleanNodeChart : NodeAchieverChart M`, then
`routeMCore_box_diverges_clean := routeMCore_box_diverges_of_nodeChart M (cleanNodeChart ...)`. The
`NodeAchieverChart` structure has a `cov` field and a reusable M-agnostic assembly
`routeMCore_box_diverges_of_nodeChart`. The smeared certificate's DESIGN (§4) says the smeared chart
ALSO fits `NodeAchieverChart` with the SAME single pivot z, leafH z = minAdm-1, but its `cov` must ride
an A.E.-ANALYTIC change-of-variables (the map is RATIONAL, undefined on the null pole set) — there is
banked S1.1 transport machinery (`S1Transport`/`S1NonMPTransport`/`S1G5` single c-o-v on V\N + null-drop,
the `|det Dπ|`-weight transport, sorry-free `_aux`) intended for exactly this.

THE FORK (what I need adjudicated):
ROUTE A — fit `NodeAchieverChart M` via the a.e.-analytic `cov` (S1.1 transport on box\pole). M-agnostic
  by construction (mirrors the CLEAN branch), reuses `routeMCore_box_diverges_of_nodeChart`. Cost: prove
  the rational chart's `cov` field via the a.e. transport lemma + the |z|^{minAdm-1} Jacobian off the
  pole (need: rational phi HasFDerivWithinAt off the pole at parametric width; |det| = |z|^{minAdm-1};
  injectivity off pole; the a.e.-analytic c-o-v lemma's hypotheses).
ROUTE B — generalize the (2,3,1) `RadialMPChart` route to parametric width: psi=Q∘shear MP+embedding +
  R radial + weighted source. Cost: generic r×r Gram-inverse measurability (no explicit formula) + a
  PARAMETRIC core-shear split (vs the hand Fin-9 peel) + the weighted sub-box divergence at parametric
  r·c.

QUESTIONS:
1. Which route generalizes to PARAMETRIC widths with less new Lean and less width-induced fragility?
   Be concrete about the worst sub-obstacle of each (Route A: the a.e.-analytic c-o-v lemma's exact
   hypotheses + proving rational HasFDerivWithinAt off the pole at opaque Fin (M k) widths; Route B: the
   parametric MeasurableEquiv core split + generic nonsingInv measurability).
2. For the HARDEST shared sub-piece — proving the rational chart's Jacobian |det| = |z|^{minAdm-1} at
   PARAMETRIC width — is the block-triangular (identity-front ⊕ radial-pivotBlowup ⊕ identity-spectator,
   minus the det-neutral shear shift) argument cleanly Lean-able generically, or does it need per-M
   width plumbing that defeats the ∀M goal?
3. Is there a THIRD option I'm missing — e.g. reduce the smeared atom to the already-banked CLEAN ∀M
   atom by a measure-preserving change that absorbs the rational shear (since the shear is det-1 unit-
   triangular, it's measure-preserving, so the smeared box-integral EQUALS a clean-shaped box-integral)?
   If the rational shear is globally measure-preserving (a measurable bijection off a null set), can the
   smeared divergence be transported to the radial-only (clean-like) divergence, reusing the banked
   `routeMCore_box_diverges_of_RadialMPChart` once with psi = the shear and R = the radial, but with the
   r×r generic structure — and is THAT the minimal path?

Give a concrete recommendation (A / B / hybrid) + the spine of the recommended Lean construction at
PARAMETRIC width + the single biggest risk to flag. Note Mathlib v4.29 has no explicit n×n inverse
formula lemmas beyond fin_two; Matrix.nonsingInv = Ring.inverse(det) • adjugate.
