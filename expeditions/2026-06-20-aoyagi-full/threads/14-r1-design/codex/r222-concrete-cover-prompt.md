<task>
Lean 4 + Mathlib v4.29. I'm building the concrete 24-leaf resolution cover for the (2,2,2) deep-linear
RLCT: prove `∫⁻_U |F|^{-c} = Σ_{24 leaves} ∫⁻_{leaf} |det φ_leaf|·|F∘φ_leaf|^{-c}` and then that each
leaf integrand = `monomialIntegrand d k h c` (a weighted monomial). I have the abstract machinery
PROVEN; I need the cleanest STRUCTURE for the concrete instantiation (the biggest + most
fidelity-critical remaining piece). Give a structural plan + the decisive design choices, NOT full code.

## What's PROVEN (gated/ready, axiom-clean)
- `g5_pivotNode (active : Finset (Fin N)) (U) (hUcov : U =ᵐ ⋃ p∈active, argmaxCellOn active p) (g) :
   ∫⁻_U g = Σ_{p∈active} ∫⁻_{chartDomOn active p \ pivotZeroOn p} ofReal|det(pivotBlowupOnDeriv active p x)|·g(pivotBlowupOn active p x)`
   — ONE blow-up node (pivot family on a coordinate subset, spectators fixed), all 6 obligations discharged
   from atoms. `pivotBlowupOn active p x = if i=p then x p else if i∈active then x p*x i else x i`;
   `det = (x p)^(active.card-1)`.
- Cover→rlct spine (S1Cover): `cover_integral_lt_top_iff`, `rlctAtOn_ge_of_integral_lt`, `rlctAtOn_le_of_adm_le`.
- Per-leaf: `monomialIntegrand_integrable_of_lt` (c'<monomialThreshold ⟹ leaf integral finite, 0<c').
- `monomialIntegrand d k h c u = (∏ⱼ|uⱼ|^{hⱼ})·(∏ⱼ|uⱼ|^{2kⱼ})^{-c}`; `monomialThreshold = sSup{adm}`.

## The concrete (2,2,2) cover (pp's design, sympy-verified)
F = ‖A·B‖² on Fin 8 → ℝ (A,B 2×2; a00=slot0..b11=slot7). The resolution tree, 4 nodes:
- STEP 1: blow up the A-block (active = {a-slots}), 4 pivots, |det|=x³ (pivotBlowupOn, n+1=4). F = x²·Q.
- LEMMA-2: a HOMEOMORPHISM (det ±1, polynomial change of coords (t1,t2,t3,B)→(E,F0,δ,q,G,H)) making
  Q = E²+F0²+(qE+δG)²+(qF0+δH)², center {E=F0=δ=0}. NOT a cover — a regular reindex.
- STEP 2: blow up {E=F0=δ=0} (active = those 3 slots), 3 pivots, |det|=s². E/F0-pivot → UNIT leaf
  (Q=s²·unit, unit(0)=1) ⟹ x²s²·unit; δ-pivot → smooth-4-block (needs step 3).
- STEP 3 (δ-branch): blow up the 4-block vertex, 4 pivots, |det|=u³ ⟹ x²s²u²·(1+Σ³z²) = monomial×unit.
Result: 8 UNIT leaves (Jac x³s², integrand → monomialIntegrand 2 ![1,1] ![3,2]) + 16 BLOCK leaves
(Jac x³s²u³, → monomialIntegrand 3 ![1,1,1] ![3,2,3]). Both monomialThreshold = 3/2.

## The questions
1. THE 3-DEEP COMPOSITION SHAPE: g5_pivotNode gives `∫⁻_U g = Σ_p ∫⁻_{V_p} w_p·(g∘φ_p)`. To go deeper I
   recurse on `g' := w_p·(g∘φ_p)` over the SAME Fin 8 → ℝ. But each node's `active` set differs (A-block,
   then (E,F0,δ)-slots, then 4-block), and the Lemma-2 homeomorph sits between step1 and step2. What's the
   cleanest way to thread the Lemma-2 reindex into the g5_pivotNode chain — (a) treat Lemma-2 as a
   measure-preserving homeomorph and `rw` the inner integral through it (∫⁻_V g'∘L2 = ∫⁻_{L2''V} g', via
   the m.p. + a coordinate rewrite), OR (b) absorb it into the step-1 charts (φ_step1-then-L2 as one map,
   so step-2's g5_pivotNode sees the already-L2'd coords)? Which keeps the per-leaf Jacobian bookkeeping
   (x³ · 1 · s² · u³) cleanest?
2. THE PER-LEAF "integrand = monomialIntegrand" BRIDGE (fidelity-critical, the load-bearing link): after
   the composition, a leaf integrand is `|det φ_composite|·|F∘φ_composite|^{-c}` on the leaf chart domain.
   I must show this EQUALS `monomialIntegrand d k h c` (in the leaf's local coords) so the leaf's
   `monomialThreshold` is its actual rlct. This needs (i) `F∘φ_composite = (∏|uⱼ|^{2kⱼ})·unit` (the loss
   becomes monomial×unit — requires the Lemma-2 factoring + the blow-up substitutions) and (ii)
   `|det φ_composite| = ∏|uⱼ|^{hⱼ}`. The unit factor `unit(0)≠0` is the subtlety (monomialIntegrand has NO
   unit factor — it's bare monomial). How is the unit handled — is `monomialThreshold` of the leaf the same
   WITH the unit (a bounded-away-from-0 factor doesn't shift the threshold)? Do I need a "threshold is
   unit-invariant" lemma (|unit| ∈ [m,M] on a nbhd ⟹ same integrability threshold), and is that the
   S1.3-style ideal-invariance I already have, or new? This is THE crux — advise the cleanest formulation.
3. SCOPE/DECOMPOSITION: the controller wants (1) the cover ∫=Σ∫ gated first, then (2) the min-connection.
   Given the Lemma-2 homeomorph + the unit-factor subtlety, is there a SINGLE-LEAF validation (prove ONE
   representative leaf's integrand=monomialIntegrand end-to-end) worth doing first to de-risk, before the
   full 24? And is the unit-invariance (Q2) better proven abstractly (reusable) or per-leaf?

## Output
Q1: ranked (a)/(b) for the Lemma-2 threading + decisive reason. Q2: the cleanest unit-factor handling
(is it unit-invariance-of-threshold? do I have it (S1.3) or need it? exact lemma shape) — THE crux, be
concrete. Q3: single-leaf-first yes/no + unit-invariance abstract-vs-per-leaf. Terse; name Mathlib/my
lemmas confident vs unverified.
</task>

<output_contract>
Q1: (a)/(b) ranked + reason. Q2: the unit-factor/threshold-invariance formulation (concrete lemma shape +
whether it's existing S1.3-style or new). Q3: single-leaf-first + abstract/per-leaf calls. Flag the
load-bearing risk honestly.
</output_contract>

<grounding_rules>
Distinguish confident-v4.29 Mathlib names from inferred. If the unit-factor handling is genuinely subtle
(it's the fidelity crux), say so plainly — don't paper over whether monomialThreshold-of-the-leaf actually
equals the leaf's rlct in the presence of the unit factor.
</grounding_rules>
