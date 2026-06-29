<task>
A Jacobian-determinant factorization for a structured chart map phi: R^N -> R^N is being formalised in
Lean 4 / Mathlib. The radial direction has been pinned: phi = B ∘ blowup, where blowup = pivotBlowupOn(active, p)
is a pivot blow-up (x_p -> x_p; x_i -> x_p*x_i for i in `active`; else x_i), and B is a "de-radialized chart".
We need the LEAST-cast way to DEFINE B constructively (as a Lean map) so that det Dphi = det(DB)·det(D blowup)
via LinearMap.det_comp. Derive the construction yourself; do not assume our candidate is right.
</task>

<facts_established_exactly_sympy>
- blowup = pivotBlowupOn(active, p). Its Frechet derivative is an ARROW matrix (diagonal + pivot column);
  det = x_p^(|active|-1). It is NOT globally invertible (degenerate at x_p = 0).
- KEY structural fact (proven exactly at N=8 and N=27): every active coordinate x_i (i in active, i != p)
  occurs in phi ONLY multiplied by the pivot, i.e. phi's polynomial entries contain x_i only inside the
  monomial x_p * x_i (never x_i alone, never x_i times another free coord, never x_p^2).
- Consequence verified exactly: defining B by the formal substitution x_i -> y_i/x_p (i in active),
  x_p -> y_p, x_j -> y_j (spectators), the 1/x_p ALWAYS CANCELS — B is a POLYNOMIAL (division-free) map of y.
  And B(blowup(x)) = phi(x) holds as maps (identity of polynomials).
- Verified exactly: |det DB| equals the desired "boundary/engine" product (u-free), and
  det Dphi = det(DB)·det(D blowup) = (engine product) · x_p^(|active|-1).
</facts_established_exactly_sympy>

<lean_context>
Two candidate ways to obtain B in the existing Lean development:
(i) A "composeFold" framework: phi is expressed as a foldr-composition of a List of "ChartFactor"s, each a
    full-ambient self-map (Fin N -> R) -> (Fin N -> R) carrying its HasFDerivAt and per-point det. There is a
    banked theorem composeFold_abs_det : |det D(composeFold fs) u| = ∏ |det (D f_i at its prefix)|, and
    composeFold_hasFDerivAt (chain rule, automatic). The radial factor pivotBlowupOn is ALREADY a full-ambient
    ChartFactor (banked, radialFactor). The boundary factors (Schur frame, LDU core) currently live on small
    spaces (SchurInc t r c, LDUParam t) and would need conjugating into full-ambient (Fin N -> R) factors.
(ii) A banked "staircase conjugacy" theorem: it requires a hypothesis hconj of the form
    fderiv phi u = e.symm ∘ stairMap V (L+1) f c ∘ e, where e : (Fin N -> R) ≃ StairProd V (L+1) is a SINGLE
    global linear equiv regrouping ALL coordinates, stairMap is a block-lower-triangular map with diagonal
    blocks f_s, and c the couplings. Layer 0's f_0 is exactly the radial arrow; layers s+1 are the engine blocks.
    Building hconj is the "compute the fderiv VALUE as a staircase over opaque widths" cost (cast-heavy).
</lean_context>

<questions>
1. Given the established fact "every active coord appears in phi only as x_p*x_i", is the cleanest CONSTRUCTIVE
   definition of B simply: "phi, but reading the active input-slots directly (not blown up)"? Concretely, is B
   = phi ∘ section, where section : R^N -> R^N is x_p->x_p, y_i (i active)-> treat as the value x_p*x_i already,
   spectators identity — i.e. does B have an elementary closed form NOT requiring the inverse of blowup?
   State the cleanest B you can define directly (no division, no inverse), and the identity that must be proven
   (phi = B ∘ blowup) — at the MAP level.

2. For Lean det purposes we need det Dphi = det(DB) · det(D blowup). Given phi = B ∘ blowup as maps and both
   differentiable, is this just HasFDerivAt.comp + LinearMap.det_comp, with NO need to invert blowup or to
   evaluate at x_p != 0? Confirm the chain-rule/det-comp argument is division-free and valid at x_p = 0.

3. Compare the two routes (i) composeFold-with-B-as-the-non-radial-factors vs (ii) global stairMap conjugacy.
   Which is LEAST-cast for proving det Dphi = (engine) · x_p^(|active|-1) faithfully? Is the two-factor
   phi = B ∘ blowup (one det_comp) strictly simpler than either a long composeFold list OR the global e?
   What is the irreducible obligation in each (the map-equality phi = B∘blowup; the per-engine |det DB|;
   the full hconj)?
</questions>

<output_contract>
For each question: a direct answer + the precise Lean-level obligation it leaves. For Q3, a ranked recommendation
(least-cast first) with the irreducible proof obligation of each route named. Mark proof vs heuristic.
</output_contract>

<grounding_rules>
The sympy facts are exact. Reason about Lean/Mathlib feasibility at the level of "what equality must be proven",
not tactic details. Do not rubber-stamp; if B-as-a-map hides a cast cost comparable to the global e, say so.
</grounding_rules>
