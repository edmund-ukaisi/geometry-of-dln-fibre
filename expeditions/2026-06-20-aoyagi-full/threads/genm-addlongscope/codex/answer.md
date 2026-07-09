**Bottom Line**

I would not scope this as “a few Lean lemmas.” From scratch in Lean 4 + Mathlib v4.29, this is a **multi-module mini-expedition**. If this is the sole remaining project gap, I would strongly prefer **citing/Axiomatizing the classical analytic result** unless the target is a fixed low-dimensional case with an already-written chart proof.

1. **Size Tier**

Point estimate: **tier (c), 20-35 person-weeks** for the general boxed lemma, assuming the mathematical proof is already explicit enough to formalize.

Rough range:

- **Fixed binding case only, hand-enumerated charts:** 8-18 person-weeks.
- **General widths/chains, bespoke explicit charts:** 20-50 person-weeks.
- **Reusable AG/principalisation infrastructure:** 80-200+ person-weeks.

The hard part is not monomial integrability. It is getting the product rank-drop locus into monomial form with enough uniform bookkeeping.

2. **Tractability Probabilities**

My estimate for the general lemma:

- **Explicit measure-theoretic chart route, no AG primitive:** ~35%.
- **Forces principalisation-equivalent machinery / large AG detour:** ~60%.
- **Some unexpectedly simple analytic domination works:** ~5%.

For the single `(3,3,3,4), t=1` case, I would raise explicit-chart tractability to maybe **55-65%**, but only if one accepts a non-reusable, heavily charted proof.

3. **Non-Coordinate Blow-Up Obstruction**

Yes: if the dense-torus witness is real, it kills a **coordinate-center-only** strategy in the original matrix entries. Coordinate blow-ups do not affect dense-torus singular/incidence behavior.

It does **not** logically kill an explicit chart route. You can still use local affine/shear changes, translate the non-coordinate center into coordinate form on a patch, then apply ordinary charted blow-ups. But that is already a bespoke principalisation, just written analytically rather than as AG infrastructure.

I would not expect “blow up one factor at a time” to solve it cleanly. Product rank drop includes incidence conditions like `im(suffix) ∩ ker(prefix) ≠ 0`, not just rank drops of individual factors. Product structure helps organize charts, but does not remove the coupled center.

4. **Weaker Sufficient Form**

A weaker one-sided lemma may exist, but probably not by crude envelopes.

Zero slack kills the standard cheap moves:

- **Fubini separation:** fails because the determinant factor is already at its own threshold.
- **Hölder split:** no room; any `p > 1` pushes the critical determinant exponent past threshold.
- **Crude determinant lower bounds:** usually lose multiplicity/slack and make the majorant divergent.
- **Domination by free-matrix behavior:** likely too pessimistic exactly at the borderline.

What might work is a **coarse joint sublevel-volume estimate**: not exact RLCT, but still a joint estimate for the product of the determinant factor and residual loss. However, proving that in Lean likely requires the same kind of local monomialization/principalisation data, just with less sharp final numerics.

So: weaker than exact RLCT, yes. Weaker than joint resolution-style analysis, probably no.

5. **Top 3 Risks**

1. **Hidden principalisation burden.** The proof may require resolving a coupled incidence/determinantal locus, not merely bounding two known singular factors.

2. **Lean analytic infrastructure cost.** Change-of-variables charts, Jacobian determinants, finite covers, local integrability, a.e. restrictions, and real matrix-coordinate bookkeeping will be expensive in v4.29.

3. **Combinatorial/chart explosion.** Pivot choices, rank strata, product decompositions, and width inequalities can easily dominate the formal proof, especially if stated uniformly in `M_i`.

My scoping recommendation: **cite the classical theorem/result boundary if acceptable**. Build from scratch only if the goal is either a fixed small case or the project explicitly wants a new Lean development of determinantal/principalisation-style analytic estimates.
