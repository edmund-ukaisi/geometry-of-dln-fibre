<task>
Lean 4 / Mathlib formalisation SCOPE/EFFORT adjudication. I was asked to build the
achiever-divergence atom for the (r,r,4) family ∀r (the R1 LOWER bound), expected to be a
"bounded reshape mirroring an hfin reshape on the divergence side." I'm finding it may be a
genuine WALL instead. Adjudicate: bounded build or research-scale wall?

## The setup

The goal `routeMCore_box_diverges_achiever (![r,r,4])`: for c' ≥ ½·minAdm, the box integral
∫_{cube ε} |routeMCore (![r,r,4])|^{−c'} = ⊤ for all ε>0. There is an M-AGNOSTIC assembly
`routeMCore_box_diverges_of_nodeChart M (W : NodeAchieverChart M)` that is PROVEN — it takes a
`NodeAchieverChart M` bundle and produces the divergence atom. So my task reduces to: CONSTRUCT
`NodeAchieverChart (![r,r,4])` ∀r.

## What NodeAchieverChart M requires (the fields I must instantiate, ∀r)

A structure with these M-specific fields:
- `phi : (Fin N → ℝ) → (Fin N → ℝ)` — the chart map (an explicit "Schur-frame ∘ radial blow-up"
  diffeomorphism in flat coordinates), N = flatDim(![r,r,4]) = r·r + r·4 = r²+4r.
- `p` — binding pivot axis; `leafH : Fin N → ℕ` the Jacobian exponents with `leafH p = minAdm−1
  = 4r−5`.
- `Ufun`, `Ubound` (compact bound + a.e.-positivity), `Umeas` — the unit factor of F∘phi = u_p²·U.
- `leaf_integrand` — the a.e. identity `(∏_j |u_j|^{leafH j})·|F∘phi|^{−c} = monomialIntegrand·U^{−c}`.
- `cov` — the change-of-variables: `∫_{phi''(V∖{u_p=0})} g = ∫_{V∖{u_p=0}} ofReal(∏|u_j|^{leafH j})·g(phi u)`.
  This is the genuine Jacobian c-o-v (needs `|det Dphi| = ∏_j |u_j|^{leafH j}`).
- `image_subset` — small box [0,δ]^N → cube ε.

## The existing r=3 instance (achieverChart334) — the template

The (3,3,4) instance (`achieverChart334`) is the "depth-2 miracle": a single weighted radial
blow-up `phi334` with EXPLICITLY-COMPUTED Jacobian `|det Dphi| = |u 0|⁷·|u 1|²` (the 7 = r²−2 at
r=3), built from three bespoke verified-exact components `pb334 ∘ shear334 ∘ bsubst334`, plus:
- `routeMCore_phi334 : routeMCore M334 (phi334 u) = (u 0)²·U` (the EXACT loss factorization, off a
  verified `loss_schur_blowup_factor`),
- `phi334_abs_det` (the HasFDerivAt Jacobian determinant = |u0|⁷|u1|², sorry-free),
- `phi334_cov` (the Jacobian c-o-v on the doubly-punctured set + null-slice drops),
- `phi334_injOn`, `phi334_zero`, continuity, `Ufun334` bounds.
The whole (3,3,4) instance is ~1285 lines in one file (RouteMLayerCoverGEL2.lean). Three other
bespoke instances exist similarly: nodeChart222, nodeChart3333, nodeChart4422 (each hundreds of
lines, each M-specific).

## My concern (verify or correct)

The hfin reshape I built for (r,r,4) was PURE MP plumbing (a measurable-equiv box reshape +
Tonelli, ~256 lines, generalizing eParams334 — genuinely a bounded reshape). But the divergence
side needs an explicit DIFFEOMORPHISM phi with a COMPUTED Jacobian determinant `|det Dphi| =
∏|u_j|^{leafH j}` and an EXACT loss-factorization `F∘phi = u_p²·U`. For ∀r this means:
- a uniform `phi_{(r,r,4)}` whose blow-up structure + Schur-frame depend on the rank-(r-1?) binding
  stratum (which shifts with r),
- a `HasFDerivAt` Jacobian determinant computation at GENERAL r (the r=3 case `|u0|⁷|u1|²` was a
  bespoke det calc; the ∀r exponent is r²−2 on the pivot — a general-dimension determinant),
- the exact loss factorization `frobSq(prod(![r,r,4]) (phi u)) = (u_p)²·U` ∀r,
- the c-o-v + injectivity + image containment ∀r.

## Questions (rank + answer each, concise)

1. Is constructing `NodeAchieverChart (![r,r,4])` ∀r a BOUNDED build (a clean generalization of
   achieverChart334 from r=3 to ∀r, ~few-hundred lines like the hfin reshape) or a RESEARCH-SCALE
   wall (a dimension-parametrized explicit diffeomorphism + general-r Jacobian determinant + exact
   loss factorization, none of which exist generically)? Give a verdict + the single biggest
   obstruction.

2. Specifically: the r=3 chart `phi334` has a BESPOKE Jacobian `|u0|⁷|u1|²` proven by an explicit
   HasFDerivAt det calc. Is the ∀r analog (`|u_p|^{4r-5}·spectators`, a general-dimension blow-up
   determinant) a known-bounded Lean technique, or does it require building a general-r determinant
   machinery that doesn't exist? (The hfin side had NO Jacobian — it was measure-preserving. The
   divergence side's Jacobian is the crux.)

3. Is there a SHORTCUT that avoids the explicit ∀r chart? E.g. (a) a scaling/homogeneity argument
   (the (r,r,4) loss is degree-2-homogeneous in each layer — can divergence be shown by a 1-D
   radial slice without the full diffeomorphism?), or (b) reducing the box-divergence directly to a
   monomial divergence via a cheaper coordinate argument, or (c) a lower-bound by restricting to a
   sub-locus where the chart is trivial? Rank any viable shortcut.

4. RECOMMENDATION: should I (A) attempt the full ∀r NodeAchieverChart build (if bounded), (B)
   pursue a shortcut from Q3 (if one is viable + cheaper), or (C) report this as a research-scale
   wall + depth-checkpoint to the controller (if neither A nor B is bounded)? Be decisive.
</task>

<output_contract>
Four numbered sections. Q1: bounded/wall verdict + biggest obstruction. Q2: Jacobian-determinant
verdict (bounded technique / needs new machinery). Q3: rank the shortcuts (viable+cheaper / none).
Q4: a single decisive recommendation (A/B/C) with the reasoning. Concise; flag inference vs derived.
</output_contract>

<grounding_rules>
Distinguish what you DERIVE from the structure described (the chart fields, the r=3 template size,
the Jacobian requirement) from what you ASSUME about Lean tactic availability. If a shortcut (Q3)
depends on a fact you can't verify (e.g. "the loss has a 1-D divergent slice"), flag it as an
inference to be checked, not a conclusion. Do not claim the full build is bounded if the general-r
Jacobian determinant is the kind of thing that took ~1285 lines at a SINGLE r.
</grounding_rules>
