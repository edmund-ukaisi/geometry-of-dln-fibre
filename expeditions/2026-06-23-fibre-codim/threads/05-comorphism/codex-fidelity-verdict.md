# Codex decorrelated fidelity verdict (F1 review, 2026-06-23)

Model: gpt-5.1-codex-max, reasoning effort high. Prompt in `codex-fidelity-prompt.md`.

## Question A — the bridge (eval_multPoly): PASS
- Not definitionally rfl: multPoly builds the matrix product in the polynomial ring, then evaluation
  is pushed through by ring-hom properties (Matrix.map_mul / Matrix.map_one). Induction on prefixes
  is the honest way to commute evaluation with the iterated matrix product.
- No hidden commutativity smuggled: only k-commutativity (needed for MvPolynomial/eval) is used;
  matrix multiplication stays noncommutative; Matrix.map_mul holds for any semiring hom.
- The single-variable step (genericTuple i).map (eval …) = A i is substantive, not a definitional
  loop. Statement faithfully captures "plug A's coordinates into the generic product to recover mult d A".

## Question B — the Ideal.map identity: PASS (with scope note)
- multComap is the comorphism X_rc ↦ multPoly rc; mapping span{X_rc − B_rc} along it yields exactly
  span{multPoly rc − B_rc} — the standard "extension of the point's maximal ideal along the comorphism".
- maxIdealOfPoint is the usual kernel of evaluation-at-B in the target algebra; non-circular, meaningful.
- Name fibreGenIdeal is appropriate for a generated ideal; the lemma does NOT claim it is radical or
  the full vanishing ideal — no overclaim. Radical equality is a separate statement (Claim 4).
