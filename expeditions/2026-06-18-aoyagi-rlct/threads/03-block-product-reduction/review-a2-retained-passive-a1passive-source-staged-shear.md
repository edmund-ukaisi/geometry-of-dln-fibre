# Review - A2 Retained-Passive A1 Passive Source-Staged Shear

Date: 2026-06-27.

Reviewer: Lagrange, xhigh read-only explorer.

## Verdict

PASS for the proposed slice boundary.

## Boundary Check

The Lean statements match the intended scope:

- the nonterminal `solvedA3` projection is only for `p.castSucc`, with no
  determinant-chart hypothesis;
- the terminal `solvedA3` derivative is not source-staged standalone; the
  all-edge theorem only identifies the product after multiplying by the
  successor extended `F2` slot;
- the passive `A1` formula rewrites the old derivative-staged bridge using
  staged successor `F2` and lower-left source tangents only in that component.

## Endpoint Risks

- For the last passive index `p : Fin M`, `p.succ : Fin (M+1)` is terminal and
  must not be treated as nonterminal.
- The terminal `solvedA3` derivative is not zero and not the staged terminal
  lower-left tangent.  Only the identity `coord.F2 (Fin.last (M+1)) = 0`
  kills the product.
- The final passive `A1` theorem still needs the determinant-chart hypothesis
  through the old `A1passive_shear...` bridge, even though the new projection
  and multiplier readout lemmas are more elementary.

## False Statements To Avoid

- `d(solvedA3_q) = X_G q` for all `q`;
- the terminal `solvedA3` derivative vanishes;
- this stages the whole tuple, or stages `Ctop`/`F3`;
- this is a determinant, measure, normal-crossing, pole-order, or RLCT theorem.

## Naming Notes

After `coord := data.toCoordinateData`, the extended field is `coord.F2`.
`F2full` is the nonredundant-data field before conversion.  The multiplier
lemma name is sound but could be clearer if future work renames it to mention
both sides' multiplier explicitly.
