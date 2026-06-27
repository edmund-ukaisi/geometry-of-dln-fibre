# Review - A2 Retained-Passive Actual Derivative C Unshear

Date: 2026-06-27.

Status: reviewed; documentation nit fixed.

Reviewer: xhigh read-only explorer `Euler the 5th`.

## Verdict

Pass after a low-severity documentation correction.

## Findings

The reviewer found no Lean formalization or mathematical accuracy issue in the
new theorems.

One documentation mismatch was found and fixed: the reproduction note had
written the tangent `F2` source as `v.F2 p.castSucc`.  The basepoint
coefficient is indexed as `coord.F2 p.castSucc`, but the tangent vector uses
the stored nonterminal coordinate `v.F2 p`, which is `v.2.1 p` in Lean.

## Checked Points

- `rawEdgeTupleA3_topologyTupleEdgeRawOrder` handles the `Fin.lastCases` split
  correctly, with the passive cases using `rawEdgeTupleA3_castSucc` and the
  terminal case using `rawEdgeTupleA3_last`.
- The component theorem differentiates
  `C p - solvedA3 p * F2 p.castSucc`, then cancels
  `d(solvedA3 p) * F2 p.castSucc` by adding the sheared lower-left derivative
  component.
- The full-derivative theorem only transports the component identity through
  linear projections of the ambient Frechet derivative of
  `topologyTupleEdgeRawOrder`.
- The later bridge corollary
  `C_unshear_fderiv_topologyTupleEdgeRawOrder_eq_formalRawOrderJacobianAt`
  only rewrites this component identity through the point-specialized formal
  raw-order apply formula.
- The notes do not claim a full derivative factorization, full determinant
  formula, measure pushforward, normal crossings, pole order, or RLCT.

## Residual Risk

The notes describe the shear as determinant-one mathematical narration.  This
slice proves the component shear identity, not a global determinant-one shear
linear-equivalence theorem.
