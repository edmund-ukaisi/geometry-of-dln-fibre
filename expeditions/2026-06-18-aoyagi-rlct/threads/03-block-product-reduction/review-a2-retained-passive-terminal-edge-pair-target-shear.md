# Review - A2 retained-passive terminal edge-pair target shear

Date: 2026-06-27.

Reviewers:

- Mendel, xhigh read-only pen-and-paper scout.
- Ramanujan, xhigh read-only Lean/API scout.

Verdict: PASS.

## Checked

- The terminal target-side pair uses
  `p : Fin (M+1) := Fin.last M`.
- The actual target normalization is
  `UF = Dzv.F2_p + rawEdgeTupleA1(Dzv)_p * coord.F2 p.castSucc` and
  `UC = Dzv.C_p + rawEdgeTupleA3(Dzv)_p * coord.F2 p.castSucc`.
- `UF` is identified with the formal `F2` component by the terminal `F2`
  theorem.
- `UC` is identified with the formal `C` component by the all-edge `C`
  unshear theorem instantiated at the terminal edge.
- Source `F2` and `C` recovery correctly reuses the already-landed formal
  recovery identities with the actual normalized pair rewritten to the formal
  pair.
- The theorem avoids expanding `rawEdgeTupleA3` at the terminal edge, reducing
  dependent `Fin.last` transport friction.

## Endpoint Check

For `M = 0`, the unique edge is terminal.  The target shear uses the stored
slot `coord.F2 p.castSucc`, while the formal inverse uses
`coord.F2 p.succ`, and only the latter is the terminal zero slot.  This
distinction is essential.

The theorem does not identify the terminal `F3` factor.  In the one-edge case
that factor is controlled by `LastTop = coord.Ctop`, not by `Tail`.

## Nonclaims Checked

The Lean statements do not claim a nonterminal staged shear, a global
target-side linear equivalence, determinant-one factorization, actual
derivative determinant equality, measure transport, normal crossings, pole
order, or RLCT.
