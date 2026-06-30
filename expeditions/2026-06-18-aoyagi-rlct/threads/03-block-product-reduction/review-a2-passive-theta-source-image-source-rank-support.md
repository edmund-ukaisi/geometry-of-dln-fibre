# Review - A2 passive-theta source-image source-rank support

Date: 2026-06-30.

## Independent Checks

Xhigh mathematical checker `Bohr` approved the statement as a conditional
forward-image result.  The checker identified the Aoyagi correspondence as
Lemma 2 / Theorem 3 retained-passive rank bookkeeping plus the Case 2
selected-entry successor residual block, and warned not to infer the
successor-rank equation from the nonzero pivot condition.

Xhigh Lean/API checker `Anscombe` recommended the implemented route:

```text
pointwise full-theta wrapper
image inclusion by unpacking sourceChart '' V
measure support via measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
```

It also flagged the determinant-chart evidence on `V` as the only local datum
that needed to be exposed by the existing source-image theorem.

## Verdict

PASS, conditional on the Lean verification recorded in the controller
synthesis.

## Boundaries

The result is one-way support only.  It proves no source-rank coverage, no
source-image equality, no original/source-prior transport, no Haar transport,
no normal crossings, no pole order, and no RLCT extraction.
