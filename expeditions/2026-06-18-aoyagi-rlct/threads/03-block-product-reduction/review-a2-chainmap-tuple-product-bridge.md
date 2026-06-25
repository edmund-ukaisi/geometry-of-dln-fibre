# Review - A2 chain-map tuple product bridge

Date: 2026-06-25.

Reviewers: Mill the 5th and Franklin the 5th, xhigh, read-only scouts.

Confirmatory reviewer: Euler the 5th, xhigh, read-only.

Status: passed.

## Findings

No blockers.

The key order convention is correct.  The core prefix product satisfies

```text
multPrefix_succ : prefix(p+1) = A_p * prefix(p),
```

and Aoyagi's source-to-target chain composite satisfies

```text
chainMap_succ : chainMap(i,p+1) = E_p.comp chainMap(i,p).
```

Mathlib's `LinearMap.toMatrix_comp` turns this composite into the same
left-multiplication order:

```text
[E_p ∘ chainMap(i,p)] = [E_p] * [chainMap(i,p)].
```

Thus `submult d M i j` matches `[chainMap(i,j)]`, and `mult d M` is the
zero-to-last specialization.

The theorem needs no `0 < N` hypothesis.  When `N = 0`, both sides are the
identity matrix.  When `N = 1`, both sides are the single edge matrix.

The reverse-vertex wrapper is the right Aoyagi specialization: set
`V = reverseVertex W` and use the given reversed edges.  Later comparison with
paper-order maps should use the existing `chainMap_reverse_eq_paper` theorem
rather than a manual reversal.

## Risks

The theorem assumes Lean's column-vector matrix orientation
`Matrix target source`.  Paper-order row-style products or the separate
`paperMatrixChain` convention require a distinct bridge.

The bases must be a matching fixed family at all intermediate vertices.  If
one compares to another family of bases, basis-change matrices must be inserted
and controlled separately.

This review does not certify a `lossDLN` comparison.  The next step still has
to choose the target matrix in the same endpoint bases and unfold
`lossDLN` as a Frobenius square of `mult d A - B`.

## Confirmatory Review

Euler checked the final patch after the `submult` theorem and reverse-vertex
wrapper were added.  No blockers were found.  The review confirmed the
left-multiplication order for `submult`/`multPrefix`, the matching
left-composition order for `chainMap_succ`, the orientation of
`LinearMap.toMatrix_comp`, and the fact that `mult_toMatrix_chainMap_reverseVertex`
is only the specialization `V = reverseVertex W`.  It also confirmed that the
new aggregate import is appended at the end of `DLNFibre.lean` and that the
notes do not claim a `lossDLN`, statistical, normal-crossing, pole-order, or
RLCT theorem.
