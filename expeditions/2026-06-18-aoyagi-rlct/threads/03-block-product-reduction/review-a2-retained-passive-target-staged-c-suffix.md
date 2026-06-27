# Review - A2 target-staged `C` suffix derivative

Date: 2026-06-27.

Reviewer: xhigh `Maxwell the 2nd`.

Verdict: PASS.

## Findings

No mathematical or formalisation inaccuracies were found in the reviewed diff.

The generic suffix starts at vertex `m`: `retainedPassiveCSuffixProductAt`
uses `⟨m, ...⟩` as the residual-product start, and the recursive step unfolds
through `p := ⟨m, hm⟩`.

The product-rule order is preserved:

```text
dCsucc * data.C p + Csucc z * recoveredC p.
```

No matrix factors are commuted.

The `Cnext` specialization starts at `r.succ` with `r := q.succ`, both in the
staged definition and in the concrete Frechet-derivative comparison.

Terminal behavior is scoped correctly: the staged derivative of the empty
successor suffix becomes zero, but the lower-left core still has the full
term

```text
dCnext * data.C r + Cnext z * dCcur.
```

Thus it does not drop `Cnext * dC_r`.

The wrapper only removes the explicit `dCnext` slot; `dAcur`, `dPsucc`, and
`dNext` remain supplied arguments.

## Boundary

This checkpoint does not prove the full recursive target-only lower-left
recurrence, determinant-one target normalizer, determinant equality,
source-prior or measure transport, normal crossings, pole order, or RLCT.
