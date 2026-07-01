# Review - A2 Case 2 baseJ raw-Haar inverse-Jacobian domination

Date: 2026-07-01.

Status: controller review PASS; xhigh scout `Laplace the 3rd` independently
confirmed the theorem boundary and API stack.

## Checks

- The theorem is about `baseJ`, so the extra forward-Jacobian upper scalar
  `ofReal K` is present.
- The determinant-chart domination hypothesis remains explicit and is still
  about the unweighted `passiveSource`.
- The target density is the raw-order inverse-Jacobian density, not the
  previous source-side formal product readback density.
- The proof composes two inequalities:

```text
Measure.map rawMap (baseJ.restrict V)
  <= ofReal K • Measure.map rawMap (passiveSource.restrict V)
```

and

```text
Measure.map rawMap (passiveSource.restrict V)
  <= c • rawHaarInvJac.
```

Thus the final scalar is `ofReal K * c`.

## Boundary

This is still a conditional socket.  It removes no determinant-chart Haar
transport hypothesis and makes no exact raw-Haar pushforward claim.
