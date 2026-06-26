# Review - A2 p.13 passive-variable local source chart boundary

Date: 2026-06-26.

Reviewer: Arendt the 2nd, xhigh read-only.

## Verdict

No blocking findings after the wording repair below.

## Finding Addressed

- Low: the first draft over-compressed source attribution by making Lemma 2
  sound like the source of the accumulated one-step formulas
  `Ctop = C1 A1` and `F3 = F3old - D A3 Ctop^{-1}`.  Lemma 2 supplies the
  Schur-complement formulas; the accumulated `Ctop` and `F3old` formulas come
  from Theorem 3's induction step using Lemma 2.

The reproduction now says that Lemma 2 is used inside Theorem 3's induction
and clarifies that the displayed target tuple order is the raw-shaped order
used by the determinant-facing measure API.

## Checks

- The signs in the one-step formulas match the current Lean convention:
  `F2 = -A1^{-1} A2`, `F3 = F3old - D A3 Ctop^{-1}`, and
  `A4 = C - A3 F2` in the inverse.
- The note correctly separates the full one-step raw determinant chart, the
  p.13 reduced section, and a hypothetical retained-passive multi-step source
  chart.
- The note does not claim local source coverage, full raw-Haar transport,
  source-density transport, or a retained-passive local inverse from Aoyagi
  pp. 10-13.
- No Lean theorem should be attached to this audit without an explicit
  retained-passive source map, coverage theorem, and density/Jacobian package.
