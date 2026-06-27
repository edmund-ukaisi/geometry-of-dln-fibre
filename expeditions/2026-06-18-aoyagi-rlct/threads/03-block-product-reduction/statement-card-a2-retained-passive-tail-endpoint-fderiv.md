# Statement Card - A2 Retained-Passive Tail Endpoint Frechet Derivative

## Lean Files

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesDerivative.lean
```

## Intended Lean Names

```text
fderiv_retainedPassive_A1TailAfterFirst_zero_apply
fderiv_retainedPassive_A1TailAfterFirst_succ_apply
fderiv_retainedPassive_A1TailAfterFirst_pos_apply
```

## Reproduction

```text
reproduction-a2-retained-passive-tail-endpoint-fderiv.md
```

## Claim

For `M=0`, the retained-passive tail after the first edge is the empty product,
so

```text
d(Tail_0)_z(v) = 0.
```

For a nonempty passive tail, the preferred positive-length wrapper assumes
`hM : 0 < M` and lets

```text
q = ⟨0, hM⟩ : Fin M,
p = q.succ,
Psucc(y) = residualFactorProduct A1seed(y) (Fin.last (M+1)) p.succ.
```

Then

```text
d(Tail_M)_z(v)
  = d(Psucc)_z(v) * A1seed_z(p) + Psucc(z) * v.A1passive_0.
```

The successor-indexed theorem gives the same formula after writing the
positive tail length as `M+1`, avoiding the explicit positivity witness.

## Proof Plan

1. In the zero case, unfold `retainedPassiveA1TailAfterFirst` and reduce to
   the derivative of the constant identity matrix.
2. In the successor or positive case, identify the tail map with the recurrence
   theorem's `Pcast` for the first passive index.
3. Apply
   `fderiv_retainedPassive_A1seed_residualFactorProduct_succ_castSucc_apply`.
4. Rewrite only by definition/proof irrelevance; do not add determinant-chart
   hypotheses.

## Status

Pen-and-paper reproduction written and Lean implementation proved.
Pen-and-paper scout `Goodall`, Lean/API scout `Bohr`, and independent xhigh
implementation review `Russell` passed.  Focused and full `DLNFibre` builds
passed.  `scripts/sorries` reported `0 sorry`, `0 #exit`, `0 native_decide`,
and `0 axiom`; `git diff --check` passed.  Axiom audit for the three new
theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.

## Nonclaims

This is not a closed finite-sum formula for `dTail`, not inverse-tail
differentiation, not full `Ctop` source staging, not `F3` source staging, not
determinant equality, not measure transport, not normal crossings, not pole
order, and not RLCT.
