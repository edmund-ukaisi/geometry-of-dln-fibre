# Review - A2 retained-passive D and L recurrences

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `McClintock the 3rd`.

## Scope

Audit the pen-and-paper note
`reproduction-a2-retained-passive-d-l-recurrence.md` and the corresponding
finite Lean scope in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`.

The review checked:

- the Schur residual calculation for
  `[A1_p, -A1_p F2_p; A3_p, C_p - A3_p F2_p]`;
- the residual-field orientation `D_p = D_{p+1} * C_p`;
- the sign and order of the lower-unitriangular contribution
  `-(D_{p+1} * A3_p * Ctop_p^-1)`;
- whether this is a sound narrow rung toward the omitted `A3_last` endpoint
  formula.

## Verdict

PASS, with caveats.

## Checks

The Schur residual calculation is correct:

```text
schurResidualBlock M_p = C_p
```

using `A1_p^-1 * A1_p = I` and the convention

```text
LR - LL * TL^-1 * UR.
```

The D orientation is correct:

```text
D_p = D_{p+1} * C_p,
```

not `C_p * D_{p+1}`.  Thus the iterated residual field is the ordered product

```text
D_i = C_{N-1} * ... * C_i,
```

matching `residualFactorProduct C (Fin.last N) i hi`.

The L lower-left contribution has the right sign and order:

```text
F3_p = F3_{p+1} - D_{p+1} * A3_p * Ctop_p^-1,
```

where `Ctop_p = Ctop_{p+1} * A1_p`.  Parenthesize the new contribution as
`-(D_{p+1} * A3_p * Ctop_p^-1)` to avoid ambiguity.

## Caveats

The D recurrence alone does not prove `A3_last`.  That endpoint theorem still
needs the iterated L/F3 recurrence, finite-sum formalization, `D_N = I`, and
right cancellation by the unit `Ctop_last`.

The Lean theorems still assume a full determinant-unit family
`A1 : Fin N -> Matrix rho rho K`, including `A1_0`.  They are not yet the
retained-passive coordinate-domain theorem where `A1_0` is constructed from
active `Ctop_0`.

## Nonclaims

No source-chart construction, source-rank coverage, source/image equality,
source-measure pushforward, Jacobian/density transport, normal crossings, pole
order, or RLCT is proved.
