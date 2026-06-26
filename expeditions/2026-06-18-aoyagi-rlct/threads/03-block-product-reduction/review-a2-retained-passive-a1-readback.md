# Review - A2 retained-passive A1 readback

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Hubble the 3rd`.

## Scope

Audit the proposed constructor-side readback theorem in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_A1_eq_suffixState_Ctop_inv_mul_Ctop
```

The review checked the algebraic order, source fidelity against
`reproduction-a2-retained-passive-coordinate-domain-inverse.md`, and whether
the theorem risks overclaiming the actual retained-passive coordinate-domain
construction.

## Verdict

PASS, with a scope caveat.

## Checks

From the Ctop recurrence

```text
Ctop_p = Ctop_{p+1} * A1_p
```

and the determinant-unit fact for `Ctop_{p+1}`, left cancellation gives

```text
A1_p = Ctop_{p+1}^-1 * Ctop_p.
```

The order is correct.  The reviewed theorem does not use the noncommutative
wrong formula `Ctop_p * Ctop_{p+1}^-1`.

## Caveat

The theorem still assumes a full family

```text
A1 : Fin N -> Matrix rho rho K
```

and a unit-determinant hypothesis for every `A1_p`.  Therefore, at `p=0`, it
reads back an already supplied `A1_0`.  It does not yet define or recover the
omitted active endpoint variable from the retained-passive coordinate domain.

The actual endpoint theorem should be framed separately with active
`Ctop_0 = I + X` and passive `A1_p` for `p > 0`.

## Nonclaims

Do not present this theorem as a retained-passive source-map readback theorem
or source-chart/domain theorem.  It is a finite constructor-side readback
lemma only.  It proves no `A3_last` recovery, source coverage, source-measure
pushforward, Jacobian/prior density theorem, normal crossings, pole order, or
RLCT.
