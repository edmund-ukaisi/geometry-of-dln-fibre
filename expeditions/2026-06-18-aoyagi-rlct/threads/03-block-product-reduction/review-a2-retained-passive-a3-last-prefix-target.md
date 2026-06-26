# Review - A2 retained-passive `A3_last` prefix target

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Tesla the 3rd`.

## Scope

Audit the uncommitted Lean additions in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveA3WithoutLast
ChartLocalSuffixState.retainedPassiveA3WithoutLast_last
ChartLocalSuffixState.retainedPassiveA3WithoutLast_eq_of_ne
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_withoutLast_last
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq
```

The review checked the sign convention for the earlier signed tail, the
nonempty final-edge indexing, determinant-unit usage, and the nonclaim
boundary.

## Verdict

PASS.  No blocking findings.

## Checks

- `A3early` zeroes only the final edge.
- `EarlyTail = Tail_0(A3early)` is the signed earlier contribution, so the
  paper-facing unsigned prefix is `-EarlyTail`.
- The hypothesis
  `A3_last = -(F3 - EarlyTail) * Ctop_last` is equivalent to
  `A3_last = -(F3 + Prefix) * Ctop_last`.
- The split theorem is indexed over `m ≤ M` for an edge family `Fin (M+1)`;
  the base case is the final edge and the induction step only uses
  non-final `p`.
- The only determinant-unit cancellation is inherited from the endpoint theorem
  and is on `Ctop_last.det`.
- No inverse or cancellation of a residual `C` factor is introduced.
- The reproduction and statement card do not claim a full coordinate domain,
  `A1_0` reconstruction, coverage, measure transport, normal crossings, pole
  order, or RLCT.

## Verification

The reviewer ran:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

The focused build passed.

## Follow-up

The next retained-passive target should package the coordinate-domain source
map using active `Ctop_0` and `F3`, passive `A1_p` for `p>0`, the existing
`A1_0` readback algebra, and this `A3_last` prefix-target theorem.
