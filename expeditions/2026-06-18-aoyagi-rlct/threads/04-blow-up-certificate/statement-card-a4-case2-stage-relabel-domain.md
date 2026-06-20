# Statement card - A4 Case 2 stage-relabel domain audit

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.introducedLabel_currentSucc_iff_succStage_zero_of_nextWidth_eq`
- `DLNFibre.DLN.Aoyagi.introducedLabelFinset_currentSucc_eq_succStage_zero_of_nextWidth_eq`
- `DLNFibre.DLN.Aoyagi.not_introducedLabel_current_of_lt_index`
- `DLNFibre.DLN.Aoyagi.introducedLabel_succStage_zero_extra_witness_of_nextWidth_ge`
- `DLNFibre.DLN.Aoyagi.case2_next_frontier_currentPrefixMin_or_nextWidth_eq_of_cont_of_not_next`

## Statement

Lean now records the finite label-domain side condition needed for auditing
Aoyagi's terminal Case 2 advance.  If the displayed pivot is valid and the next
continuation bound fails, then

```text
prefixMinNat n S = J+1 or n(S+1) = J+1.
```

Under the stronger actual-width side condition `n(S+1)=J+1`, the introduced
labels at old `(S,J+1)` equal the introduced labels at `(S+1,0)`.

If `J+2 <= n(S+1)`, then `(S,J+2)` is an explicit extra label introduced at
`(S+1,0)` but not at old `(S,J+1)`.

## Proved

- The terminal frontier equality splits into current prefix-row exhaustion or
  actual next-width exhaustion.
- Old `(S,J+1)` and `(S+1,0)` have the same introduced-label predicate and
  finite introduced-label set under `n(S+1)=J+1`.
- A current-layer label above the processed index is not introduced at the
  current state.
- If actual width still contains `J+2`, then `(S,J+2)` witnesses failure of
  unconditional relabeling from old `(S,J+1)` to `(S+1,0)`.

## Assumed

- `1 <= S` for the frontier side split.
- `n(S+1)=J+1` for the relabel equality.
- `1 <= S`, `S <= L`, and `J+2 <= n(S+1)` for the extra-label witness.

## Not Proved

- No `S+1` recurrence/exponent transition.
- No terminal `D'''` block-shape theorem.
- No construction of `C'^(S+1)`, chart production, chart coverage,
  coordinate regularity, Jacobian/volume arithmetic, normal crossings, RLCT
  extraction, termination, transition invariant, or printed-vector repair.

## Reproduction and Review

- Reproduction artifact: `reproduction-case2-stage-relabel-domain-a4.md`.
- Review artifact: `review-case2-stage-relabel-domain-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
