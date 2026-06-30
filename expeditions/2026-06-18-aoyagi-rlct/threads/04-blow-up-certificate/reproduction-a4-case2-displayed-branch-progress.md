# Reproduction - A4 displayed Case 2 branch progress

Date: 2026-06-30.

Status: controller pen-and-paper reproduction before Lean.

## Question

Can the finite Case 2 frontier split be connected to the introduced-label
progress kernel without filling branch source production or branch termination?

Answer: yes, for the continuing branch only.  The stopped branches remain
terminal alternatives.  If the displayed Case 2 pivot at state `(S,J)` is
valid, then Aoyagi's next frontier is:

```text
J+2 <= M(S+1)          continuing same-stage branch
n(S+1) = J+1           actual next-width stopped branch
M(S) = J+1             current-prefix row-exhausted stopped branch
```

where `M(S)` denotes the prefix minimum `prefixMinNat n S`.

## State and Child

The introduced-label progress state is:

```text
s = (S,J),  1 <= S,  S <= L.
```

The continuing child is:

```text
child(s) = (S,J+1).
```

This is only the same-stage continuing child.  There is no child attached to
the two stopped alternatives in this slice.

## Guard Completeness

Assume the displayed Case 2 pivot is valid:

```text
J+1 <= prefixMinNat n (S+1).
```

The existing finite frontier theorem gives:

```text
J+2 <= prefixMinNat n (S+1)
or n(S+1) = J+1
or prefixMinNat n S = J+1.
```

This is guard completeness for the three displayed branch predicates.  The
guards are not made exclusive, because the stopped alternatives can overlap.

## Continuing Progress

The progress kernel already proves that

```text
(S,J) -> (S,J+1)
```

strictly grows `introducedLabelFinset L n S J` by the fresh label `(S,J+1)`
under the weaker bound:

```text
J+1 <= prefixMinNat n (S+1).
```

Therefore both the displayed pivot-validity hypothesis and the stronger
continuing guard imply:

```text
progressStep L n child(s) s.
```

## Source Fidelity

Aoyagi PDF pp. 19-22 support the displayed Case 2 continuation/stopping split
and the same-stage update `J -> J+1` on the continuing branch.  The finite
guard names and introduced-label progress relation are expedition bookkeeping.

## Nonclaims

This does not construct source-production payloads, does not prove that any
payload's source data realizes the child state, does not prove branch guard
exclusivity, does not fill `SelectedEntryBranchTerminationData`, and does not
prove normal crossings, pole order, or RLCT.
