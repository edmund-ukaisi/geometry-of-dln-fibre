# Review - A6 Definition 3 `L=2` triangle parity formula package

Date: 2026-06-24.

Reviewer: Hubble the 3rd, xhigh.

Verdict: PASS.

## Scope Reviewed

Lean file:
`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

Theorems:

```text
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_odd_rankWidth
AoyagiDefinition3SourceData.exists_consecutive_three_widths_theorem2Formula_of_triangle_even_rankWidth
```

Reproduction:
`reproduction-definition3-l-eq-two-triangle-parity-formula-a6.md`

Statement card:
`statement-card-a6-definition3-l-eq-two-triangle-parity-formula.md`

## Findings

No required changes.

The all-source `L=2`, `ell=2` triangle specialization is faithful to Aoyagi
Definition 3/Theorem 2 on pp. 8-9: the selected inequalities are exactly

```text
2*w_i < w1+w2+w3,
```

and the nonselected clauses are vacuous because all three source layers are
selected.

The parity arithmetic is correct:

- odd `T`: `T = 2*(T/2)+1`, `ceilWidth=T/2+1`, `aParam=1`, order `2`;
- even `T`: triangle strictness forces `T>0`, so
  `T = 2*(T/2-1)+2`, `ceilWidth=T/2`, `aParam=2`, order `1`.

The theorem names are precise enough and the reproduction/statement card do
not overclaim beyond finite Definition 3/Theorem 2 arithmetic.

## Nonclaim Check

No Eq5 payloads, chart certificates, final sockets, normal crossings, pole
order, or RLCT are constructed.

## Verification

Reviewer reports focused elaboration passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Controller additionally reran:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```
