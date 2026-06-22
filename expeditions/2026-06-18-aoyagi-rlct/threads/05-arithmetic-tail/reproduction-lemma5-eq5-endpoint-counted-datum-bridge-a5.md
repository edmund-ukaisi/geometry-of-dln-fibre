# Reproduction - Lemma 5 Eq5 endpoint counted-datum bridge

Status: reproduced; Lean checked.

## Source

This slice connects the supplied equation `(5)` terminal-room endpoint chain
to the counted-datum codomain used in Lemma 5.  It uses the previously proved
Eq5 terminal-room binary-prefix deltas and the existing terminal-binary
counted-datum maps-to theorem.

## Calculation

Fix an interior selected coordinate

```text
j in {1,...,ell-1}.
```

The supplied Eq5 endpoint-chain data give:

```text
H_j = T(C.point j - 1).
```

The Eq5 terminal-room binary-delta theorem gives:

```text
Delta_r(H) in {0,1} for all r < ell.
```

Together with the supplied source endpoint `H_0=m_0`, terminal endpoint
`H_ell=0`, selected-width sum, and `a<=ell` from the Eq5 certificate, the
existing terminal-binary maps-to theorem gives:

```text
some (j, H_j) in aoyagiLemma5CountDatumSet ell a M m baseValue
```

whenever `H_j != baseValue j`.

Rewriting by the endpoint-chain equality gives the source-facing endpoint
form:

```text
some (j, T(C.point j - 1)) in
  aoyagiLemma5CountDatumSet ell a M m baseValue
```

whenever `T(C.point j - 1) != baseValue j`.

## Lean Targets

```text
aoyagiLemma5Eq5_endpointChain_countDatumSet_mem_of_terminalRoom
aoyagiLemma5Eq5_endpointValue_countDatumSet_mem_of_terminalRoom
```

## Use

These are counted-datum codomain membership bridges for Eq5 endpoint values.
They avoid restating the binary-delta proof at every counted-datum use site.

## Nonclaims

- No Eq5 vector is constructed.
- No endpoint-chain realisation is constructed; the endpoint correspondence is
  supplied.
- No proof is given that the endpoint value is nonbase.
- No counted-datum classifier, injection, back-to-label coverage, order count,
  pole order, normal crossings, or RLCT extraction is proved.
