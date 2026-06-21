# Statement card - A5 Lemma 5 counted-datum maps-to adapters

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5CountDatumSet_mem_of_HtildeBounds`

## Claim

At an interior coordinate `j`, any non-base Htilde interval value determines a
nonbase counted datum:

```text
some (Sigma.mk j H) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

The second theorem gives the same conclusion from explicit same-coordinate
Htilde bounds.

## Proved

The interval-membership theorem rewrites the counted-datum membership
characterisation and uses `Finset.mem_erase`.  The bounds theorem first uses
`aoyagiHtilde_mem_intervalValueSet_iff_bounds` and the natural-indexed
interval wrapper.

## Assumed

The coordinate is interior, the value is not the supplied base value at that
coordinate, and for the bounds theorem `a <= ell` plus the two Htilde bounds
are supplied.

## Deferred

Source branch construction, Eq3/Eq4/Eq5 vector construction, terminal chain
production, classifier injectivity, back-to-label coverage, no-extra
terminal-minimum coverage, Lemma 5 order count, pole order, normal crossings,
and RLCT extraction.

## Review

Focused Lean check passed for `DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily`.
Independent xhigh reviewer `Heisenberg` found no fidelity or claim-soundness
break.
