# Statement card - A5 Lemma 5 equation (5) alpha-family source label

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaFamily_mem_iff_guards`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaFamily_actualWidthLabel_at_of_widthBound`

## Claim

Membership in the strict Eq5 alpha domain is exactly

```text
1 <= alpha,
alpha <= aoyagiLemma5IntervalExcess ell a p,
alpha < p.
```

Under Definition 3 selected-width hypotheses, source-index bounds
`1<=S<=L`, actual-width dominance `W_p<=n(S+1)`, and
`k=Htilde'_p+1-alpha`, that alpha-domain membership implies
`actualWidthLabel L n S k`.

## Proved

Lean proves the guard equivalence by finite interval arithmetic and proves the
actual-label wrapper by unpacking the domain membership and calling the
existing Eq5 source-label theorem.

## Assumed

The wrapper assumes the selected-width hypotheses, explicit source-index
bounds, explicit actual-width dominance, and the label relation for `k`.

## Deferred

Displayed-vector construction, branch existence, cutoff guard, selected-span
coverage, terminal `tilde t=0`, vector admissibility, chart sequence,
classifier/injection/back-to-label coverage, Lemma 5 order count, pole order,
normal crossings, and RLCT extraction.

## Review

- xhigh source-slice scout `Avicenna` recommended this as the next smallest
  safe Eq5 follow-up.
