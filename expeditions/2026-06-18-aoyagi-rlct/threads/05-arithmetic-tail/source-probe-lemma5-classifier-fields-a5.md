# Source Probe - Lemma 5 classifier fields

Probe: Ptolemy, xhigh-effort subagent.
Date: 2026-06-21.

Source used: Aoyagi 2023 PDF only, with existing Aoyagi expedition notes for
orientation.

## Verdict

The full Lemma 5 upper-bound/no-extra classifier is not proved by the printed
paragraph on PDF p. 26.  The interval count plus the sentence that `J`
increases by one in Case 1(2) does not by itself give a classifier, injection,
or back-to-label map.

## Field Status

- `label-to-vector`: conditional.  Missing data: every terminal minimum label
  must be tied to a legal source label `(s,k)`, a terminal vector `T_{s,k}`,
  the selected-endpoint chain convention, and terminal `tilde t=0`.
- `minimum-to-lambda`: conditional/obstructed from pp. 25-27 alone.  Missing
  data: terminal-exponent normalisation against Aoyagi's `M_{s,k}` and a
  converse bridge from terminal minimum conditions to correspondence with
  `lambda`.  Lemma 4 is sufficient, not a classifier.
- `interval classifier`: partially source-reproducible only as `mapsTo` under
  explicit source-chain hypotheses.  If a chain has terminal `H_ell=0`,
  binary/two-valued increments, total high-count `a`, and the selected-width
  sum, then the binary-prefix arithmetic gives `Htilde_j <= H_j <= Htilde'_j`.
  This does not choose a canonical counted datum or prove injection.
- `Case 1(2) uniqueness/injection`: obstructed.  The sentence that `J`
  increases records local inductive progress, not nonduplication of terminal
  lambda-vectors under a counted-datum map.
- `back-to-label`: obstructed as printed.  The displayed lower-bound families
  `(3)`, `(4)`, and `(5)` still require extra guards and supplied
  terminal/admissibility data before they can be treated as full Lemma 4
  witnesses.

## Next Formal Slice

The recommended next formal direction is a narrow conditional interval
`mapsTo` theorem from terminal/binary chain data to the counted interval
codomain.  It should be documented as `mapsTo`, not as the full no-extra
classifier.
