# Thread 06 - DLN translation

Type: formalisation. Status: active; first formula-notation slice landed.

## Task

Translate Aoyagi's notation and final formula to this repo's DLN notation
using Aoyagi's paper as the only mathematical source.

## Output contract

- Dimension/rank convention map.
- A theorem or statement card showing the local Aoyagi formula in repo notation.
- Explicit warning that Aoyagi's `theta` is RLCT order/multiplicity and should
  use a distinct Lean/display name such as `rlctOrder`.

## Controller notes

Do not consult the Lehalleur-Rimanyi source for this translation. Any later
comparison belongs outside this Aoyagi-only expedition.

## Current slice - 2026-06-22

The first A6 Lean layer is
`lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`, imported by
`lean/DLNFibre.lean`.

It translates Aoyagi Definition 3 and Theorem 2's displayed arithmetic into
source-facing notation:

- integer reduced widths `M^(s)=H^(s)-r`;
- indexed selected reduced widths from `AoyagiSelectedCutpoints`;
- a separate selected value set helper, not used for sums;
- `AoyagiDefinition3CeilData`, separating the selected object from the
  ceiling integer `ceilWidth` and recording `0 < ell`, `0 < a <= ell`;
- the Theorem 2 order formula as `theorem2OrderFormula`, not `theta`;
- the three displayed `lambda` formula definitions and elementary rational
  rewrites among them.

Artifacts:

- `reproduction-definition3-theorem2-translation-a6.md`;
- `statement-card-a6-final-formula-notation.md`;
- `review-final-formula-notation-a6.md`.

Boundary: this is formula bookkeeping only.  It does not prove the full
Definition 3 selection inequalities, existence of the ceiling datum, Lemma 4
or Lemma 5 exponent minimisation, normal crossings, pole order, or RLCT
extraction.
