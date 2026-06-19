# Thread 04 - blow-up certificate

Type: pen-and-paper/formalisation. Status: blocked.

## Task

Turn Aoyagi's recursive Case 1 / Case 2 blow-up bookkeeping into a formal
transition invariant or certificate, then prove the certificate matches the
coordinate substitutions.

## Output contract

- A finite state representation of the exponent/vector bookkeeping.
- Explicit source correspondence for every transition and terminal case.
- A completeness argument for the case split, with a decorrelated
  counterexample hunt before treating it as established.
- Lean implementation only after the certificate shape is stable.

## Controller notes

This is likely the crux. Build small infrastructure if it reduces proof risk.
Do not mimic prose geometry if a certificate gives a cleaner Lean target.

## 2026-06-18 check result

Draft reproduction: `reproduction-draft.md`. Independent checker:
`Copernicus`, saved at `reproduction-check.md`.

Status: not formalisation-ready. The certificate must first separate actual
layer widths `M^{(S+1)}` from prefix minima `M(S+1)`, repair the Case 1/2
transition updates, cover missing pivot charts, prove regularity/divisibility
for the `P` matrices, and replace the unstable termination measure.

## 2026-06-19 repair checkpoint

Repair report: `reproduction-repair-a4.md`.

Status: still blocked. The width split is now source-faithful: actual reduced
widths are `M^{(s)}`, while `M(S)` is the prefix minimum. Page-image inspection
and xhigh source scout `Russell the 2nd` confirm that Case 2 prints
`t_{S,J+1}^{(i)} = M^{(i+1)}` for `i < S` and
`M'_{S,J+1}=(M(S)-J)(M^{(S+1)}-J)`. The terminal exponent formula on PDF p. 22
uses actual widths `M^{(j)}`. Therefore the printed Case 2 vector gives
`(M^{(S)}-J)(M^{(S+1)}-J)` in the terminal formula, not the printed Case 2
increment, unless `M(S)=M^{(S)}`. Xhigh pen-and-paper scout `Hume the 2nd`
confirmed that replacing the earlier coordinates by prefix minima
`M(2),...,M(S)` repairs the arithmetic while keeping actual-width label
ranges. Do not start a full Lean transition theorem until this is explicitly
split into source-faithful and corrected-certificate statements.

Additional open obligations: all pivot charts, monomial divisibility for
`P`, recurrence-based interpretation of the `b'_i`/standalone-`u` algebra,
termination/off-by-one convention, and rectangular/boundary cases.

## 2026-06-19 Lean arithmetic split

Statement card: `statement-card-a4-terminal-exponent-split.md`.

Landed `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`, imported by
`lean/DLNFibre.lean`. This file proves the terminal-exponent arithmetic for
both the printed Case 2 vector and the prefix-minimum repaired vector:

- `terminalExponent_printedCase2Vector` gives
  `(M^(S)-J)(M^(S+1)-J)`.
- `terminalExponent_prefixCase2Vector` gives
  `(M(S)-J)(M^(S+1)-J)`.

This is deliberately not a blow-up transition theorem. It isolates the source
gap and gives a clean arithmetic target for any corrected certificate.

## 2026-06-19 Lean monomial divisibility

Statement card: `statement-card-a4-monomial-recurrence-divisibility.md`.

Xhigh pen-and-paper scout `McClintock the 2nd` confirmed that regularity of the
quotients `b'_i / b'_(J+1)` in the displayed `P` matrix reduces to a plain
monomial recurrence lemma.  Lean now proves that a recurrence
`b_(k+1)=step_k*b_k` has tail-product divisibility `b_a | b_b` for `a <= b`,
and that common multiplication by a pivot variable preserves this divisibility.
This still does not construct `P` or prove the matrix row-operation identity.
