# Statement Card - A5 Lemma 5 Terminal Minimum Numerator Bridge

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4FreeHighCount`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin`
- `DLNFibre.DLN.Aoyagi.IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator`

## Claim

For a supplied full Lemma 5 branch `x`, the named free high-count parameter
attains Aoyagi Lemma 3's isolated numerator minimum.  If an introduced-label
exponent certificate has numerator supplied to be this Lemma 3 expression, then
the corresponding `terminalExponent` equals the minimum numerator.

## Inputs

- A full supplied admissible Lemma 5 branch family.
- A tagged branch `x in fullBranches`.
- The selected-width sum hypothesis and `a <= n+1`.
- An introduced-label exponent certificate.
- A supplied introduced-label proof for `(s,k)`.
- A supplied numerator normalisation

```text
numerator s k = A(n+1,a,b_x).
```

## Proves

```text
terminalExponent L (widthZ width) (t s k)
  = a*(n+1)*((n+1)-a).
```

## Does Not Prove

- The numerator normalisation from Aoyagi's terminal-exponent formula.
- Terminal `tilde t=0`.
- Source-label legality for the supplied branch family.
- Displayed-vector construction, chart coverage, `lambda`, pole order, normal
  crossings, or RLCT extraction.

## Source

Aoyagi PDF pp. 22-24 for the terminal-exponent quadratic calculation and
Lemma 3; PDF pp. 25-27 for the Lemma 5 branch count.  The bridge is a
supplied-data theorem because the source-backed terminal-exponent
normalisation and terminal-label realisation remain unreproduced.
