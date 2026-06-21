# Statement card - A5 Lemma 5 terminal source endpoint payload

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5TerminalSourceEndpointPayload`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_terminalSource_terminalEndpointPayload`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedBinaryFamily.fullBranch_terminalSource_terminalEndpointPayload`

## Statement

For a supplied full Lemma 5 branch, if the terminal source coordinate

```text
T(C.point ell - 1)
```

is explicitly realised by the branch-chain terminal coordinate

```text
F.fullH x (Fin.last ell),
```

then the branch's terminal chain-zero theorem gives a terminal endpoint
payload:

- terminal Eq5 finite-set coverage at `p=ell`;
- terminal interval membership of the source value;
- the equality `T(C.point ell-1)=1-1`;
- introduced-label membership for `(C.point ell-1,1)`.

## Proved

- The admissible supplied family produces this payload under `a<=ell`, the
  selected-width sum, terminal source range, terminal width positivity, branch
  membership, and explicit source realisation.
- The binary supplied family produces the same payload; its terminal chain zero
  comes from binary `Hlast`/`baseHlast`, while terminal interval membership
  still uses the selected-width sum.

## Assumed

- Supplied full-family branch data.
- The source-realisation equality
  `T(C.point ell-1)=F.fullH x (Fin.last ell)`.
- Terminal source range `C.point ell<=L+1`.
- Terminal width positivity `1<=n(C.point ell)`.

## Cited

- None in Lean.  This is finite endpoint assembly from existing formalised
  Lemma 5 terminal-zero, terminal Eq5, and source-label bookkeeping.

## Deferred

- Terminal branch construction, source-produced source-realisation equality,
  source-backed classifier, injection, back-to-label coverage, pole order,
  normal crossings, and RLCT extraction.

## Review

- xhigh API scout `Euclid` recommended this payload as the safe next terminal
  assembly theorem, with the source-realisation equality kept explicit.
- xhigh hardener `Carver` warned that terminal bridge work must not be named or
  used as terminal branch construction or source-backed exactness.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`
