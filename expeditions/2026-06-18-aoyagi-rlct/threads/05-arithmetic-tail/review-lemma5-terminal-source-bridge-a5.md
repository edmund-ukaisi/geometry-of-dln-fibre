# Review - Lemma 5 Terminal Source Bridge

Reviewer: xhigh subagent `Russell`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean`
- `lean/DLNFibre.lean`
- `reproduction-lemma5-terminal-source-bridge-a5.md`
- `statement-card-a5-lemma5-terminal-source-bridge.md`
- expedition ledger updates

## Findings

None.

## Checks

- Both Lean bridge theorems retain the explicit source-coordinate equality
  hypothesis `T(C.point ell - 1)=fullH x (Fin.last ell)`.
- The proofs use that hypothesis to derive `T(C.point ell - 1)=0`, then call
  the existing terminal Eq5 supplied-zero wrapper.
- No theorem infers terminal source-coordinate coverage from `H_ell=0`.
- Import placement is local: the bridge imports only `Lemma5DisplayedVector`
  and `Lemma5SuppliedFamily`, and the aggregator import is appended at the end.
- The reproduction, statement card, and ledgers preserve the boundary and list
  the source-realisation equality as an input, not a conclusion.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5TerminalSourceBridge.lean
lake env lean DLNFibre.lean
```

Both passed.  The controller also ran focused/module/full builds, the sorry
scanner, and `git diff --check`.
