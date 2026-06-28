# Review: A2 retained-passive Case 2 canonical chart selected-entry square-sum

Reviewer: `Lorentz the 3rd` (xhigh).  Result: PASS after documentation status
correction.

## Findings

The initial review returned FAIL for one documentation issue only: the new
reproduction and statement card still had stale pending-status language after
the Lean theorem and focused build had landed.

The status text was corrected in:

```text
reproduction-a2-retained-passive-case2-canonical-chart-selected-entry-square-sum.md
statement-card-a2-retained-passive-case2-canonical-chart-selected-entry-square-sum.md
```

## Lean and Mathematical Checks

The reviewer found no Lean/formal issue.

- The theorem is genuinely specialized to `M = 1`: the ambient source uses
  `W : Fin (1 + 2)`, `B : Fin (1 + 1)`, and both upstream bridge calls use
  `M := 1`.
- It only replaces the previous explicit selected-entry residual-factor matrix
  hypothesis with the displayed Case 2 factor identities `hD`, `hF`, and the
  entrywise product readout `hentry`.
- The endpoint equivalences and residual-coordinate equivalence are oriented
  consistently with the upstream two-edge product theorem and the canonical
  square-sum bridge.
- No import-cycle risk was found; the new module is a leaf import in
  `DLNFibre.lean`.

## Nonclaims Checked

The theorem does not imply a longer-suffix selected-entry matrix identity,
outside-factor removal or absorption, residual zero-locus nullity, chart-side
a.e. positivity, finite negative-power integrability, density transport,
normal crossings, pole order, or RLCT extraction.
