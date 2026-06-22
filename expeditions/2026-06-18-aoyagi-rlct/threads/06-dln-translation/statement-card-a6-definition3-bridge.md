# Statement Card - A6 Definition 3 Bridge

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`

Aggregator:

- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.one_le_ell`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.one_le_aParam`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.terminalEndpoint_eq_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerChain_last_eq_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeUpperChain_last_eq_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerNat_last_eq_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeUpperNat_last_eq_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeUpperNat_pred_eq_sub_lastWidth`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.Hlast_eq_zero_of_htildeChainBounds`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.intervalSize_excess_sum_Icc_eq_theorem2OrderFormula`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeIntervalValueSetNat_excess_sum_Icc_eq_theorem2OrderFormula`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeIntervalValueSetNat_terminal_eq_singleton_zero`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.suppliedTerminalZero_Eq5_offsets_eq_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma4_twoValueCount_of_htildeChainBounds`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.selectedWidth_le_pred_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq4_localData_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq5_labelBounds_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq3_localData_of_sourceSelectedInequality_and_slack`

## Claim

Lean now consumes `AoyagiDefinition3CeilData` in the existing Lemma 4 and
Htilde arithmetic layer.  The selected-sum identity gives terminal endpoint
zero, lower/upper Htilde terminal zeros, terminal same-coordinate singleton
bookkeeping, and finite count rewrites to the Theorem 2 displayed order
formula.  The strict source-selected inequality, when supplied separately,
gives selected-width and local equation `(4)`/`(5)` wrappers.  Equation `(3)`
still requires an explicit one-unit slack hypothesis.

## Proved

- The Definition 3 datum supplies `1 <= ell` and `1 <= aParam`.
- Definition 3 selected-sum data makes the Lemma 4 terminal endpoint zero.
- The lower and upper Htilde chains vanish at the terminal selected coordinate.
- The penultimate upper Htilde endpoint rewrites as
  `ceilWidth - last selected width`.
- A chain squeezed between the lower and upper Htilde chains has terminal
  value zero.
- The finite interval-size excess sum and same-coordinate Htilde interval
  value-set excess sum both rewrite to `data.theorem2OrderFormula`.
- The terminal same-coordinate Htilde interval value set is `{0}`.
- A separately supplied terminal zero fills the terminal Eq5 offset set into
  the terminal same-coordinate value set.
- Under supplied Htilde chain bounds and a supplied two-value increment
  hypothesis, Lemma 4's two-value count theorem can be invoked through
  Definition 3 data.
- With the additional strict source-selected inequality, every selected width
  is at most `ceilWidth-1`.
- With that same additional hypothesis and local guards, existing equation
  `(4)` and `(5)` finite arithmetic can be invoked through the Definition 3
  datum.
- Equation `(3)` local finite arithmetic can be invoked only with the strict
  source-selected inequality, `aParam < ell`, and an explicit one-unit slack
  hypothesis.

## Assumed

- A supplied `AoyagiDefinition3CeilData`.
- For selected-width and label-bound wrappers, the strict selected-width
  inequality `forall i, ell*m_i < sum_j m_j`.
- For Lemma 4's count wrapper, supplied Htilde chain bounds, the initial value
  `H 0 = m 0`, and the two-value increment hypothesis.
- For the terminal Eq5 offset wrapper, a supplied terminal zero
  `T(C.point ell - 1)=0`.
- For equation `(4)` local data, the local index guards `1 <= p`,
  `p+1 <= aParam`, and `p <= ell-aParam`.
- For equation `(5)` bounds, the local index/alpha guards.
- For equation `(3)` local data, `aParam < ell` and the explicit slack
  `aoyagiSelectedWidthNat ell m 0 + 2 <= ceilWidth`.

## Cited

None in Lean.  This is finite arithmetic packaging.

## Deferred

- The full Definition 3 selection inequalities as a single source package.
- Existence/uniqueness of selected cutpoints and ceiling data.
- Vector admissibility and displayed-vector construction.
- Lemma 4's two-value increment hypothesis.
- Lemma 5 chart-family coverage and terminal-minimum classification.
- Interpreting the finite Theorem 2 order formula as pole order.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-definition3-lemma4-bridge-a6.md`.
- Review artifact:
  `review-definition3-bridge-a6.md`.

## Verification

Run from `lean/`:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
lake build DLNFibre
scripts/sorries
```
