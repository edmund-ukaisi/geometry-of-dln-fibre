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
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.selectedWidth_le_pred_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.lemma5Eq5_labelBounds_of_sourceSelectedInequality`

## Claim

Lean now consumes `AoyagiDefinition3CeilData` in the existing Lemma 4 and
Htilde arithmetic layer.  The selected-sum identity gives terminal endpoint
zero and lower/upper Htilde terminal zeros.  The strict source-selected
inequality, when supplied separately, gives selected-width and label-bound
wrappers.

## Proved

- The Definition 3 datum supplies `1 <= ell` and `1 <= aParam`.
- Definition 3 selected-sum data makes the Lemma 4 terminal endpoint zero.
- The lower and upper Htilde chains vanish at the terminal selected coordinate.
- The penultimate upper Htilde endpoint rewrites as
  `ceilWidth - last selected width`.
- A chain squeezed between the lower and upper Htilde chains has terminal
  value zero.
- With the additional strict source-selected inequality, every selected width
  is at most `ceilWidth-1`.
- With that same additional hypothesis, existing equation `(4)` and `(5)`
  label-bound arithmetic can be invoked through the Definition 3 datum.

## Assumed

- A supplied `AoyagiDefinition3CeilData`.
- For selected-width and label-bound wrappers, the strict selected-width
  inequality `forall i, ell*m_i < sum_j m_j`.
- For equation `(4)` bounds, the local index guards `1 <= p` and
  `p <= aParam`.
- For equation `(5)` bounds, the local index/alpha guards.

## Cited

None in Lean.  This is finite arithmetic packaging.

## Deferred

- The full Definition 3 selection inequalities as a single source package.
- Existence/uniqueness of selected cutpoints and ceiling data.
- Vector admissibility and displayed-vector construction.
- Lemma 4's two-value increment hypothesis.
- Lemma 5 chart-family coverage and terminal-minimum classification.
- Normal crossings, pole order, and RLCT extraction.

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
