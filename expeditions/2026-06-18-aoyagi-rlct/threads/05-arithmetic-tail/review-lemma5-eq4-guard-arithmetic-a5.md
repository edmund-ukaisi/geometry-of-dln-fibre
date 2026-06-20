# Review - A5 Lemma 5 equation (4) guard arithmetic

Reviewer: xhigh `Galileo`.

Scope:

- `aoyagiLemma5IntervalExcess_eq_self_of_le_min`;
- `aoyagiLemma5Eq4_selectedIndexGuard_iff`;
- `aoyagiHtildeLowerNat_add_one_labelBounds_iff_prefixCrossing`;
- reproduction, statement card, and ledger updates.

## Findings

None.

## Verdict

Pass as-is.

The interval-excess lemma correctly specializes
`min(p, ell-p, a, ell-a)` to `p` under `p<=a` and `p<=ell-a`.  The selected
index guard correctly proves
`p+(ell-a)+2<=ell+1 <-> p+1<=a`.  The label-bounds theorem correctly unfolds
the lower chain under `p<=a` and rewrites
`1<=Htilde_p+1<=W_(p+1)` as the zero-based inclusive-prefix form of
`P_p < pM <= P_(p+1)`.

No source overclaim was found.  The patch keeps full equations `(3)`/`(4)`
realisation, terminal `tilde t=0`, and legal-label bounds from Definition 3
alone blocked.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5IntervalArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake build DLNFibre.DLN.Aoyagi.HtildeChainArithmetic`
- `./scripts/sorries`
- `git diff --check`
