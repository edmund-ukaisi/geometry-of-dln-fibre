# Statement card - A5 Lemma 5 Eq5 early and tail interval guards

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5PreAlphaLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5AlphaToPLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_iff_index_le_intervalExcess`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_iff_predAlpha_le_intervalExcess`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_preAlpha_mem_intervalValueSetNat_of_preAlphaLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaToP_mem_intervalValueSetNat_of_alphaToPLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_tail_mem_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5PreAlphaLowerGuard_of_alphaDomain`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5AlphaToPLowerGuard_of_alphaDomain`

## Claim

For supplied equation `(5)` branch values:

- `preAlpha` interval membership is equivalent to
  `b <= intervalExcess(ell,a,b)`;
- `alphaToP` interval membership is equivalent to
  `alpha-1 <= intervalExcess(ell,a,b)`;
- `tail` interval membership is automatic because the value is `Htilde_b`;
- strict Eq5 alpha-domain membership supplies the `preAlpha` and `alphaToP`
  lower guards.

## Proved

Lean rewrites each supplied branch value and applies the existing Htilde
interval-membership iff.  It then proves the two early-branch guard predicates
from strict alpha-domain membership by finite `min` arithmetic.

## Assumed

The equation `(5)` piecewise certificate and the corresponding branch
hypotheses are supplied.

## Deferred

Eq5 vector construction, source-label legality, post-`p` guard production,
terminal `tilde t=0`, chart coverage, selected-span exactness,
classifier/injection/back-to-label coverage, Lemma 5 count, pole order,
normal crossings, and RLCT extraction.

## Review

- xhigh pen-and-paper scout `Lagrange` independently derived the exact guards.
- Focused Lean check passed for `Lemma5DisplayedVector.lean`.
- Independent xhigh reviewer `Hypatia` returned `survived` with no findings.
