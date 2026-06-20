# Statement card - A5 Lemma 5 equation (4) own coordinate

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperChain_sub_index_eq_lowerChain_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_sub_index_eq_lowerNat_of_le_min`

## Statement

Lean now proves the finite arithmetic behind the own-coordinate sanity check
for Aoyagi Lemma 5, equation `(4)`.

If a coordinate index `p` lies in the rising overlap

```text
p <= a,
p <= ell-a,
```

then the gap between the upper and lower displayed `Htilde` chains at `p` is
exactly `p`, so

```text
Htilde'_p - p = Htilde_p.
```

This is the arithmetic needed for the printed equation `(4)` branch to satisfy
`t^(s)=k-1` at its own source label, under an extra guard not printed in the
source line.

## Proved

- The Fin-indexed chain identity.
- The Nat-indexed source-facing identity.

## Assumed

- `a <= ell`.
- The overlap bounds `p <= a` and `p <= ell-a`.

## Cited

- None in Lean.  This is finite arithmetic from the displayed `Htilde` chain
  gap formula.

## Deferred

- Equation `(3)` and `(4)` full displayed-family realisation.
- Legal source-label bounds.
- `tilde t_{s,k}=0`.
- Source vector-to-chain correspondence and vector admissibility.
- Lemma 5 chart-family coverage/order count, pole order, normal crossings, and
  RLCT extraction.

## Review

- Source/math scout: xhigh `Heisenberg`.
- Lean/API scout: xhigh `Hooke`.
- Landed-patch review passed by xhigh `Hegel`:
  `review-lemma5-eq4-own-coordinate-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
