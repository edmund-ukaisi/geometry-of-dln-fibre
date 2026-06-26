# Statement Card - A2 source-stratum local-subset local-source finite-integral consumer

Date: 2026-06-26.

## Claim

If a supplied measurable local source contains the source-rank stratum inside a
specified open neighborhood of the base point, then the local-source p.13
finite-integral theorem yields the same finite integral on a shrunk open
source-rank-stratum neighborhood.

## Lean Name

```text
exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_sourceStratum_locally_subset_localSource
```

## Inputs Kept Explicit

- `[SFinite mu]` for product-restriction measure comparison;
- open neighborhood `Ulocal` with `x0 in Ulocal`;
- local inclusion `Ulocal ∩ sourceStratum ⊆ Ulocal ∩ localSource`;
- measurability of `localSource`;
- residual positivity and residual negative-power integrability on
  `localSource`;
- local source-filter loss and density bounds.

## Nonclaims

No p.13 local inverse, no source/image equality, no raw-Haar pushforward, no
source-measure or prior transport, no Jacobian/source-density identity, no
normal-crossing production, no pole-order theorem, and no RLCT theorem is
proved.

## Verification

Focused build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

Forbidden-marker scan and whitespace check passed:

```text
scripts/sorries
git diff --check
```
