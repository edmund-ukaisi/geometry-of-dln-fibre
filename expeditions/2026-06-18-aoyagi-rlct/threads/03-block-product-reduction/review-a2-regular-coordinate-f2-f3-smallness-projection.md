# Review - A2 regular-coordinate F2/F3 smallness projection

Date: 2026-06-24.

Reviewer: xhigh scout `McClintock the 4th`.

Status: passed after checking the uncommitted theorem shape and focused Lean
build.

## Checked Statement

The reviewed theorem is

```text
AoyagiRegularBlockCoordinateIndex.f2_f3_squareSum_eventually_le_one_of_forall_centered_continuousAt
```

in `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`.

The statement assumes only finite index types, a topological source type, and a
tagged real coordinate family

```text
coord : alpha -> AoyagiRegularBlockCoordinateIndex iota mu nu -> real
```

whose every tagged scalar coordinate is centered and continuous at `x0`.  The
conclusion is the ambient-neighborhood event

```text
eventually x in nhds x0,
  squareSum(F2_x) + squareSum(F3_x) <= 1.
```

The theorem was checked as a direct projection of the generic two-family
smallness lemma to the two regular-coordinate subfamilies tagged by
`inr (inl -)` and `inr (inr -)`.

## Type-Annotation Check

The nested-sum annotations are important:

```text
F2 tag: inr (alpha := iota x iota) (inl (beta := mu x iota) ij)
F3 tag: inr (alpha := iota x iota) (inr (alpha := iota x nu) ij)
```

The reviewer warned not to weaken these to bare nested `Sum.inr`/`Sum.inl`
terms because type inference is fragile for this regular-coordinate index.

## Verification

The focused module build passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

## Nonclaims

This is only a finite real square-sum neighborhood lemma for the `F2` and `F3`
subfamilies.  It does not prove smallness of the full regular square-sum, does
not mention `Ctop`, residual `D`, product corrections, ideals, charts, or
RLCT, and does not require metric or norm structure beyond real-valued
coordinates.
