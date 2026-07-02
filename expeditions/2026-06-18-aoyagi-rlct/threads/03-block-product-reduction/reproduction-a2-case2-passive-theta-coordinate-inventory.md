# Reproduction - A2 Case 2 passive-theta coordinate inventory

Date: 2026-07-02.

Status: coordinate-count boundary for the next A2 source-image gate.

## Source Boundary

Aoyagi Lemma 2 and Theorem 3 give the block substitutions

```text
F2 = -A1^{-1} A2,
F3 = -A3 A1^{-1},
C4 = A4 - A3 A1^{-1} A2,
```

and the p.13 product-difference display

```text
[ C1 - Er              -F2 ]
[ -F3      prod_s C^(s) - F3 F2 ].
```

This supports a finite coordinate inventory for the p.13 active blocks.  It
does not state source-image equality, determinant-Haar transport, a prior
Jacobian, or domination of an ambient formal-product measure by a selected
source image.

## Lean Objects

For the two-edge Case 2 post-pivot chain,

```text
case2PostPivotTwoEdgeDomain n S J τ 0 = τ,
case2PostPivotTwoEdgeDomain n S J τ 1 = Case2ResidualColIndex n S (J+1),
case2PostPivotTwoEdgeDomain n S J τ 2 = Case2ResidualRowIndex n S (J+1).
```

The retained-passive topology tuple has an active field

```text
C : ∀ p : Fin 2, Matrix (κ p.succ) (κ p.castSucc) ℝ.
```

Therefore its two scalar coordinate blocks are:

```text
C(0): Case2ResidualColIndex n S (J+1) × τ,
C(1): Case2ResidualRowIndex n S (J+1) × Case2ResidualColIndex n S (J+1).
```

The current passive-theta source has

```text
Case2PassiveTheta.Center n S J
  = {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J+1)}.
```

Since

```text
case2ResidualBlockPivotEntries n S (J+1)
  = case2ResidualBlockRows n S (J+1)
      × case2ResidualBlockCols n S (J+1),
```

`Center` is equivalent to the scalar coordinate index of `C(1)`, not to the
full `C` tuple.

## Count

Let

```text
c = |Case2ResidualColIndex n S (J+1)|,
h = |Case2ResidualRowIndex n S (J+1)|,
t = |τ|.
```

The full retained-passive `C` field has scalar count

```text
c * t + h * c.
```

The selected-entry center has scalar count

```text
h * c.
```

When `τ` is transported from the next residual-column index, `t = c`, so the
missing head block has count `c^2`.  The bare center can fill the tail factor
but cannot by itself parameterize the ambient active `C` field unless the head
block is empty.

## Lean Slice

The formalised inventory is in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCoordinateInventory
```

and proves:

```text
centerEquivCTailCoordinateIndex
center_card_eq_cTailCoordinateIndex_card
cHeadCoordinateIndex_card
cTailCoordinateIndex_card
cCoordinateIndex_card_eq_cHead_add_cTail
cCoordinateIndex_card_eq_cHead_add_center
```

The last theorem records the safe boundary:

```text
|full active C coordinate index| = |head C block| + |Center|.
```

## Consequence

The next A2 production theorem cannot dominate the ambient p.13
formal-product measure using bare `Case2PassiveTheta` alone.  One of the
following must happen first:

- enlarge the source domain to include the head `C(0)` block as a genuine
  coordinate variable;
- restrict the target measure to the selected section where the head block is
  fixed and use a section-image measure;
- prove a separate change-of-variables theorem whose chart piece is contained
  in the actual image of the selected source.

## Nonclaims

No source-image coverage, determinant-chart Haar transport, raw-Haar
pushforward, original-prior transport, Jacobian density identity, density
bound, normal-crossing theorem, pole order, or RLCT extraction is proved here.
