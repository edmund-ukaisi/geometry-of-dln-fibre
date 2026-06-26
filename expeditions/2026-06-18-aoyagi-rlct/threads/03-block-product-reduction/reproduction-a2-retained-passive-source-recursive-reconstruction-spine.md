# Reproduction - A2 Retained-Passive Source-Recursive Reconstruction Spine

Date: 2026-06-26.

Status: reproduced and formalised the first finite algebraic spine for the
right-inverse direction of the retained-passive source readback.

## Question

The previous rung proved that the source readback map

```text
sourceReadback E
```

is continuous on the recursive determinant domain.  The next target is the
right-inverse statement

```text
edgeMatrix (sourceReadback E) = E
```

under the same recursive determinant hypothesis.  The full statement needs
three finite reconstruction ingredients:

- reconstruct the solved full `A1` family from the source suffix-state
  top-left blocks;
- reconstruct the solved full `A3` family from the source suffix-state
  lower-left blocks;
- reassemble each transformed source edge from its Schur readbacks, then
  cancel the deterministic upper-unitriangular multiplier.

This rung proves the Schur reassembly lemma, determinant propagation, the
`F2` source-readback recurrence, and the complete solved-`A1` reconstruction.
The solved-`A3` endpoint and final per-edge cancellation remain the next
finite targets.

## One-Step Schur Reassembly

For a block matrix `M` with invertible selected top-left corner, the readbacks

```text
A1 = topLeftCorner M
F2 = -(A1^-1 * upperRightBlock M)
A3 = lowerLeftBlock M
C  = schurResidualBlock M
```

reassemble `M` as

```text
[A1, -A1 F2; A3, C - A3 F2].
```

Lean proves this as the generic lemma

```text
fromBlocks_schurReadbacks_eq
```

in `ProductReduction.lean`, near the definitions of `topLeftCorner`,
`upperRightBlock`, `lowerLeftBlock`, and `schurResidualBlock`.  The proof is
the definition of the Schur residual plus `A1 * A1^-1 * upperRight = upperRight`
under the determinant-unit hypothesis.

## Determinant Propagation

Let

```text
S_i(E) = sourceReadbackSuffixState E i
T_p(E) = sourceReadbackTransformedEdge E p.
```

The recursive determinant hypothesis says that every visited `T_p(E)` has
invertible selected top-left corner.  The suffix-state recurrence gives

```text
S_{p.castSucc}.Ctop = S_{p.succ}.Ctop * topLeftCorner T_p.
```

Starting from the terminal state `S_last.Ctop = 1`, backward induction proves
that every `S_i.Ctop` has determinant a unit.  Lean records this as

```text
sourceReadbackSuffixState_Ctop_det_isUnit_of_sourceRecursiveDetChart
```

and packages the immediate domain consequence as

```text
sourceReadback_detChart_of_sourceRecursiveDetChart.
```

This only proves that the explicit readback coordinates satisfy the
retained-passive determinant-chart predicate.  It is not a source-image or
openness theorem.

## Right Block Readback

The source suffix-state step stores the negative right readback:

```text
sourceReadback E . F2full i = - S_i(E).B.
```

For `i = p.castSucc`, this unfolds directly from the step definition.  For
`i = last`, both sides are zero: `F2full last = 0` and the terminal suffix-state
has `B = 0`.  Lean proves

```text
sourceReadback_F2full_eq_neg_sourceReadbackSuffixState_B.
```

This is the finite algebra needed later to cancel the left
upper-unitriangular multiplier in

```text
sourceReadbackTransformedEdge E p =
  [I, S_{p.succ}.B; 0, I] * E p.
```

## Solved Top-Left Reconstruction

The source readback stores passive top-left seeds by reading
`topLeftCorner T_{p.succ}`.  The omitted active first block must be recovered
from the active endpoint `Ctop = S_0.Ctop`.

The finite invariant is stronger than the endpoint needed immediately:
for every nonzero vertex `i`,

```text
residualFactorProduct (sourceReadback E).A1seed last i = S_i(E).Ctop.
```

Lean proves this as

```text
sourceReadback_A1Tail_eq_sourceReadbackSuffixState_Ctop_of_ne_zero.
```

The special case `i = succ 0` gives the passive tail after the first edge:

```text
sourceReadback_A1TailAfterFirst_eq_sourceReadbackSuffixState_Ctop_succ_zero.
```

Then the step recurrence at `p = 0`,

```text
S_0.Ctop = S_1.Ctop * topLeftCorner T_0,
```

and determinant-unit propagation for `S_1.Ctop` give

```text
S_1.Ctop^-1 * S_0.Ctop = topLeftCorner T_0.
```

Nonzero components of the solved `A1` family are passive seed projections.
Together this proves

```text
sourceReadback_solvedA1_eq_topLeftCorner.
```

## Remaining Algebra

The right-inverse theorem is not complete.  The next substantial finite target
is the analogous solved-`A3` statement:

```text
(sourceReadback E).toCoordinateData.solvedA3 p =
  lowerLeftBlock (sourceReadbackTransformedEdge E p).
```

For non-final `p`, this should be definitional from `A3passive`.  The final
case must use the source-left suffix-state lower-left field `F3` and the
retained-passive lower-left tail sum.  After that, per-edge reconstruction
should use:

- `sourceReadback_solvedA1_eq_topLeftCorner`;
- the solved-`A3` analogue;
- `sourceReadback_F2full_eq_neg_sourceReadbackSuffixState_B`;
- `C = schurResidualBlock T_p` by definition of `sourceReadback`;
- `fromBlocks_schurReadbacks_eq`;
- `upperUnitriangular_neg_mul_upperUnitriangular`.

## Nonclaims

This rung proves finite determinant propagation and partial right-inverse
algebra only.  It does not prove the full theorem
`edgeMatrix (sourceReadback E) = E`, image openness, source-rank coverage,
source/image equality, a local homeomorphism, measure pushforward,
density/Jacobian transport, normal crossings, pole order, or RLCT extraction.
