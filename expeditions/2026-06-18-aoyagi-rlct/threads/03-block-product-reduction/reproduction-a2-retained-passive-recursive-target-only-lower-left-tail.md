# Reproduction - A2 retained-passive recursive target-only lower-left tail

Date: 2026-06-27.

Status: controller pen-and-paper reproduction for the next narrow Lean rung.

This note is independent of the quiver-based paper.  It records the elementary
recursion that removes target-side source tangents from the retained-passive
zeroed-final lower-left derivative recurrence.

## Setup

Work in positive-tail shape

```text
z, w : RetainedPassiveRawTopologyTuple (M := M+1) rho kappa' R,
kappa' : Fin ((M+1)+2) -> Type.
```

For `m <= M+1`, let

```text
L_m(y)
```

be the retained-passive lower-left zeroed-final tail beginning at edge `m`.
The boundary is the zeroed-final endpoint:

```text
dL_{M+1} = 0.
```

For a nonterminal `n < M+1`, set

```text
q : Fin (M+1)       := <n, n < M+1>,
p : Fin ((M+1)+1)  := q.castSucc,
r : Fin ((M+1)+1)  := q.succ.
```

The already-landed lower-left one-step core has the order

```text
-((dCnext * C_r + Cnext * dC_r) * A3p * Pcast^-1)
- (Cprod * dG * Pcast^-1)
+ Cprod * A3p * Pcast^-1
    * (dPsucc * solvedA1(p) + Psucc * dAcur)
    * Pcast^-1
+ dNext.
```

No matrix factors commute.

## Target-side replacements

The current solved-`A1` tangent is staged by

```text
retainedPassiveLowerLeftTailCurrentTargetOnlySolvedA1TangentAt hz w n.
```

At `n=0`, this uses the target-recovered `Ctop` tangent and the recursive
target-staged passive `A1` tail derivative.  At `n=s+1`, it uses the passive
target-staged `A1` tangent at `s.castSucc`.

The current stored `C` tangent is staged by

```text
retainedPassiveTargetRecoveredSourceCAt hz w r.
```

The `Cnext` suffix derivative is staged by

```text
retainedPassiveCnextTargetStagedFDerivAt hz w q,
```

where `Cnext` begins at `r.succ`, not at `r`.

The suffix-product tangent `dPsucc` is also target-staged.  The product
`Psucc` begins at the solved-`A1` vertex `p.succ`, whose value is `n+1`.
Thus the implemented target-side derivative uses the full solved-`A1` suffix
API:

```text
dPsucc#(w) =
  retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
    (M := M+1) z w p.succ.val.
```

The auxiliary algebraic fact recorded for this layer is that a positive suffix
of the solved `A1` family is unchanged by solving the omitted first block:

```text
prod_{i >= m, solved A1_i} = prod_{i >= m, A1seed_i}
```

for `m >= 1`.  In this lower-left step, `m = p.succ.val = n+1`, so the
comparison is available when one wants to relate the solved suffix back to the
passive seed suffix.  The target-only derivative bridge itself is stated for
the solved-`A1` suffix, which keeps the terminal solved factor in scope.

## Recursive target-only derivative

Define

```text
D^o_{M+1}(w) = 0,
D^o_n(w) =
  retainedPassiveLowerLeftTailTargetOnlyStepCoreWithCnextAt
    hz w q
    dAcur#(w)
    dPsucc#(w)
    D^o_{n+1}(w).
```

On an actual raw-order derivative target

```text
w = D_z topologyTupleEdgeRawOrder(v),
```

the staged current solved-`A1`, `C`, `Cnext`, `dPsucc`, and successor lower-left
terms become the corresponding source-direction terms.  Therefore the
recursive target-only expression agrees with the already-landed
source-direction staged lower-left recursion, and hence with the Frechet
derivative of `L_m`.

## Lean target

Expected Lean layer:

```text
retainedPassiveSolvedA1_residualFactorProduct_eq_A1seed_of_pos
retainedPassiveSolvedA1TargetStagedTangentAt
retainedPassiveSolvedA1TargetStagedTangentAt_zero
retainedPassiveSolvedA1TargetStagedTangentAt_succ
retainedPassiveSolvedA1TargetStagedTangentAt_fderiv_eq_source
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_self
retainedPassiveSolvedA1SuffixTargetStagedFDerivAt_step
retainedPassiveSolvedA1SuffixProductAt
fderiv_retainedPassive_solvedA1_residualFactorProduct_targetStaged_apply
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_self
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_step
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_zero
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_succ
retainedPassiveLowerLeftProductTailTargetOnlyFDerivAt_fderiv_eq_sourceStaged
fderiv_retainedPassiveLowerLeftProductTailSum_targetOnly_apply
```

The first theorem is pure finite matrix algebra.  The recursion and comparison
theorems belong in the Jacobian layer because they are target-side
normalizer-support API.

## Kill conditions

- Do not shift `dPsucc` away from `p.succ.val`; in the positive-tail step this
  value is `n+1`, the first solved-`A1` vertex in `Psucc`.
- Do not use ambient `M` for the solved-`A1` suffix derivative in `dPsucc`;
  the positive tail is formalized with parameter `M+1`.
- Do not start `Cnext` at `r`; it starts at `r.succ`.
- Do not drop `Cnext * dC_r` at the terminal active step.
- Do not replace successor solved-`A1` by `w.1 q`; the target-only helper uses
  the staged passive tangent at `s.castSucc`.
- Do not claim determinant-one normalization, determinant equality, measure
  transport, normal crossings, pole order, or RLCT from this rung.
