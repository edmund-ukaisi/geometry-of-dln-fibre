# Reproduction - A2 residual-factor product two-edge unfold

Date: 2026-06-25.

Status: Lean target implemented as generic finite product API.

## Source Boundary

Aoyagi's p.13 residual term is an ordered product of residual factors.  In
the displayed Case 2 continuation on pp. 19-22, after the selected pivot is
removed, the local post-pivot product has two factors:

```text
D_{J+1} * C'_+
```

where `D_{J+1}` is the Schur residual block `D - x*y` and `C'_+` is the tail
of the transported following factor `C' = Q^-1 C`.  The p.20 convention
`b'_i = u b_i` remains the scalar guardrail: the selected scalar is already in
the transported weights and is not counted again.

The Lean slice recorded here is the generic two-edge residual-factor product
unfold.  It does not package the Case 2 factors into a dependent `Fin 3`
family, because the currently useful Case 2 API still lacks the residual-index
equivalences and RHS selected-entry matrix identification needed by the
readout theorem.

## Calculation

For a three-object residual-index family

```text
kappa_2, kappa_1, kappa_0
```

and supplied factors

```text
C_1 : Matrix kappa_2 kappa_1
C_0 : Matrix kappa_1 kappa_0,
```

the explicit residual-factor product from endpoint `2` to endpoint `0` is

```text
residualFactorProduct C 2 0 = C_1 * C_0.
```

In Lean, the middle endpoint can be written both as
`Fin.castSucc (1 : Fin 2)` and as `Fin.succ (0 : Fin 2)`.  These have the
same value but are not definitionally the same index expression, so the
theorem casts both factors to the canonical endpoint `(1 : Fin 3)`.

## Lean Target

Implemented in `lean/DLNFibre/DLN/Aoyagi/ProductReduction.lean`:

```text
ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul
```

The proof uses the existing split theorem

```text
ChartLocalSuffixState.residualFactorProduct_trans
```

through the middle endpoint, then unfolds each one-edge product with

```text
ChartLocalSuffixState.residualFactorProduct_castSucc.
```

## Nonclaims

- No concrete Case 2 dependent `Fin 3` factor family.
- No construction of global p.13-compatible `Cfac`.
- No residual-index equivalence construction.
- No equality with a selected-entry coordinate matrix.
- No source/image equality, source-measure transport, density/Jacobian
  theorem, normal crossings, pole order, or RLCT.

## Review

Review:
`review-a2-residual-factor-product-two-edge-unfold.md`.

The xhigh Lean/API scout `Goodall` recommended this generic API and warned
against packaging the Case 2 free-`Cprime` product as a bespoke dependent
`Fin 3` residual-factor product before a concrete readout consumer supplies
the missing equivalence and RHS-identification data.  The xhigh source scout
`Ohm` confirmed that the local two-factor product is source-backed only as
finite product algebra.
