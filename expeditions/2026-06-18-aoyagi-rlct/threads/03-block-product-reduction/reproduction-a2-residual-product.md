# A2 residual-product wrapper reproduction

Source used: Aoyagi 2023 preprint, Section 5, Lemma 2 and Theorem 3
(PDF/printed pp. 10-13). Independent xhigh reviewers: endpoint-wrapper scout
`Copernicus`; Lean/math reviewer `Pascal`.

## Paper calculation

Aoyagi's Lemma 2 diagonalises one charted block matrix

```text
A = [ A1 A2
      A3 A4 ],
```

where `A1` is regular. The lower and upper triangular changes kill the
off-diagonal blocks and replace the lower-right block by the Schur residual

```text
C4 = A4 - A3 A1^{-1} A2.
```

In Theorem 3, suppose the first `S` layers have already been diagonalised:

```text
Q1' (A^(1) ... A^(S)) Q2'
  = [ C1'       0
      0    C^(1) ... C^(S) ].
```

Aoyagi then absorbs the old right multiplier into the next layer:

```text
A'^(S+1) = (Q2')^{-1} A^(S+1)
         = [ A1' A2'
             A3' A4' ].
```

Multiplying before the next elimination gives

```text
Q1' (A^(1) ... A^(S)) A^(S+1)
  = [ C1' A1'                  C1' A2'
      (C^(1) ... C^(S)) A3'    (C^(1) ... C^(S)) A4' ].
```

After the same Lemma 2 elimination at the top-left block `C1' A1'`, the new
lower-right block is

```text
(C^(1) ... C^(S)) A4'
  - (C^(1) ... C^(S)) A3' (C1' A1')^{-1} C1' A2'
= (C^(1) ... C^(S)) (A4' - A3' (A1')^{-1} A2').
```

Thus the induction updates the lower-right endpoint block by right-multiplying
the previous residual product by the Schur residual of the transformed next
edge. This is exactly the recursion

```text
D_i = D_{i+1} * residualBlock_i,
D_j = I,
```

when the chain is traversed down from endpoint `j` to `i`.

## Lean correspondence

The deterministic suffix state already had the field recurrence

```text
(suffixState E j p.castSucc _).D
  = (suffixState E j p.succ _).D * residualBlock E j p _.
```

The new definition

```text
ChartLocalSuffixState.residualProduct E j i hij
```

is the same decreasing recursion with base identity at `j`. The theorem

```text
ChartLocalSuffixState.suffixState_D_eq_residualProduct
```

proves by decreasing induction that the deterministic state's `D` field is
this product. The endpoint certificate wrapper then rewrites the existing
block diagonal form

```text
[I 0; F3 I] * total * [I F2; 0 I] = [Ctop 0; 0 S.D]
```

as

```text
[I 0; F3 I] * total * [I F2; 0 I]
  = [Ctop 0; 0 residualProduct EMat (Fin.last N) 0 _].
```

## Nonclaims and scope

The product is a product of transformed Schur residual blocks visited by the
deterministic suffix recursion. It is not a raw product of the original edge
lower-right blocks.

The abstract suffix-chain wrapper still uses the existing stronger chart
hypothesis `forall p Bprev, identityCornerDetChart ...`, even though this
particular proof only uses the recursively visited `Bprev` values. This is an
explicitly stronger assumption, not a false statement.

This slice does not prove chart coverage from source rank hypotheses,
exact-rank openness, Aoyagi Lemma 1, analytic ideal transport, regular
coordinate RLCT additivity, normal crossings, pole order, or any RLCT
consequence.
