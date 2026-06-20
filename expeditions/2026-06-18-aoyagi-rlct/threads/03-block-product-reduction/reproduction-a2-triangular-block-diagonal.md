# A2 triangular block-diagonal wrapper reproduction

Source used: Aoyagi 2023 preprint, Section 5, Lemma 2 and Theorem 3
(PDF/printed pp. 10-13).  Independent xhigh scouts: Lean API scout
`Epicurus`, paper-algebra scout `Nietzsche`.

## Paper calculation

Aoyagi's Lemma 2 starts with a block matrix

```text
A = [ A1 A2
      A3 A4 ]
```

where `A1` is a regular `r x r` block.  The lower triangular multiplier

```text
Q1 = [ I 0
       -A3 A1^-1 I ]
```

gives

```text
Q1 A = [ A1 A2
         0  A4 - A3 A1^-1 A2 ].
```

The upper triangular multiplier

```text
Q2 = [ I -A1^-1 A2
       0 I ]
```

kills the upper-right block, so

```text
Q1 A Q2 = [ A1 0
            0  A4 - A3 A1^-1 A2 ].
```

For Theorem 3, the induction hypothesis after the first `S` layers is

```text
Q1' (A^(1) ... A^(S)) Q2' = [ C1' 0
                              0   D_S ],
```

with `Q1' = [I 0; F3' I]`, `Q2' = [I F2'; 0 I]`, and
`D_S = C^(1) ... C^(S)`.  Absorb the old right multiplier into the next layer:

```text
A'^(S+1) = (Q2')^-1 A^(S+1)
         = [ A1' A2'
             A3' A4' ].
```

Then

```text
Q1' (A^(1) ... A^(S)) A^(S+1)
  = [ C1' A1'  C1' A2'
      D_S A3'  D_S A4' ].
```

Assuming the new chart block `A1'` is regular, `C1' A1'` is regular.  The new
lower multiplier

```text
[ I 0
  -D_S A3' (C1' A1')^-1 I ]
```

kills the lower-left block.  The lower-right block becomes

```text
D_S A4' - D_S A3' (C1' A1')^-1 C1' A2'
  = D_S (A4' - A3' (A1')^-1 A2').
```

The new upper multiplier `[I -(A1')^-1 A2'; 0 I]` kills the upper-right block.
Products of lower unitriangular matrices stay lower unitriangular:

```text
[I 0; G I] [I 0; F I] = [I 0; G + F I].
```

Thus the final endpoint product has Aoyagi's triangular shape

```text
[I 0; F3 I] (A^(1) ... A^(L)) [I F2; 0 I]
  = [ C1 0
      0  D ],
```

where the right multiplier in the Lean deterministic state is `F2 = -S.B`.

## Lean correspondence

The existing deterministic certificate already proves

```text
S.L * total * [I -S.B; 0 I] = [S.Ctop 0; 0 S.D].
```

The only new algebra needed is that `S.L` has the lower-unitriangular shape
`[I 0; F3 I]`.  This follows from the definition of `suffixState`: terminal
state has `L = I`, and each `step` left-multiplies by a lower unitriangular
block.

## Nonclaims

This is not chart coverage, exact-rank openness, Aoyagi Lemma 1, analytic
ideal transport, regular-coordinate RLCT additivity, normal crossings, or an
RLCT consequence.  The residual `D` remains the recursively transformed Schur
residual product represented by the deterministic suffix state, not a raw
untransformed lower-right product.
