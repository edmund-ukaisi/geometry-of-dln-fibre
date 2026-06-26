# Reproduction - A2 Retained-Passive p.13 Source-Chart Boundary

Date: 2026-06-26.

Status: pen-and-paper boundary after xhigh reconstruction by Franklin the
3rd and read-only Lean/API audit by Socrates the 3rd.  No new Lean theorem is
claimed here.

## Source Window

Aoyagi pp. 10-13 provide:

- Lemma 2: one-step Schur block elimination under a regular top-left block.
- Theorem 3: induction of that block elimination through a product.
- p. 13: the displayed transformed product-difference block and the regular
  variable shift formula.

These pages support the finite block algebra below.  They do not by
themselves supply a source-rank coverage theorem, exact-rank openness, a
measure pushforward, a Jacobian-density theorem, or RLCT extraction.

## Coordinate Domain

Let the retained rank block have size `r`, and let the source chart have
`N = M + 2` edges indexed by `p = 0, ..., last`, where `last = N - 1`.
Each transformed edge is written in the retained-passive form

```text
M_p =
  [ A1_p   -A1_p F2_p
    A3_p    C_p - A3_p F2_p ].
```

The p.13 active coordinates are:

```text
X = Ctop_0 - I_r
F2 = F2_0
F3 = F3_0
C_p, for p = 0, ..., last
```

The retained passive variables are:

```text
A1_p, for p = 1, ..., last
F2_p, for p = 1, ..., last
A3_p, for p = 0, ..., last - 1
```

The solved endpoint variables are:

```text
A1_0
A3_last
```

The determinant chart requires:

```text
det(Ctop_0) is a unit
det(A1_p) is a unit for p = 1, ..., last.
```

The p.13 basepoint is:

```text
Ctop_0 = I_r, so X = 0
F2_p = 0 for every p
F3 = 0
A1_p = I_r for p > 0
A3_p = 0 for p < last
C_p = 0 for every p.
```

The passive variables `F2_p` for `p > 0` must be retained.  If they are fixed
to zero, the construction is again a section and cannot support a full
source-chart or raw measure statement.

## Recursive Source Map

Set terminal data:

```text
Ctop_N = I_r
D_N = I
F2_N = 0
F3_N = 0.
```

The solved top-left endpoint is determined by the passive tail:

```text
Tail = A1_last A1_(last-1) ... A1_1
A1_0 = Tail^-1 Ctop_0.
```

For the suffix recursion:

```text
Ctop_p = A1_last A1_(last-1) ... A1_p
D_p = D_(p+1) C_p
B_p = -F2_p.
```

The solved final lower-left endpoint is determined from the requested p.13
`F3` coordinate:

```text
F3 = - sum_{p=0}^{last} D_(p+1) A3_p Ctop_p^-1,
```

so

```text
A3_last =
  -(F3 + sum_{p=0}^{last-1} D_(p+1) A3_p Ctop_p^-1) Ctop_last.
```

For `N = 1`, this reduces to `A3_0 = -F3 Ctop_0`.

The original fixed-base edge is reconstructed by

```text
E_p =
  [ I  F2_(p+1)
    0  I        ] M_p,
```

with `F2_N = 0`, so the same formula covers the final edge.

## One-Step Check

The one-step Aoyagi variables satisfy:

```text
Ctop = C1 A1
F2   = -A1^-1 A2
F3   = F3old - D A3 (C1 A1)^-1
C    = A4 - A3 A1^-1 A2.
```

The inverse equations are:

```text
C1    = Ctop A1^-1
A2    = -A1 F2
F3old = F3 + D A3 Ctop^-1
A4    = C - A3 F2.
```

Substituting the inverse into the forward equations recovers
`Ctop`, `F2`, `F3`, and `C`.  Substituting the forward equations into the
inverse recovers `C1`, `A2`, `F3old`, and `A4`.  The algebra only uses the
determinant-unit hypotheses on `A1` and the accumulated `Ctop` products.

## p.13 Loss Readout

After Theorem 3, Aoyagi p.13 reads the transformed product-difference block as

```text
[ Ctop - I      -F2
  -F3        D - F3 F2 ],
```

where `D` is the product of the residual `C_p` blocks.

In the retained-passive chart this readout depends only on:

```text
Ctop_0 - I
F2_0
F3_0
product_p C_p.
```

The passive `A1_p`, passive `F2_p`, and passive `A3_p` enter the source map
and the solved endpoints, but not this displayed active block.  Near the
basepoint their inverse factors are units supplied by the determinant chart.
The formula for `A3_last` is chosen precisely so the readback endpoint is the
specified `F3`.

This supports the finite active-coordinate readout.  It does not make passive
variables additional singular variables, and it does not prove analytic
normal crossings.

## Coverage Boundary

The first meaningful missing theorem has the shape:

```text
exists_retainedPassiveP13LocalSource_coverage :
  exists Ulocal localSource, IsOpen Ulocal /\ x0 in Ulocal /\
    Ulocal inter paperEndpointFixedBaseSourceRankStratum ... subset
      Ulocal inter localSource
```

where `localSource` must be tied to the retained-passive chart, for example
as the preimage of

```text
RetainedPassiveNonredundantCoordinateData.sourceRecursiveDetChartSet
```

under the fixed-base edge-matrix map from the original source parameters.

A theorem that sets `localSource = Ulocal inter sourceStratum` without chart
fields is not progress.  The local source must expose enough structure to
connect to the retained-passive `edgeMatrix` / `sourceReadback` chart already
formalised.

Existing fixed-base neighborhood infrastructure suggests that the recursive
determinant-chart part should be approachable near the base edge family, but
the exact source-to-retained-passive bridge and source-rank inclusion still
must be named and proved explicitly.

## Jacobian Boundary

For one step, order raw variables as:

```text
(C1, D, F3old, A1, A2, A3, A4)
```

and chart variables as:

```text
(Ctop, D, F3, A1, F2, A3, C).
```

The formal diagonal factors are:

```text
C1 -> Ctop = C1 A1:        det(A1)^r
A2 -> F2 = -A1^-1 A2:      det(A1)^(-m)
F3old -> F3:               1
A4 -> C:                   1
D, A1, A3:                 1.
```

Here `m` is the lower target width of the `F2` block.  Thus the one-step
raw-to-chart factor is formally

```text
unit_sign * det(A1)^(r - m),
```

and the chart-to-raw factor is its inverse.  Across steps the formal product
is

```text
prod_p det(A1_p)^(r - m_(p+1))
```

up to endpoint unit factors involving passive tails and `Ctop`.

This is only a symbolic Jacobian calculation.  A Lean theorem replacing
`hraw_map` still needs a genuine local diffeomorphism/measure theorem,
source-measure identification, pushforward density calculation, and bounded
transported-prior statement.

## Verdict

The honest next Lean payoff is coverage, not raw-density and not a consumer
theorem.  A raw-density theorem requires the analytic measure/Jacobian work
above, and a consumer theorem would only be meaningful after coverage and
density are separately established.

## Nonclaims

No raw-Haar pushforward, source-rank finite cover, exact-rank openness,
original-loss comparison, measure/Jacobian transport, normal-crossing
construction, pole-order theorem, or RLCT extraction is proved here.
