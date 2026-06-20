# A4 Case 2 Principalized Terminal-Last Boundaries

Status: reproduced the terminal-last boundary packages with finite residual
center principalization.

## Source Anchor

Aoyagi's displayed Case 2 chart chooses the residual-block coordinate
`(J+1,J+1)` and writes it as the selected variable `u`.  In that selected
chart, every finite residual-block center coordinate is either `u` itself or
has an explicit factor of `u`.

The terminal-last branch is the endpoint condition

```text
S+1=L.
```

In that case the source suffix

```text
prod_{s=S+2}^L C^(s)
```

is the empty product, with endpoint transport in Lean.

## Pen-And-Paper Reproduction

The finite-center part is independent of the stopped terminal presentation:

```text
u is a transformed center value,
u divides every transformed center value,
ideal(transformed finite center values) = (u).
```

The actual-width terminal-last branch already gives

```text
ideal(M(q)) = ideal(T_original),
```

where `T_original` is the terminal weight times original source rows
`1..J+1`.  This branch uses both

```text
n(S+1)=J+1,
S+1=L.
```

It also carries the relabelled `(S+1,0)` level and exponent-domain
certificates.

The row-exhausted terminal-last branch already gives

```text
ideal(M(q)) = ideal(T_transport),
```

where `T_transport` is the terminal-prefix weight times transported prefix
rows.  This branch uses

```text
prefixMinNat n S=J+1,
S+1=L.
```

It does not identify the transported row `J+1` with the original source row
and does not carry `(S+1,0)` relabelled certificates.

The new package simply conjoins the relevant terminal-last boundary with the
three finite-center facts.

## Boundaries

- These theorems principalize only the finite residual-block center ideal.
- They do not principalize the terminal product ideal.
- The source following data `C` and edge matrices `Ctail` remain supplied.
- The actual-width package uses original rows and relabelled certificates.
- The row-exhausted package uses transported prefix rows and no relabelled
  `(S+1,0)` certificates.
- They do not prove chart coverage, source production of `C'^(S+1)`,
  chart-produced following products, Jacobian arithmetic, normal
  crossings/RLCT extraction, termination, transition invariance, or repair of
  the printed Case 2 vector mismatch.
