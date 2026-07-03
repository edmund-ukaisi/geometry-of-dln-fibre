# A2 two-density domination handoff

Date: 2026-07-03.

## Calculation

Let `mu` be a base coordinate reference measure on a source domain, let `nu`
be a comparison measure, and let `V` be a measurable local set.  Suppose

```text
mu.restrict V <= Cbase • nu.
```

Let `J` and `S` be two nonnegative extended-real density factors.  Assume the
first density is bounded on the base restricted measure,

```text
J(z) <= CJ for mu.restrict V-a.e. z,
```

and the second density is bounded on the once-weighted restricted measure,

```text
S(z) <= CS for (mu.withDensity J).restrict V-a.e. z.
```

The one-density handoff already proved in Lean gives

```text
(mu.withDensity J).restrict V <= (CJ * Cbase) • nu.
```

Apply the same one-density handoff again, now with base measure
`mu.withDensity J`, density `S`, scalar `CS`, and base domination scalar
`CJ * Cbase`.  This gives

```text
((mu.withDensity J).withDensity S).restrict V
  <= (CS * (CJ * Cbase)) • nu.
```

The finite-scalar side condition is purely arithmetic:

```text
Cbase < infinity, CJ < infinity, CS < infinity
  implies CS * (CJ * Cbase) < infinity.
```

## Lean targets

The generic theorem is:

```text
restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le
```

The finite-scalar wrapper is:

```text
restrict_two_withDensity_le_smul_of_restrict_le_smul_of_ae_le_of_lt_top
```

Both are in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

## Boundary

This is measure-theoretic bookkeeping only.  It does not prove the concrete
Aoyagi passive local domination hypothesis, the Jacobian-density upper bound,
the source-density upper bound, or any source-chart/original-prior transport.
It is the conditional adapter that will consume those facts once they are
proved or supplied in the correct local form.
