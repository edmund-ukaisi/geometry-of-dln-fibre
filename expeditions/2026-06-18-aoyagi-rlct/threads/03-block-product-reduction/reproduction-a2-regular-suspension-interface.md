# Reproduction - A2 supplied regular-suspension interface

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13, after Theorem 3, separates the product-difference block
ideal into three regular block families and the reduced residual product:

```text
C1 - Er        size r x r,
F2             size r x (H^(L+1)-r),
F3             size (H^(1)-r) x r,
prod C^(s).
```

The elementary count of the three regular families is

```text
c = r^2 + r(H^(L+1)-r) + (H^(1)-r)r
  = -r^2 + r(H^(1)+H^(L+1)).
```

Under the endpoint bounds `r <= H 1` and `r <= H (L+1)`, the already
formalised finite count theorem identifies `c / 2` with Aoyagi's displayed
regular term in Theorem 2.

## Boundary Being Reproduced

Aoyagi p. 13 justifies the block algebra and the regular-variable count.  It
does not, by itself, give an elementary Lean construction of the full analytic
regular-suspension chart from a reduced chart certificate.

The sound interface is therefore a supplied full-certificate boundary.  The
data are:

```text
Cred  : reduced normal-crossing chart certificate,
Cfull : full normal-crossing chart certificate,
c     : regular variable count,
```

together with named supplied obligations saying that `Cfull` is the chart
source, ideal transport, coverage, and Jacobian-compatible regular suspension
of `Cred`.  These obligations are abstract predicates in Lean; they record
what still must be proved by the later analytic chart construction.

The reduced and full chart certificates need not share a parameter space or
coefficient monoid.  The finite equality below only mentions `exponentData`,
which has forgotten those chart-level types.

The finite exponent connection is a single explicit equality:

```text
Cfull.exponentData = Cred.exponentData.jacobianPriorLossShift c.
```

This equality is not a chart construction.  It is the finite exponent
shadow that a genuine regular-suspension construction must have.

## Finite Consequences

From the equality above and the existing finite arithmetic for
`jacobianPriorLossShift`,

```text
Cfull.exponentData.exponentMinimum
  = Cred.exponentData.exponentMinimum + c/2,

Cfull.exponentData.exponentOrder
  = Cred.exponentData.exponentOrder.
```

If `c = aoyagiTheorem2RegularVariableCount L H r`, then the endpoint bounds
convert the minimum shift to Aoyagi's regular term:

```text
Cfull.exponentData.exponentMinimum
  = Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r.
```

Thus, if the reduced finite data satisfy

```text
Cred.exponentData.exponentMinimum + regularTerm
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,

Cred.exponentData.exponentOrder
  = data.theorem2OrderFormula,
```

then the full certificate's finite exponent data satisfy the existing
Theorem 2 finite formula boundary.

## Extraction Placement

The single allowed analytic citation, normal-crossing-to-RLCT extraction,
must be applied to `Cfull`, not to `Cred` followed by adding `c / 2`.

The final socket should therefore require:

```text
Cfull.ExtractionHypothesis lambda poleOrder.
```

Together with the finite formula consequence above and selected-width
provenance, this gives the existing
`AoyagiTheorem2SuppliedChartFinalBoundary Cfull ...`.

The socket returns this `Cfull` boundary exactly.  It should not route through
a boundary for `Cred.jacobianPriorLossShift c`, because that shifted
certificate is finite certificate algebra and can be misread as the analytic
regular-suspension chart.

## Nonclaims

- No construction of `Cfull` from `Cred`.
- No proof that the abstract source, ideal-transport, coverage, or Jacobian
  predicates hold.
- No analytic ideal/germ transport theorem.
- No Aoyagi Lemma 1.
- No regular-coordinate additivity theorem.
- No proof that `Cred` alone has the final RLCT after adding `c / 2`.
- No normal-crossing production, pole-order theorem, or RLCT theorem beyond
  extraction for the supplied full certificate.
