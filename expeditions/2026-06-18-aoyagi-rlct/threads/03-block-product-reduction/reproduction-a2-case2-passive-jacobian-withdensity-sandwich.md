# Reproduction - A2 Case 2 Passive Jacobian WithDensity Sandwich

Date: 2026-06-29.

Status: controller pen-and-paper reproduction before Lean banking.  This is a
bounded-density comparison on the passive product-domain measure.  It is not a
source-prior transport theorem.

## Question

The previous handoff gives an open neighborhood `U` of `z0` and positive real
constants `epsilon`, `K` such that, for the concrete passive product-domain
measure

```text
sourceMeasure = passiveMeasure.prod weightedBox,
```

the retained-passive raw-order Jacobian factor

```text
J z = retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)
```

satisfies, almost everywhere with respect to `sourceMeasure.restrict U`,

```text
epsilon <= J z
J z <= K.
```

Can this be stated as a two-sided comparison between the restricted measure
and the measure weighted by `ofReal (J z)`?

Answer: yes.  This is the elementary monotonicity of `withDensity`.

## Calculation

For any measure `mu` and real-valued function `f`, suppose

```text
for mu-a.e. x, epsilon <= f x
for mu-a.e. x, f x <= K.
```

Applying monotonicity of `ENNReal.ofReal` gives

```text
for mu-a.e. x, ofReal epsilon <= ofReal (f x)
for mu-a.e. x, ofReal (f x) <= ofReal K.
```

Mathlib's `withDensity_mono` then gives

```text
mu.withDensity (fun _ => ofReal epsilon)
  <= mu.withDensity (fun x => ofReal (f x))

mu.withDensity (fun x => ofReal (f x))
  <= mu.withDensity (fun _ => ofReal K).
```

The constant-density identity rewrites both endpoints:

```text
mu.withDensity (fun _ => ofReal epsilon) = ofReal epsilon • mu
mu.withDensity (fun _ => ofReal K) = ofReal K • mu.
```

Therefore

```text
ofReal epsilon • mu
  <= mu.withDensity (fun x => ofReal (f x))
  <= ofReal K • mu.
```

Specializing `mu` to `sourceMeasure.restrict U` and `f` to the retained-passive
Jacobian factor proves the Case 2 passive theorem.

## Lean Targets

The reusable measure helper is

```text
withDensity_ofReal_sandwich_of_ae_bounds
```

in `LocalMeasureHandoff.lean`.

The Case 2 specialization is

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

in `RetainedPassiveCase2LocalJacobianMeasure.lean`.

## Dependency Boundary

The Case 2 theorem consumes only the previously proved a.e. bounded-unit
handoff for the concrete passive product-domain measure.  It does not use the
residual-coordinate marginal, source-rank support, a local inverse, or a
source-image theorem.

## Nonclaims

- No determinant-chart Haar pushforward.
- No raw/source Haar theorem.
- No original or external DLN source prior.
- No source-prior Jacobian formula.
- No selected-entry source-image equality or coverage.
- No source-rank coverage.
- No positive-mass assertion for the restricted neighborhood.
- No normal crossings, pole order, or RLCT.

