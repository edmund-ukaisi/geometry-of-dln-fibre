# A2 Endpoint-Patch Density Domination Handoff

Date: 2026-07-03.

## Local calculation

Let `mu` be the determinant-side endpoint Haar measure, let `Omega` be the
localized endpoint patch, and let

```text
nu = (mu.restrict Omega).withDensity J.
```

Assume there is a finite scalar `C` such that

```text
1 <= C * J x
```

for `mu.restrict Omega`-almost every `x`.  Then

```text
mu.restrict Omega
  = (mu.restrict Omega).withDensity 1
  <= (mu.restrict Omega).withDensity (fun x => C * J x)
  = C • (mu.restrict Omega).withDensity J
  = C • nu.
```

The first equality is `withDensity_one`.  The inequality is monotonicity of
`withDensity`.  The third equality is scalar extraction from `withDensity`;
the finite-scalar hypothesis gives `C != infinity`, which is the side
condition needed by the nonmeasurable scalar-extraction lemma.

This calculation is purely measure-theoretic.  It does not construct the
endpoint image identity `nu = (mu.restrict Omega).withDensity J`; it only
turns that identity plus the a.e. lower bound into scalar domination.

## Endpoint patch specialization

For the with-following Case 2 endpoint source, take

```text
Omega = rawDetChart inter rawOrderOnEndpoint^{-1}(P)
J = fun y =>
  ENNReal.ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (M := 1) y).
```

If the named endpoint reference image satisfies

```text
endpointReferenceImage =
  (rawHaar.restrict Omega).withDensity J
```

and if `1 <= Cdet * J y` holds `rawHaar.restrict Omega`-a.e. with
`Cdet < infinity`, then the exact consumer-side endpoint domination follows:

```text
rawHaar.restrict Omega <=
  Cdet • Measure.map Y (referenceSource.restrict V).
```

Here `Y` is the with-following endpoint topology-tuple map and
`referenceSource` is the concrete with-following reference source.  The
right-hand measure is definitionally the named endpoint reference image.

## Lean artifacts

Generic measure lemma:

```text
restrict_le_smul_of_eq_withDensity_of_one_le_mul_density
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

Aoyagi endpoint-patch wrapper:

```text
rawHaar_restrict_endpointPatch_le_smul_case2PassiveThetaWithFollowingFactorEndpointReferenceImage_of_eq_withDensity_formalProductAbsDet_of_one_le_mul_density
```

in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaRawOrderReference.lean
```

Focused local builds passed for both edited modules.

Full verification also passed: local `lake build DLNFibre`,
`lean/scripts/sorries`, `git diff --check`, touched Lean-file marker scan, and
direct axiom probe.  The two new declarations report
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This closes only the elementary scalar-domination consequence of an endpoint
image density identity.  The following remain open:

- proving the endpoint reference image identity with determinant-side Haar;
- proving the lower bound `1 <= Cdet * J` on the chosen local endpoint patch;
- applying the theorem to the natural p.13 patch
  `P = rawSourceSet inter rawChart^{-1}(chartPiece)`;
- determinant-Haar/raw-Haar normalization beyond the existing conditional
  raw-order change-of-variables theorem;
- source-image coverage, original-prior transport, normal crossings, pole
  order, and RLCT extraction.
