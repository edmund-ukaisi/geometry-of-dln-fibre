# Reproduction - A2 Case 2 self-endpoint transport

## Shape

The displayed Case 2 two-edge endpoint family is

```text
q = 0: tau,
q = 1: Case2ResidualColIndex n S (J + 1),
q = 2: Case2ResidualRowIndex n S (J + 1).
```

The existing endpoint-transported fixed-base source-family theorem takes an
explicit equivalence

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1).
```

There is a useful definitional specialization where the free right endpoint is
chosen to be the successor residual-column type itself:

```text
tau := Case2ResidualColIndex n S (J + 1).
```

Then the equivalence `eNext` is the identity equivalence.

## Derivation

Start from

```text
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

and instantiate

```text
tau = Case2ResidualColIndex n S (J + 1),
eNext = Equiv.refl _.
```

All other endpoint data stay unchanged.  In particular, the endpoint-family
equivalences

```text
e q :
  case2PostPivotTwoEdgeDomain n S J (Case2ResidualColIndex n S (J+1)) q
    ~= throughSubspaceEndpointComplementIndex ... q
```

are still supplied.

## Boundary

This is not a source calculation from Aoyagi's PDF.  It is only a Lean
specialization of a previously proved finite endpoint-transport theorem.  It
does not prove that Aoyagi's free following-factor endpoint is canonically or
source-faithfully the successor residual-column label set; it merely supports
the self-endpoint use case.

## Proved / Assumed / Deferred

**Proved by this reproduction.** The explicit `eNext` argument can be removed
from the supplied-equivalence fixed-base source-family theorem in the
self-endpoint specialization.

**Assumed.** The endpoint-family equivalences `e`; fixed-base source data
implicit in the theorem's fixed-base construction; all local selected-entry
and retained-passive hypotheses already present in the reused theorem.

**Deferred.** `hTau`; endpoint cardinality proofs for the fixed-base endpoints;
label-preserving endpoint provenance; selected-entry preservation under
noncanonical endpoint choices; source-prior transport; Jacobian comparison;
normal crossings; pole order; RLCT.
