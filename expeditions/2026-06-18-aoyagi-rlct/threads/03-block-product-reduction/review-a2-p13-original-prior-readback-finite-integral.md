# Review - A2 p.13 Original-prior Readback Finite Integral

Date: 2026-07-01.

Reviewer: Copernicus the 2nd, xhigh read-only scout; controller proof check.

Status: PASS for theorem shape and import placement.  Full verification is
recorded in the expedition ledgers after the build gates.

## Scope

Audit the next-step theorem routing the p.13 original-prior readback bridge
into the existing passive-theta finite-integral socket:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean
```

## Findings

The theorem is the right downstream consumer.  It imports both source modules
in a fresh file, so there is low import-cycle risk and neither source bridge is
made to depend on this wrapper.

The assumptions that would require new geometry are explicit: chart-piece
measurability, containment in both `sourceLocal` and the named p.13 source set,
readback/right-inverse on the piece, local original-density boundedness, and
the formal-product p.13 readback measurability/domination with finite scalar.

The scalar is oriented correctly.  The existing p.13 bridge yields the
readback domination for the original prior with

```text
Cpull := (ENNReal.ofReal Kprior * ((cHaar^-1 : NNReal) : ENNReal)) * Cformal,
```

and the finite helper supplies `Cpull < infinity` from `Cformal < infinity`.

## Nonclaims Checked

No formal p.13 measure domination by the passive coordinate source measure,
no identification with a passive-theta source-image measure, no source
coverage, no chart-image equality, no source-rank coverage, no Haar scalar
normalization, no normal crossings, no pole order, no RLCT extraction, and no
global original-prior integrability is proved here.
