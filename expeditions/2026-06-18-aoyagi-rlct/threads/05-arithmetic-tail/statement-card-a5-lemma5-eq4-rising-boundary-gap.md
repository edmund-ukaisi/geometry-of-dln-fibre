# Statement Card - A5 Lemma 5 Eq4 Rising Boundary Gap

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_no_piecewiseSourceVector_of_not_indexGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_no_piecewiseSourceVector_of_eq_a`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_risingBoundary_eq_a_noEq4LowerEndpoint`

## Claim

At the rising boundary `p=a`, Eq5 still has the rising lower-endpoint deficit
when `1<=a` and `a<=ell-a`, but the repaired Eq4 source-shaped certificate
cannot exist at that coordinate because its guard would require `a+1<=a`.

## Inputs

- For the Eq4 nonexistence theorem: either failure of `p+1<=a`, or the
  coordinate identity `p=a`.
- For the combined Eq5/Eq4 gap: `a<=ell`, `1<=a`, and `a<=ell-a`.

## Proves

The Eq4 guard theorem proves:

```text
not (p+1 <= a) -> not Eq4PiecewiseSourceVector(ell,a,p).
```

The boundary specialization proves:

```text
not Eq4PiecewiseSourceVector(ell,a,a).
```

The combined gap theorem proves:

```text
Eq5Offsets_a = (IntervalValueSet_a.erase Htilde'_a).erase Htilde_a
```

and

```text
not Eq4PiecewiseSourceVector(ell,a,a).
```

## Does Not Prove

- Eq4 source-label legality, introduced-label status, or own-source-label
  status.
- A replacement lower-endpoint source at `p=a`.
- Construction of Eq4 or Eq5 displayed vectors.
- All-coordinate endpoint realisation, injection, back-to-label coverage,
  Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5 equations `(4)` and `(5)`, PDF pp. 26-27, represented in Lean
by the supplied `AoyagiLemma5Eq4PiecewiseSourceVector.indexGuard` field and
the existing Eq5 rising erased-endpoints theorem.
