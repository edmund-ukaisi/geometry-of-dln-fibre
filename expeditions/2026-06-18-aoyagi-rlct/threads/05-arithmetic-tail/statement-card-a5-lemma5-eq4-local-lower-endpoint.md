# Statement Card - A5 Lemma 5 Eq4 Local Lower Endpoint

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_piecewise_ownCoordinate_lowerEndpoint_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_eq_interval_erase_upper_of_piecewise`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_insertOwnCoordinate_eq5Offsets_card_eq_offsetCard_add_one_of_piecewise`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_suppliedUpper_Eq4_insertOwnCoordinate_eq_intervalValueSetNat_of_piecewise`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_eq_intervalValueSetNat`

## Claim

In the local overlap `1<=p`, `p+1<=a`, and `p<=ell-a`, a supplied Eq4
piecewise certificate gives the lower same-coordinate endpoint
`T4(C.point p-1)=Htilde_p`.  This lower endpoint fills Eq5's lower endpoint
deficit.  With a separately supplied upper endpoint, the full same-coordinate
interval is filled.

## Inputs

- A supplied Eq4 piecewise certificate, carrying `a<=ell` and `p+1<=a`.
- The local hypotheses `1<=p` and `p<=ell-a`.
- For full interval coverage, an explicit upper endpoint equality; the Eq3
  wrapper supplies this equality from a supplied Eq3-shaped certificate.

## Proves

- Eq4 own coordinate equals the lower Htilde endpoint.
- Inserting the Eq4 own-coordinate value into Eq5 strict offsets gives the
  interval with only the upper endpoint erased.
- The inserted set has cardinality `Eq5Offsets.card + 1`.
- Adding a supplied upper endpoint gives the full same-coordinate interval.

## Does Not Prove

- Source-label legality for the lower endpoint.
- Eq4 existence at the rising boundary `p=a`.
- Terminal-collision compatibility when `p+1=a`.
- All-coordinate coverage, injection, back-to-label coverage, pole order,
  normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, equation `(4)` together with the displayed
Htilde interval arithmetic.  This card records only the local finite-set
consequence of a supplied Eq4 certificate.
