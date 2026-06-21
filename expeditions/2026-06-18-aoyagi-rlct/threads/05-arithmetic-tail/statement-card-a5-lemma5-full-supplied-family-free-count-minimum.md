# Statement Card - A5 Lemma 5 Full Supplied Family Free-Count Minimum

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card_and_fullBranch_twoValueCount`
- `DLNFibre.DLN.Aoyagi.AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCount_lemma3A_eq_min`

## Claim

For a full supplied admissible Lemma 5 family, the tagged branch set has
cardinality `a*(ell-a)+1`, and every tagged branch satisfies Lemma 4's
two-value count.  Specializing to total increment length `n+1`, every tagged
branch also attains Aoyagi Lemma 3's isolated numerator minimum in the free
high-count parameter.

## Inputs

- A supplied full admissible branch family.
- A tagged branch `x ∈ fullBranches`.
- The selected-width sum hypothesis.
- `a <= ell`, or in the free-count theorem `a <= n+1`.

## Proves

- A bundled count-and-branchwise-two-value certificate for the supplied family.
- Branchwise equality

```text
A(n+1,a, #{j : Fin n | F_j(fullH x)=M})
  = a*(n+1)*((n+1)-a).
```

Here the free count uses `j.castSucc`, so it excludes the final Lemma 4
increment.

## Does Not Prove

- Construction of the branch family from Aoyagi's printed equations.
- Source-label legality, displayed-vector construction, or terminal
  `tilde t=0`.
- Identification of the isolated numerator with a terminal exponent or
  `lambda`.
- Pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemmas 3-5, PDF pp. 24-27.  This is a supplied-data wrapper around the
already-formalized finite Lemma 4-to-Lemma 3 bridge.
