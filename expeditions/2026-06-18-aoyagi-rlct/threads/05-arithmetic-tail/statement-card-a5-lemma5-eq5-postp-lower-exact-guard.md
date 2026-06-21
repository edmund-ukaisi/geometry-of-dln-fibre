# Statement card - A5 Lemma 5 Eq5 post-p lower exact guard

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5PostPLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5PostPLowerGuard_of_terminalRoom`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_iff_offset_le_intervalExcess`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_offset_le_intervalExcess`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_postP_mem_intervalValueSetNat_of_postPLowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_alphaDomain_and_postPRange_not_lowerGuard`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_not_postPLowerGuard_counterexample`

## Claim

For a supplied equation `(5)` piecewise certificate and a post-`p` branch point
`C.block b S`,

```text
T S in aoyagiHtildeIntervalValueSetNat ell a M m b
```

is equivalent to the local offset guard

```text
alpha + b - p <= aoyagiLemma5IntervalExcess ell a b.
```

## Proved

Lean rewrites the post-`p` value as

```text
Htilde'_b - (alpha+b-p)
```

and uses the existing Htilde interval-membership iff.  The upper interval
bound follows because the offset is a natural number; the lower interval bound
is exactly the offset/excess inequality.

Lean also proves that `alpha<=p`, `alpha<=a`, and
`p+2*a-alpha<=ell` are a sufficient finite-arithmetic condition for the global
post-`p` lower guard.

## Counterexample

Lean proves that the strict Eq5 alpha domain and post-`p` range do not imply
the guard: `ell=6`, `a=4`, `p=2`, `alpha=1`, `b=4` has offset `3` and interval
excess `2`.

## Assumed

For the branch-value iff, the equation `(5)` piecewise certificate and the
post-`p` branch hypotheses are supplied.

For the terminal-room theorem, the terminal-room inequalities are supplied.

## Deferred

Source construction of Eq5 branches, proof of the lower guard from Aoyagi's
source hypotheses, source-label legality, cutoff/selected-span coverage,
terminal `tilde t=0`, classifier/injection/back-to-label coverage, Lemma 5
order count, pole order, normal crossings, and RLCT extraction.

## Review

- xhigh pen-and-paper scout `Bohr` independently derived the iff and the
  concrete counterexample.
- Focused Lean checks passed for `Lemma5DisplayedVector.lean`.
- Independent xhigh reviewer `Darwin` returned `survived` with no findings.
