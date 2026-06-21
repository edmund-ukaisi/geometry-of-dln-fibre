# Statement Card - A5 Lemma 5 Eq5 Terminal-Room Guard

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5PostPLowerGuard_iff_terminalRoom_of_alphaDomain`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_nonfirstBlock_mem_intervalValueSetNat_of_alphaDomain_of_terminalRoom`

## Claim

Under equation `(5)`'s strict alpha domain, the global post-`p`
lower-bound guard is equivalent to the concrete terminal-room inequality

```text
p + 2*a - alpha <= ell.
```

Consequently, a supplied Eq5 piecewise certificate is interval-admissible on
every nonfirst selected block if the strict alpha domain and this terminal-room
inequality are supplied.

## Proved

Lean proves the reverse direction of the iff by evaluating the global guard at
the terminal post-`p` coordinate `b=p+(a-alpha)`.  At that coordinate the
offset is exactly `a`, and the interval excess is bounded above by `ell-b`,
which yields `p+2*a-alpha<=ell`.

The forward direction dispatches to the existing sufficient terminal-room
theorem after extracting `alpha<=p` and `alpha<=a` from strict alpha-domain
membership.

## Assumed

Strict Eq5 alpha-domain membership is required for the iff.  The nonfirst-block
wrapper still assumes a supplied Eq5 piecewise certificate and block
membership.

## Deferred

Source construction of Eq5 branches, proof that terminal-room follows from
Aoyagi source hypotheses, source-label legality, terminal `tilde t=0`, chart
coverage, classifier/injection/back-to-label coverage, Lemma 5 count, pole
order, normal crossings, and RLCT extraction.

## Review

- xhigh source/pen-and-paper scout `Carson` proposed the terminal-room iff and
  checked the endpoint-coordinate calculation.
- Focused Lean check passed for `Lemma5DisplayedVector.lean`.
- Independent xhigh reviewer `Halley` found no fidelity or mathematical
  soundness issues and recommended banking.
