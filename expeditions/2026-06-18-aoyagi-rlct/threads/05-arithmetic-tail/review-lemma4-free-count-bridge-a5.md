# Review - A5 Lemma 4 free-count bridge

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- `reproduction-lemma4-free-count-bridge-a5.md`
- `statement-card-a5-lemma4-free-count-bridge.md`

Verdict: independent pass at the finite bridge scope.

Independent xhigh source checker `Arendt the 5th` verified the finite
derivation.  If `a` of all `ell` increments are high and `b` is the high-count
among the first `ell-1` increments, then

```text
b + 1_{F_ell=M} = a.
```

Hence over integers `b=a` or `b=a-1`, matching the endpoint-corrected equality
cases already proved for Aoyagi's Lemma 3 numerator.

Independent xhigh reviewer `Tesla the 5th` audited the landed Lean and found
no blocking issue.  Tesla confirmed that the count split on `Fin (n+1)` uses
`j.castSucc` for the initial `Fin n` positions and `Fin.last n` for the
terminal increment, and that
`aoyagiLemma4_terminalH_freeHighCount_lemma3A_eq_min` has the intended scope:
terminal-`H` bookkeeping, the selected-width sum, and two-value increments
imply only that the free high-count attains the isolated Lemma 3 numerator
value.

Scope check: this is not Lemma 4 itself and not the A5 minimisation theorem.
It proves only the finite count split and the isolated Lemma 3 numerator value
at the resulting free high-count.  It does not prove the two-value increment
hypothesis, vector admissibility, the terminal exponent rewrite, correspondence
to `lambda`, Lemma 5, pole order, normal crossings, or RLCT extraction.
