# Review - A5 Lemma 4 endpoint squeeze

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- `reproduction-lemma4-endpoint-squeeze-a5.md`
- `statement-card-a5-lemma4-endpoint-squeeze.md`

Verdict: source and Lean/API checks pass at the finite endpoint-squeeze scope.

Independent xhigh source checker `Parfit the 5th` verified the endpoint
calculation.  At `j=ell`, Aoyagi's displayed `Htilde` and `Htilde'` endpoint
branches reduce to

```text
sum_j M(S_j) - (a*M + (ell-a)*(M-1)),
```

which vanishes by Definition 3's selected-width sum.  Therefore a supplied
endpoint sandwich implies `H_ell=0`.

Independent xhigh Lean/API scout `Galileo the 5th` checked the theorem shapes
and proof strategy.  The scout recommended keeping `a <= ell` explicit and
avoiding any circular attempt to derive it from the two-value count.

Final independent xhigh landed-patch reviewer `Ramanujan the 5th` found no
blocking, high, medium, or low findings.  The reviewer confirmed that the
source endpoint expression, Lean names/statements, explicit hypotheses, proof
hygiene, and Proved/Assumed/Cited/Deferred documentation are scoped exactly to
the endpoint-squeeze result.  The reviewer also verified the touched Lean module
with `lake env lean`.

Scope check: this is not Aoyagi Lemma 4 itself.  It replaces an explicit
`H_ell=0` hypothesis by supplied endpoint inequalities.  It does not prove the
full `Htilde`/`Htilde'` chains, the vector inequality, the endpoint sandwich
from that vector inequality, the two-value increment hypothesis, vector
admissibility, correspondence to `lambda`, Lemma 5, pole order, normal
crossings, or RLCT extraction.
