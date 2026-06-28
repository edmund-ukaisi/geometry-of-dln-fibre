# Review: A2 retained-passive target edge-pair raw-tuple determinant

Reviewer: xhigh `Lorentz the 2nd`.

## Verdict

PASS.  No issues found.

The determinant-one surface stays within the intended scope: it proves the
full raw-tuple target edge-pair shear/equivalence, not the formal `(F2,C)`
equivalence and not the analytic raw-order Frechet determinant.  The edge
regrouping includes `Ctop` and `F3` in the raw edge blocks, the same-edge
diagonal shear has determinant one, and the successor contribution uses only
the successor `(F,C)` block via the formal inverse first component.

The generic determinant lemmas are scoped to successor-upper-triangular maps:
the hypotheses explicitly say that the current block depends only on itself
and `p.succ`.  The inverse determinant is transported back by conjugation, then
transferred to the forward equivalence and absolute determinant wrapper.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean
./scripts/sorries
git diff --check
```

The reviewer also checked `#print axioms` for the four public determinant
theorems and three generic determinant lemmas; the footprint was
`[propext, Classical.choice, Quot.sound]`.

## Residual Risk

The reviewer did not run the full `scripts/lb` aggregator build.  The
controller ran that separately as the final integration gate.
