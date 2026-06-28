# Review - A2 retained-passive positive-tail post-`Ctop` `F3` shear

Reviewer: `Tesla the 2nd`, xhigh read-only reviewer.

Verdict: PASS.

Scope:

- `retainedPassivePostCtopF3PosCorrectionLinearMapAt`.
- `retainedPassivePostCtopF3PosShearRawTupleLinearEquivAt` and its apply,
  determinant, and absolute-determinant lemmas.
- `retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShearRawTupleLinearEquivAt`
  and its determinant package.
- `retainedPassiveTargetEdgePairThenA1passiveThenCtopThenF3PosShear_fderiv_F3_eq_formalRawOrderJacobianAt`.
- The terminal passive `A1` preservation helper and expedition notes.

Findings:

- No wrong sign was found in the positive-tail correction.
- `Earlyfun z`, `dEarly_postC`, and the terminal passive and solved `A1`
  indices match the existing target-only positive-tail formula.
- The `dEarly_postC` comparison is used only on `rest(T123(Dzv))`, through the
  prior after-`T123` bridge.
- The `Ctop` preservation helper only states that the `Ctop` stage preserves
  the `A1passive` component.
- No misuse of target recovery on post-`Ctop` data was found.
- The determinant claims are scoped to the linear shears and their composition;
  the notes do not overclaim a full raw-tuple equality, actual Frechet
  determinant equality, measure transport, normal crossings, pole order, or
  RLCT.

Checks reported by reviewer:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian: passed
scripts/sorries: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
git diff --check: passed
forbidden-marker search in touched Lean file: no hits
```
