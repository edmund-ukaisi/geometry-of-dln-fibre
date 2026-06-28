# Review: A2 retained-passive local formal/product-density COV

Reviewer: xhigh Hypatia the 2nd

Verdict: PASS

Scope:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobianMeasure.lean
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalJacobianMeasure.lean
lean/DLNFibre.lean
```

Review summary:

The checkpoint remains a local retained-passive chart-measure statement.  The
formal and product densities are forward source-side densities on the
retained-passive determinant chart.  The raw-order COV is composed through the
downstream `sourceChart`, and the retained-passive local-source restriction is
still gated by the original realization hypothesis `hrealize`.

No soundness issue was found.  The review confirms that the new theorem does
not claim original source-prior transport, signed-box source-density
identification, normal crossings, pole order, or RLCT extraction.

Reviewer note:

The reviewer did not rerun the build.  Controller gates reported separately:
focused builds, top-level `DLNFibre` build, `scripts/sorries`, `git diff
--check`, and code-only forbidden-marker search.
