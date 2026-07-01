# Review - A2 Case 2 formal-product source-reference identity from raw pushforward

Date: 2026-07-01.

Status: xhigh review pass with wording guardrails.

## Reviewed Claim

The theorem pair

```text
exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_sourceReference_restrict_of_case2PassiveTheta_rawMap_eq_restrict_rawSource

exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_withDensity_one_sourceReference_of_case2PassiveTheta_rawMap_eq_restrict_rawSource
```

is a conditional source-reference identity.  Assuming the explicit raw
pushforward

```text
Measure.map rawMap (thetaReference.restrict V) =
  rawHaar.restrict rawSourceSet,
```

it identifies the p.13 formal-product measure, restricted to any measurable
`chartPiece subset p13SourceSet`, with the chart-produced source reference
`Measure.map sourceChart (thetaReference.restrict V)` restricted to the same
piece.  The `withDensity (fun _ => 1)` conclusion is only the identity density
relative to that chart-produced source reference.

## Verdict

PASS, conditional on preserving the explicit raw-pushforward hypothesis and the
nonclaim boundary below.

## Checks

- Source-boundary check: this is p.13 formal-product/source-reference
  bookkeeping from the local raw-order chart and an assumed raw pushforward.  It
  is not a new Aoyagi source theorem and not a proof of the raw pushforward.
- Lean-shape check: the direct proof uses the Case 2 two-stage
  `rawMap`/`rawChart` measure identity and the p.13 formal-product raw-order
  theorem.  The proof no longer needs the original-volume scalar bridge.
- Naming check: `sourceReference` is the correct word.  `sourceImage` would
  overstate the theorem, because the statement does not prove image coverage or
  characterize arbitrary source-image pieces.
- Lean verification: focused elaboration, focused module build, full local
  `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and direct
  axiom probe passed.  The theorem's axiom footprint is `[propext,
  Classical.choice, Quot.sound]`.
- API hardening check: the direct restricted equality is now exposed as its own
  theorem, and the bounded-density socket theorem is a wrapper over it.

## Nonclaims

The theorem does not prove determinant-chart Haar transport, full raw Haar
transport, source-image coverage, source-rank coverage, original source-prior
transport, Haar scalar normalization, normal crossings, pole order, or RLCT
extraction.
