# Review - A2 Case 2 passive theta endpoint-sector domination

Date: 2026-06-30.

## Verdict

PASS, scoped as a conditional domination transfer.

Two xhigh read-only reviews informed this slice:

- Source/scope reviewer `Lorentz` recommended a local bounded-density sector
  comparison, with finite-scalar domination as the immediate consumer-facing
  corollary, and warned against claiming global exact pushforward.
- Lean/API reviewer `Carver` recommended the finite-scalar endpoint-sector
  pushforward theorem as the smallest non-overclaiming next Lean target, and
  identified the bounded-density corollary as the immediate follow-up.

## Source And Scope Review

`Lorentz` confirmed that mere support is already landed and is not a measure
comparison.  The source-faithful frontier remains a local bounded-density
sector comparison, because exact global pushforward would require additional
normalization, image-measurability, and local-inverse/injectivity work.

This slice does not claim that comparison.  It proves the conditional
transport step needed once theta-domain domination or a bounded theta-domain
density is available.

## Lean/API Review

`Carver` checked the target theorem shape against existing APIs:

- use the already landed endpoint-sector support theorem to rewrite both
  restricted endpoint pushforwards;
- apply `map_le_smul_map_of_le_smul` to transport theta-domain domination
  through `case2PassiveThetaEndpointTopologyTuple`;
- derive the bounded-density corollary by `restrict_withDensity`,
  `withDensity_const`, and `withDensity_mono`.

The review also noted that exact Haar/passive-sector equality should wait for
image measurability without explicit hypotheses, a measurable inverse or local
embedding for the theta map, and identification of the theta reference measure
with retained-passive determinant-chart Haar.

## Verification

Controller checks before banking:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All listed checks passed when run from the local `lean/` directory, except
`git diff --check`, which was run from the repository root.  The full build
replayed only pre-existing warning noise from unrelated modules.
`./scripts/sorries` reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probes for both public theorems report:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This slice does not prove exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction.
