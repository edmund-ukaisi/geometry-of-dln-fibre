# Review - A2 Case 2 passive theta Jacobian-dominated source

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Darwin` returned PASS.
- Lean/API reviewer `McClintock` returned PASS.

## Source And Scope Review

`Darwin` checked that the theorem is only local measure-domination
bookkeeping.  The statement assumes an arbitrary theta-domain candidate
measure and only derives the residual-source conclusions after a returned
open neighborhood `W`, under the explicit finite-scalar domination

```text
candidateMeasure.restrict W
  <= c * (passiveSource.withDensity jacobianDensity).restrict W.
```

The proof route is source-faithful: use the concrete theta Jacobian sandwich
to obtain an open neighborhood `U` with an upper Jacobian bound, apply the
existing passive-product residual-source socket to
`candidateMeasure.restrict U`, and finally set `W = U inter V`.

No overclaim was found.  The reproduction and statement card keep the result
scoped to local domination over the globally Jacobian-weighted passive theta
measure, and exclude source-prior construction, determinant-chart Haar
transport, raw-order Haar transport, exact passive-sector pushforward,
source-image equality, source-rank coverage, normal crossings, pole order,
and RLCT extraction.

## Lean/API Review

`McClintock` checked the theorem shape and proof APIs:

- The target theorem statement matches the intended local domination socket.
- The restriction equalities correctly rewrite
  `candidateMeasure.restrict (U inter V)` and the global `withDensity`
  restriction into the upstream local `U`/`V` form.
- The scalar domination step correctly converts domination by the
  Jacobian-weighted measure into finite domination by `passiveSource`.
- No simpler existing API looked strictly preferable.

## Verification

Reviewer direct checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
scripts/sorries DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
git diff --check
```

Controller checks before banking:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All listed reviewer and controller checks passed.  The focused and full builds
replayed only pre-existing warning noise from unrelated modules.
`./scripts/sorries` reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
