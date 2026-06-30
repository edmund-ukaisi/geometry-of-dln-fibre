# Review - A2 Case 2 passive theta global Jacobian-weighted single open

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Leibniz` returned PASS.
- Lean/API reviewer `Locke` returned PASS.

## Source And Scope Review

`Leibniz` checked that the source-faithful cleanup is exactly the single-open
`W` formulation.  It is safe to call the measure globally weighted only because
all conclusions are localized after restriction to `W`; the statement must not
suggest a global source-prior or global transport result.

The review confirmed that Aoyagi pp. 10-13 support the retained-passive
coordinate/Jacobian-unit bookkeeping and pp. 19-22 support the selected-entry
residual calculation already used by the residual-source handoff.  This slice
adds no new source theorem.

Preserved nonclaims: no determinant-chart Haar transport, raw-order Haar
transport, original/source-prior transport, construction of an original
source-prior density, exact passive-sector pushforward, source-image equality,
source-rank coverage, global usefulness of the Jacobian density outside the
chosen local neighborhood, normal crossings, pole order, or RLCT extraction.

## Lean/API Review

`Locke` checked the uncommitted candidate and confirmed the safest theorem
shape:

```text
exists W, IsOpen W and z0 in W, with
sourceMeasure = passiveSource.withDensity jacobianDensity
mu = Measure.map sourceChart (sourceMeasure.restrict W)
```

The proof uses `W = U ∩ V`, where `U` and `V` come from the previously banked
two-open theorem.  The key equality is:

```text
(passiveSource.withDensity jacobianDensity).restrict (U ∩ V)
  = ((passiveSource.restrict U).withDensity jacobianDensity).restrict V
```

The available API is `restrict_withDensity` and
`Measure.restrict_restrict`, with open-set measurability; no `map`/`restrict`
commutation is needed.

## Verification

Reviewer direct check:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
```

Controller checks:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All listed controller checks passed.  The focused and full builds replayed only
pre-existing warning noise from unrelated modules.  `./scripts/sorries`
reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
