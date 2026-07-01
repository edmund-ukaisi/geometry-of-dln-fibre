# Review - A2 Original Edge-Family Volume Haar Normalization

Date: 2026-07-01.

Reviewer: xhigh `Lagrange the 2nd`.

Verdict: PASS.

## Scope

Reviewed:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPriorHaar.lean
lean/DLNFibre.lean
threads/03-block-product-reduction/reproduction-a2-original-edge-family-volume-haar-normalization.md
threads/03-block-product-reduction/statement-card-a2-original-edge-family-volume-haar-normalization.md
priorities.md
synthesis.md
theorem-ledger.md
```

## Findings

No formalization or mathematical accuracy findings.

The equivalence orientation is correct: `edgeFamilyMatrixTupleLinearEquiv`
maps edge families to tuples and has inverse `tupleToEdgeFamily`; the
`@[simp]` apply lemmas are definitional `rfl`.

The Haar instance is justified by pushing `originalTupleVolume d` along the
inverse continuous linear equivalence, matching the definition

```text
originalEdgeFamilyVolume b
  = Measure.map (tupleToEdgeFamily b) (originalTupleVolume d).
```

The implementation does not install broad topology/Borel instances for
continuous-linear-map product spaces.

The scalar comparison is full-space only and correctly requires
`LocallyCompactSpace` and `SecondCountableTopology`. The positivity and
ENNReal-finiteness lemmas state exactly the finite positive scalar facts needed
for downstream domination.

## Checks

Reviewer checks from `lean/`:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPriorHaar.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPriorHaar
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
```

The reviewer also ran a stdin `#check` pass for the new public declarations.
All checks exited 0. The full build emitted only existing linter warnings
elsewhere.

Controller checks:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPriorHaar.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPriorHaar
env LEAN_NUM_THREADS=3 lake env lean DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_edge_family_prior_haar_axioms.lean
```

The axiom probe reports only:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims Checked

The documentation does not overclaim retained-passive transport, source-image
equality, determinant-chart Haar transport, scalar `1`, normal crossings, pole
order, or RLCT extraction.
