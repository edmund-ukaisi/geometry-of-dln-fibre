# Statement card - A2 chart-local suffix-state field continuity

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-a2-chart-local-suffix-state-field-continuity.md`.

## Target

Extend the existing `ChartTopology.lean` suffix-state continuity API from the
`B` field to the deterministic fields `L`, `Ctop`, and `D`, carrying the
basepoint determinant-unit invariant for `Ctop`.

## Expected Lean Artifacts

Expected declarations in `lean/DLNFibre/DLN/Aoyagi/ChartTopology.lean`:

```text
continuousAt_chartLocalSuffixState_step_fields
continuousAt_chartLocalSuffixState_suffixState_fields
```

The suffix theorem should have the same hypotheses as the existing
`continuousAt_chartLocalSuffixState_suffixState_B`:

```text
E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) K
hE : ContinuousAt E x0
hchart : recursive determinant-chart hypotheses at x0
```

and should return, for every `i <= j`,

```text
IsUnit ((suffixState (E x0) j i hij).Ctop.det) ∧
ContinuousAt (fun x => (suffixState (E x) j i hij).L) x0 ∧
ContinuousAt (fun x => (suffixState (E x) j i hij).B) x0 ∧
ContinuousAt (fun x => (suffixState (E x) j i hij).Ctop) x0 ∧
ContinuousAt (fun x => (suffixState (E x) j i hij).D) x0
```

## Expected Proof

Prove a one-step bundled theorem first.  The step theorem should reuse the
existing `continuousAt_chartLocalSuffixState_step_B` for the `B` component and
prove the other components by continuity of matrix multiplication, submatrix
projections, block assembly, negation/subtraction, and inversion at
determinant-unit matrices.

The suffix theorem should be a descending induction parallel to the existing
`continuousAt_chartLocalSuffixState_suffixState_B`.

## Kill Conditions

- Do not assert exact-rank strata are open.
- Do not call continuity analytic regularity.
- Do not add wrappers around endpoint rank/source-rank packages.
- Stop if the theorem loses the determinant-chart hypotheses or the carried
  `Ctop.det` unit invariant needed for `L`.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 lake env lean DLNFibre/DLN/Aoyagi/ChartTopology.lean
cd lean && LEAN_NUM_THREADS=1 lake build DLNFibre.DLN.Aoyagi.ChartTopology
cd lean && LEAN_NUM_THREADS=1 lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

The intended `scripts/lb` route was not available in this sandbox because the
shared `~/.lake-shared` lock write requires unsandboxed execution.  The local
single-worker build route passed.
