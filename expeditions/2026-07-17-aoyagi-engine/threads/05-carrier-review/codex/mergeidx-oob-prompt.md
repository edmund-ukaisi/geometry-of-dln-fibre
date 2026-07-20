# Decorrelated adjudication: is the out-of-range `mergeIdx` default in `stepUpdate` acceptable?

Independent reviewer. One sharp question about a Lean 4 skeleton certifying Aoyagi's DLN
resolution. Verdict + concrete counterexample if you find one; distinguish INFER from FACT.

## Context (established, treat as given)

The engine's finiteness certificate `∀ M, RouteMBoxThresholdFinite M` (box integral finite for
`c' < ½·minAdm M`) is proved by `engine_box_threshold_finite`, which consumes ONLY `region_glue`
(needs `ChartBridge` + a ratio side-condition over `terminalExponents`) and the lower-bound half of
`exponent_ledger_bridge`. It **does NOT consume** `case_step_invariant`/`StepRel`. This was verified
in a prior round: `StepRel` could be replaced by `True` without changing the driver. `minAdm` is
banked independently as `min` over `Adm M` of `Mval`. `StepRel`'s role is now FIDELITY: certifying
that the tree's per-step transitions match Aoyagi's page-image construction.

## The rung-1 faithful transition (just landed)

```
structure RootLedger where
  numDiv : ℕ ; divExp : Fin numDiv → ℕ ; divTilde : Fin numDiv → ℕ ; cleared : ℕ

def rootLedger : ResolutionTree M → RootLedger      -- projects a subtree's root ledger core

def stepUpdate (n : StepData M) (c : StepCase) (σ : ChartSubst M) : RootLedger :=
  match c with
  | case11 =>                                        -- merge INTO divisor σ.mergeIdx (in place)
      { numDiv := n.numDiv
        divExp := fun k => if (k:ℕ) = σ.mergeIdx then n.divExp k + σ.runLen * n.resCols else n.divExp k
        divTilde := fun k => if (k:ℕ) = σ.mergeIdx then n.cleared else n.divTilde k
        cleared := n.cleared }
  | case12 =>                                        -- SPLIT divisor σ.mergeIdx into a new pivot
      { numDiv := n.numDiv + 1
        divExp := Fin.snoc n.divExp
          ((if h : σ.mergeIdx < n.numDiv then n.divExp ⟨σ.mergeIdx, h⟩ else 0) + σ.runLen * n.resCols)
        divTilde := Fin.snoc n.divTilde n.cleared
        cleared := n.cleared + 1 }
  | case2 =>                                         -- append a new shared divisor
      { numDiv := n.numDiv + 1
        divExp := Fin.snoc n.divExp (n.resRows * n.resCols)
        divTilde := Fin.snoc n.divTilde n.cleared
        cleared := n.cleared + n.resRows }

def StepRel (n : StepData M) (e : Edge M) : Prop :=
  rootLedger e.child = stepUpdate n e.case e.subst      -- FULL structural equality of RootLedger
```

`σ.mergeIdx : ℕ` is a raw natural (not `Fin n.numDiv`), so `stepUpdate` is total. **Out-of-range
consequences** (`mergeIdx ≥ n.numDiv`):

- **case11:** no `k : Fin n.numDiv` satisfies `(k:ℕ) = mergeIdx`, so `divExp`/`divTilde` are
  UNCHANGED and `numDiv`/`cleared` unchanged — `stepUpdate = the parent ledger` (a NO-OP). So `StepRel`
  ACCEPTS a "case-1(1) edge" whose child ledger equals the parent's (a step that merges nothing).
- **case12:** the `dite` default gives the new pivot exponent `0 + runLen·resCols` (dropping the
  `n.divExp(mergeIdx)` base term), i.e. a DIFFERENT exponent than the in-range `divExp(mergeIdx) +
  runLen·resCols`.

Note: the real construction (`monomialization_terminates`, a sorried hole) always sets `mergeIdx` to
the actual target divisor (in range); an out-of-range `mergeIdx` would also break the termination
measure `μ = (L+1−S, layerCap−J, #{k | J < t̃})` for case-1(1) (a no-op does not decrease `μ`).

## Questions

**Q1.** Is the out-of-range `mergeIdx` default (case11 no-op / case12 base-dropping) a defect that
should block the rung-1 spot-check, or is it acceptable? Weigh: (i) `StepRel` is off the finiteness
critical path (never consumed by the driver), so no finiteness-soundness impact; (ii) `StepRel`'s
current PURPOSE is fidelity, and a no-op case-1(1) or a base-dropping case-1(2) is a non-faithful
transition that `StepRel` nonetheless accepts; (iii) the real construction never emits out-of-range
`mergeIdx` (breaks fidelity AND termination). Is this "acceptable totality default, never exercised"
or "a fidelity hole that should carry an in-range guard"?

**Q2.** If a guard is warranted, what is the minimal fix — add `σ.mergeIdx < n.numDiv` as a hypothesis
in `StepRel`'s case-1 clauses (making `StepRel` reject out-of-range), or make `mergeIdx : Fin
n.numDiv` a typed field of the edge (no out-of-range state possible)? Any downside to the typed-`Fin`
form for the construction (which must produce these edges)?

**Q3 (content-rejection sanity check).** `StepRel` is a FULL `RootLedger` structural equality. Confirm
or refute: this rejects not only extra/missing divisors (via `numDiv` mismatch) but ALSO a
`numDiv`-preserving corruption (right divisor count, wrong `divExp`/`divTilde`/`cleared`) — because
structural equality of `RootLedger` is componentwise on all four fields. Is there any way a
`numDiv`-preserving but exponent-wrong child could satisfy `rootLedger child = stepUpdate n c σ`?

**Q4.** Any other soundness or fidelity gap in `stepUpdate`/`StepRel` as written (e.g. the case-1(2)
`cleared += 1` vs case-2 `cleared += resRows`, or the deliberately-omitted `support` propagation)
that a spot-check should surface? (Support propagation is knowingly STOP-AND-SURFACEd to a later rung
— flag only if its omission breaks something beyond fidelity-of-sharing.)
