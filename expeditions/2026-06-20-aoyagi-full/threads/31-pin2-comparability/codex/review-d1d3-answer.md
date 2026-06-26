**Q1. VERIFY:** `change` cannot weaken or alter the statement. In Lean, `change tgt'` is accepted only when the current target and `tgt'` are definitionally equal. It is not a rewrite by theorem, not an implication, and not a replacement by a merely pointwise-equal function. ([lean-lang.org](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/))

So if the current goal really came from `Φscore` after `rw [hΦscore, hScoreDef]` and the `Score` summand split, then the displayed `change Measurable fun w => ... Mw w ...` proves that same obligation. If one of the four `REINDEX_EXPR` occurrences differed non-definitionally, `change` would fail. A wrong statement cannot be masked by `change`; only notation/unfolding/β-ζ-reduction/alpha-equivalent binder names can disappear.

**INFER:** The only possible unsoundness would be upstream: e.g. `hΦscore`/`hScoreDef` not defining the intended mathematical score. But within this subgoal, `change` itself is kernel-checked conversion.

**Q2. VERIFY:** Sound. Mathlib’s matrix inverse is definitionally the adjugate formula:
`A⁻¹ = A.det⁻¹ʳ • A.adjugate`, by `Matrix.inv_def`. The source defines matrix inverse as `A.det⁻¹ʳ • A.adjugate` and `inv_def` is `rfl`. ([raw.githubusercontent.com](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean))

For `ℝ`, using `Ring.inverse_eq_inv'` to rewrite `Ring.inverse` to field `Inv.inv` is exactly the needed total equality. If that rewrite elaborates, Lean has checked it at all inputs, including `0`. There is no missing nonzero side condition. Thus `measurable_inv` applies to the total real inverse, and the determinant/adjugate/product measurability route is sound.

Caveat: this proves measurability of Lean’s total matrix inverse, which is zero at singular matrices. If the informal mathematics meant a partial inverse only on `det ≠ 0`, that is a modeling issue, not a Lean proof gap.

**Q3. VERIFY:** Not circular at the bridge lemma. The proof composes two independent facts:

1. germ equality:
`rlctAtOn (fun x => Φcore (Psi x)) wstar = rlctAtOn Φscore wstar`

2. local-diffeo invariance:
`rlctAtOn (fun w => Φcore (Psi w)) wstar = rlctAtOn Φcore wstar`

After

```lean
rw [← rlctAtOn_germ_local (fun x => Φcore (Psi x)) Φscore wstar hcomp]
```

the goal becomes exactly

```lean
rlctAtOn (fun w => Φcore (Psi w)) wstar = rlctAtOn Φcore wstar
```

up to alpha-renaming of `x`/`w`, so the `exact rlctAtOn_comp_localDiffeo ...` matches.

**INFER:** The hypotheses encode stronger/different geometric data: a local reparametrization with invertible strict derivative, fixed basepoint, and a germ identity. They do not mention `rlctAtOn Φscore = rlctAtOn Φcore`.

**Q4. VERIFY/INFER:** Not vacuous. The identity case satisfies the shape: `Psi = id`, `e = ContinuousLinearEquiv.refl ℝ M`, and `Φscore =ᶠ[nhds wstar] Φcore`.

No overclaim: the lemma is only a conditional reduction. It does not assert existence of `Psi` or prove `hcomp`; it defers that geometry to the consumer.