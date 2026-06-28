**Q1 Ranking**

1. **(b) abstract `λ` bundle.** Lowest friction for this scaffold. The wrapper does not need to compute `λ`; it only needs a threshold symbol that the deferred `recStep` can use. Concrete `λ 2 = 2` / `λ 3 = 4` are then local instantiation rewrites, not global recursion proofs.

2. **(a) `def schurLambda` by strong recursion.** Good eventually, but extra Lean work now: `ℝ`-valued finite minima are `noncomputable`; you need `classical`, `Finset.inf'`/nonempty witnesses, beta lemmas for `Nat.strongRecOn`, and arithmetic for `r - j < r`. Proving `schurLambda 2 4 = 2` and `schurLambda 3 4 = 4` will likely require custom simp lemmas, not just `norm_num`.

3. **(c) inline min-expression.** Worst for reuse. It avoids a definition but makes every theorem statement and application heavier; you will fight `lt_min_iff`, finite-min unfolding, coercions, and duplicated threshold expressions.

Recommendation: use **(b)** now. Keep `λ` abstract and package only the inequalities the real `recStep` will consume:

```lean
structure SchurThreshold (p : ℕ) (λ : ℕ → ℝ) : Prop where
  lambda0 : λ 0 = 0
  radial_le : ∀ {r : ℕ}, 1 ≤ r → λ r ≤ (r ^ 2 : ℝ) / 2
  peel_le :
    ∀ {r j : ℕ}, 1 ≤ j → j ≤ r →
      λ r ≤ ((j : ℝ) * (p : ℝ)) / 2 + λ (r - j)
```

**Q2 Shape**

Confident v4.29 names: `Nat.strong_induction_on`, `Nat.strongRecOn`, `Nat.strongRecOn'`, `Nat.strongRecOn'_beta`, `Finset.inf'`, `Finset.inf'_le`, `Finset.exists_mem_eq_inf'`. For the arithmetic proof `r - j < r`, use `omega`.

```lean
noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

abbrev SchurCore (p r : ℕ) (c' T : ℝ) : Prop :=
  (∫⁻ Δ in matBox r r T, ∫⁻ S in matBox r p T,
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))) < ⊤

/-- The IH in the exact form consumed by the Schur peel:
the JOINT lower core over free `Δ` and free `S`, not an `Sc`-only statement. -/
abbrev SchurLowerIH (p : ℕ) (λ : ℕ → ℝ) (r : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ r →
    ∀ c'' : ℝ, 0 < c'' → c'' < λ (r - j) →
      ∀ T'' : ℝ, 0 < T'' → SchurCore p (r - j) c'' T''

/-- Deferred analytic step. Stub this, not the wrapper. -/
abbrev SchurRecStep (p : ℕ) (λ : ℕ → ℝ) : Prop :=
  ∀ r : ℕ, SchurThreshold p λ → SchurLowerIH p λ r →
    ∀ c' : ℝ, 0 < c' → c' < λ r →
      ∀ T : ℝ, 0 < T → SchurCore p r c' T

/-- Clean strong-induction wrapper. No analytic content here. -/
theorem core_schurGen_lt_top
    (p : ℕ) (λ : ℕ → ℝ)
    (hλ : SchurThreshold p λ)
    (hstep : SchurRecStep p λ) :
    ∀ r : ℕ, ∀ c' : ℝ, 0 < c' → c' < λ r →
      ∀ T : ℝ, 0 < T → SchurCore p r c' T := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      exact hstep r hλ
        (fun j hj0 hjr c'' hc0 hcλ T'' hT'' =>
          ih (r - j) (by omega) c'' hc0 hcλ T'' hT'')

end DLNFibre.DLN.RLCT
```

Concrete proved instances then match literally:

```lean
example (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) (T : ℝ) (hT : 0 < T) :
    SchurCore 4 2 c' T := by
  simpa [SchurCore] using core_schur2_lt_top c' hc0 hc' T hT
```

**Q3 Gotchas**

- `Nat.strong_induction_on` is `Prop`-only. For defining `schurLambda : ℕ → ℝ`, use `Nat.strongRecOn` or `Nat.strongRecOn'`, not `strong_induction_on`.
- Motive inference is smoother if you `intro r; induction r using Nat.strong_induction_on`, as above. If using term mode, specify `(p := fun r => ...)`.
- For option (a), expect `noncomputable section`, `classical`, finite-min nonempty proofs, and beta unfolding via verified names `Nat.strongRecOn_eq` or `Nat.strongRecOn'_beta`.
- For the deferred step, make the wrapper theorem take `hstep : SchurRecStep p λ` as a hypothesis. Then `#print axioms core_schurGen_lt_top` stays clean; only the concrete theorem that supplies the sorry/axiom step should depend on that deferred constant.
- If you want the deferred boundary named in `#print axioms`, prefer a top-level named `axiom schurRecStep_deferred : SchurRecStep 4 λ` over an anonymous local `have ... := by sorry`.