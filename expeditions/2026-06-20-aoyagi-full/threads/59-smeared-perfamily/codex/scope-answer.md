**1. Attempt Order**

1. **(c) Generic rate route.**  
   Delivers the core identity `routeMCore (phi_sm_M u) = (u_p)^2 * U` from abstract matrices plus `P₁ * Λ₀ = P₂`. Cast-risk: medium if stated away from dependent widths. Stands alone: yes, it is the main mathematical bedrock.

2. **(a) Structural front-factor bridge.**  
   Delivers the hypothesis needed by your banked `(2)/(3)`: `P = U * V` through the bottleneck and `det(Vρ) ≠ 0`. Cast-risk: medium-high, but localized. Stands alone: yes, especially if it ends in an abstract `FrontFactorsThrough` theorem.

3. **(b) Opaque-width chart packaging.**  
   Delivers the actual `phi_sm_M = ψ ∘ R` chart over dependent-Fin widths. Cast-risk: high. Stands alone: partially; useful if it exposes clean typed interfaces, but easy to sink time into casts.

4. **(e) Final divergence headline via existing contract.**  
   Delivers the theorem users want, but mostly consumes prior pieces. Cast-risk: low-medium if using `routeMCore_box_diverges_smearedContract`; high if building full `NodeAchieverChart`. Stands alone: no.

5. **(d) Rational `cov` change-of-variables.**  
   Delivers the determinant/Jacobian side. Cast-risk: high and analytically delicate. Stands alone: yes mathematically, but least urgent if the contract can take `hSdiv` separately.

**2. Highest-Leverage Abstraction**

Inference: yes, state the rate over an abstract front-factorization and shear cancellation, then instantiate dependent-Fin widths only once.

Concretely, aim for a lemma shaped like this, modulo actual signatures:

```lean
theorem routeMCore_smeared_rate_of_frontShear_cancel
    (M : Model)
    (u : SmearedChartSource M)
    -- unpacked chart data
    (z : ℝ)
    (P P₁ P₂ Hbar Sbot Λ₀ : Matrix _ _ ℝ)
    (Urate : ℝ)
    -- structural interpretation of the packed parameters
    (h_chart :
      prodAux M (A_of_smeared u) (L - 1)
        =
      P)
    (h_decomp :
      P * A_tail_of_smeared u
        =
      P₁ * (z • Hbar - Λ₀ * Sbot) + P₂ * Sbot)
    -- the only algebraic cancellation needed
    (h_cancel : P₁ * Λ₀ = P₂)
    -- definition of the remaining positive factor
    (h_U : Urate = ‖P₁ * Hbar‖^2)
    :
    routeMCore M (phi_sm_M u) = z^2 * Urate
```

Even better, make this independent of `phi_sm_M`:

```lean
theorem routeMCore_rate_of_telescoping
    (W : NetworkWeights M)
    (z : ℝ)
    (P₁ P₂ Hbar Sbot Λ₀ : Matrix _ _ ℝ)
    (Urate : ℝ)
    (h_eval :
      evalFrontTail M W =
        P₁ * (z • Hbar - Λ₀ * Sbot) + P₂ * Sbot)
    (h_cancel : P₁ * Λ₀ = P₂)
    (h_U : Urate = ‖P₁ * Hbar‖^2)
    :
    routeMCore M W = z^2 * Urate
```

Then `(b)` only has to prove that `phi_sm_M u` supplies `h_eval`, not reprove the rate through casts.

**3. Cheapest Honest Ceiling**

Leave exactly one gap at the chart-instantiation boundary, not inside the algebra.

Suggested gap theorem:

```lean
theorem smearedChart_telescoping_eval
    (M : Model)
    (u : SmearedChartSource M)
    :
    ∃ z P₁ P₂ Hbar Sbot Λ₀ Urate,
      evalFrontTail M (phi_sm_M u)
        =
      P₁ * (z • Hbar - Λ₀ * Sbot) + P₂ * Sbot
      ∧ P₁ * Λ₀ = P₂
      ∧ Urate = ‖P₁ * Hbar‖^2
      ∧ pivotCoordinate u = z
```

If your downstream contract wants the exact rate directly, make the single gap even narrower:

```lean
theorem routeMCore_smeared_rate_chart_gap
    (M : Model)
    (u : SmearedChartSource M)
    :
    routeMCore M (phi_sm_M u) =
      (pivotCoordinate u)^2 * smearedU M u
```

But the first version is better bedrock: it isolates the dependent-Fin chart/cast bookkeeping while preserving the reusable algebraic rate proof.

**4. Trap To Avoid**

Do not let “factors through the bottleneck” blur into “the relevant block has full rank” without naming the selected rows/columns and their casts. The cancellation needs the exact `P₂ = P₁ * Λ₀` in the same matrix types as the telescoping identity. If those live behind definitional hopes about `Fin` widths, Lean will make the proof brittle. Keep selectors explicit and push all dependent-width transport into one bridge theorem.