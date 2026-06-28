**A. RANKING**

1. **R2: cheapest, medium effort.** Four explicit `2×2` pivot charts, then `a`-axis radial divisor plus `1×1` Schur residual. Blocking difficulty: Leanizing the chart change of variables/Jacobian and shifted-box bookkeeping. Math is exactly aligned with available lemmas.

2. **R1: higher risk.** A global `2×2` factorisation without charts looks attractive, but the obvious `det / norm` bound only gives the corank-1 threshold `c' < 1/2`. Anything sharp needs a pivot choice or SVD, which is worse in Lean.

3. **R3: likely not cheap / possibly dead.** Row-wise product domination shares the same `S`; corank-1 cores do not decouple. You get Gram-determinant singularities of `S Sᵀ`, essentially a new proof.

4. **R4: unbounded effort.** Any new resolution or singular-value proof is mathematically plausible but far from the existing API.

**B. SKELETON**

Winner: **R2**, manual `r = 2` chart proof.

```lean
1. Prove an auxiliary `chart00Finite (e)` for the chart `|Δ₀₀| = max entries`.
   Inputs: `0 < e`, `e < 2`, and either `e < p/2` or `p/2 < e ∧ e - p/2 < 1/2`.

2. On chart `00`, write
   b = a*g, c = a*h, d = a*(h*g + s),
   so Δ = a • R(g,h,s), with R = !![1,g; h,h*g+s].
   Ratios satisfy `|g| ≤ 1`, `|h| ≤ 1`, `|s| ≤ 2`.
   Jacobian contributes `|a|^3`.  -- INFERENCE: local r=2 chart-COV lemma.

3. Apply `schur_minorPivot_split (r:=2) (p:=p) (j:=1)` to `R`.
   Since `Fin 1` collapses, `Sc = !![s]`, and
   frobSq (R*S) ≳ frobSq (X + g•Y) + frobSq (s•Y).

4. Hence
   frobSq (Δ*S)^(-e) ≲ |a|^(-2*e) *
     (‖X + g•Y‖² + s² * ‖Y‖²)^(-e).

5. Integrate the `a` variable using `radial_aAxis_divisor_lt_top`;
   threshold is `3 - 2*e > -1`, i.e. `e < 2`.

6. Small case `e < p/2`:
   dominate by `(‖X + g•Y‖²)^(-e)`;
   translate/enlarge the `X` box and use `radial_morse_dominates_lt_top`.
   The remaining `g,h,s,Y` boxes have finite measure.

7. Large case `p/2 < e`:
   apply `core_T_peel_le_aeG (m := p-1)` to the `U = X + g•Y` variables.
   Residual exponent is `β = e - p/2`.

8. Show `0 < β` from `p/2 < e`, and `β < 1/2` from
   `e < schurLambdaP p 2 ≤ (p+1)/2`.

9. Close the residual with
   `schurCoreP_one p hp β hβ0 hβ_lt (T' := enlargedT)`.
   Positivity of `s² * frobSq Y` is a.e. from `s ≠ 0` a.e. and
   `frobSqGP_ne_zero_ae`.

10. Obtain the other three charts by row/column permutations of `chart00`.
    -- INFERENCE: permutation invariance/box-preserving lemma names.

11. Cover the `2×2` box by the four max-entry charts, ignoring `Δ = 0` as null.
    Sum the four finite chart integrals.

12. Threshold arithmetic for the theorem:
    from `hc' : c' < schurLambdaP p 2`,
    get `c' < 2` using `min ≤ 4`,
    and `c' < (p+1)/2` using `min ≤ 1+p`.

13. If `c' = p/2`, choose `e` with `p/2 < e < schurLambdaP p 2`,
    prove finiteness at `e`, then dominate the bounded-box integrand for `c'`
    by the one for `e`. -- INFERENCE: bounded exponent monotonicity lemma.
```

Hardest step: the explicit `chart00` change of variables plus lower bound in steps 2-4. Once that exists, the exponent bookkeeping is routine: `e < 2` handles the radial `a` divisor, and `e < (p+1)/2` makes the corank-1 residual exponent `< 1/2`.