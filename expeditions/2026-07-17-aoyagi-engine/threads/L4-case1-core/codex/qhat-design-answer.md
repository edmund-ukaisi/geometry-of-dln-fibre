## 1. Is Q̂ genuinely required?

**Inference:** Your worry is correct about the collapsed witness, but not about `Q̂` being logically necessary for every nontrivial `StepInv`.

From exact division one may retain the strict transforms:

```lean
resid' j := if j = p then 1 else w j
q' i j := q i j ∘ σ
```

so that `resid j ∘ σ = w p * resid' j`. This preserves the residual index set without `Q̂`.

The distinction is that `StepInv` as stated does not require `resid'` to be Aoyagi’s next canonical residual block. If the next state specifically expects the Schur-reduced block

\[
H_{\mathrm{next}}=\operatorname{diag}(1,\delta-\gamma\beta),
\]

then pullback alone is insufficient: after the source-realizable right operation one still has

\[
H_{\mathrm{pre}}=Q_1^{-1}H_{\mathrm{next}}.
\]

The left operation is not a source substitution. Passing from the raw strict transform to `Hnext` therefore requires row recombination—either explicitly as `Q̂`, or disguised by expanding the same coefficients entrywise.

Thus:

- nontrivial residual: no `Q̂` required;
- canonical next-state residual with genuine recursion progress: `Q̂` or its entrywise equivalent is required.

The invariant should therefore include a predicate identifying `resid` with the state’s prescribed residual block; otherwise the lazy and honest witnesses are indistinguishable.

## 2. Clean abstract statement

Your ratio orientation is correct. I would take the explicit inverse row matrix `R` as input, avoiding both diagonal inversion and Mathlib’s matrix inverse API:

```lean
def weightedCofactor
    (c : X → ι → ι → ℝ) (R : X → Matrix ι ι ℝ) :
    X → Matrix ι ι ℝ :=
  fun x a d => c x a d * R x a d
```

The core theorem should be:

```lean
theorem weightedCofactor_commutes
    [Fintype ι] [LinearOrder ι]
    (hlo : ∀ x ∈ V, ∀ a d, a < d → R x a d = 0)
    (hratio : ∀ x ∈ V, ∀ a d, d ≤ a →
      b x a = c x a d * b x d) :
    Set.EqOn
      (fun x => Matrix.diagonal (b x) * R x)
      (fun x => weightedCofactor c R x * Matrix.diagonal (b x)) V
```

Continuity is independent:

```lean
theorem weightedCofactor_continuousOn
    (hc : ∀ a d, ContinuousOn (fun x => c x a d) V)
    (hR : ∀ a d, ContinuousOn (fun x => R x a d) V) :
    ContinuousOn (weightedCofactor c R) V
```

For unipotence define a small local predicate:

```lean
def UnitLower (A : Matrix ι ι ℝ) :=
  (∀ a, A a a = 1) ∧ ∀ a d, a < d → A a d = 0
```

`R` unit-lower plus `c x a a = 1` implies `Q̂` unit-lower. The diagonal normalization is essential: `b_a = c_aa b_a` does not imply `c_aa = 1` where `b_a = 0`.

For `Q̂ 0 = I`, it suffices to assume `R 0 = 1` and `c 0 a a = 1`. `Q₁ 0 = I` is only needed to derive `R 0 = I`; it is irrelevant to the commutation identity.

**Verified Mathlib v4.29 facts:** `Matrix.diagonal_mul` and `Matrix.mul_diagonal` are simp lemmas. `BlockTriangular id` means upper-triangular; lower-triangular uses `BlockTriangular OrderDual.toDual`. There is no general matrix `UnitLower` predicate. Determinants and triangular-inverse machinery are unnecessary here.

## 3. Smallest useful decomposition

Ranked by importance:

1. **Canonical Schur identity:** `Hpre = R * Hnext` after the right operation has entered `σ`. This prevents the lazy residual.
2. **Exact division:** establishes `b'` and the strict-transform residuals.
3. **Weighted row transport:**

   ```lean
   diag b' * Hpre = Qhat * (diag b' * Hnext)
   ```

4. **Entrywise continuity of `Qhat`:** required by `StepInv`.
5. **`UnitLower` and `Qhat 0 = I`:** needed only by the stronger normal-form invariant.
6. **`Q₁` inverse, determinant, and general triangular theory:** not load-bearing for divisibility-only `StepInv`.

So the leaf can consume exact division, the explicit Schur identity, and a three-lemma `weightedCofactor` module; no large matrix development is needed.