Route **A** is less cast-painful.

Do not track `D(T1') = D(T1)` structurally through dependent matrix products. Normalize the delta algebraically, then prove each matrix entry is a finite sum of scalar products whose zero-derivative factor is explicit. This matches the existing `schurCorrection` proof style in your repo.

Core helper lemmas I would land:

```lean
open scoped BigOperators Matrix Topology
open Matrix

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem hasStrictFDerivAt_matrix_mul_entry_of_left_zero
    {m n p : Type*} [Fintype n]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X}
    (i : m) (j : p)
    (hAd : ∀ k, HasStrictFDerivAt (fun y => A y i k) (0 : X →L[ℝ] ℝ) x)
    (hA0 : ∀ k, A x i k = 0)
    (hB : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y k j) x) :
    HasStrictFDerivAt (fun y => (A y * B y) i j) (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ k : n,
      HasStrictFDerivAt (fun y => A y i k * B y k j) (0 : X →L[ℝ] ℝ) x := by
    intro k
    have hBd :
        HasStrictFDerivAt (fun y => B y k j)
          (fderiv ℝ (fun y => B y k j) x) x :=
      (hB k).hasStrictFDerivAt (by simp)
    have hm := (hAd k).mul hBd
    simpa [hA0 k] using hm
  have hsum :=
    HasStrictFDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  simpa [Matrix.mul_apply, Finset.sum_apply] using hsum
```

```lean
theorem hasStrictFDerivAt_matrix_mul_entry_of_right_zero
    {m n p : Type*} [Fintype n]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ} {x : X}
    (i : m) (j : p)
    (hA : ∀ k, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y i k) x)
    (hBd : ∀ k, HasStrictFDerivAt (fun y => B y k j) (0 : X →L[ℝ] ℝ) x)
    (hB0 : ∀ k, B x k j = 0) :
    HasStrictFDerivAt (fun y => (A y * B y) i j) (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ k : n,
      HasStrictFDerivAt (fun y => A y i k * B y k j) (0 : X →L[ℝ] ℝ) x := by
    intro k
    have hAd :
        HasStrictFDerivAt (fun y => A y i k)
          (fderiv ℝ (fun y => A y i k) x) x :=
      (hA k).hasStrictFDerivAt (by simp)
    have hm := hAd.mul (hBd k)
    simpa [hB0 k] using hm
  have hsum :=
    HasStrictFDerivAt.sum (u := Finset.univ) (fun k _ => hterm k)
  simpa [Matrix.mul_apply, Finset.sum_apply] using hsum
```

Triple product helper:

```lean
theorem hasStrictFDerivAt_matrix_triple_mul_entry_zero
    {m n p q : Type*} [Fintype n] [Fintype p]
    {A : X → Matrix m n ℝ} {B : X → Matrix n p ℝ}
    {C : X → Matrix p q ℝ} {x : X}
    (i : m) (j : q)
    (hA : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y a b) x)
    (hB : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => B y a b) x)
    (hC : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => C y a b) x)
    (hA0 : ∀ a b, A x a b = 0)
    (hC0 : ∀ a b, C x a b = 0) :
    HasStrictFDerivAt (fun y => (A y * B y * C y) i j)
      (0 : X →L[ℝ] ℝ) x := by
  have hterm : ∀ l k,
      HasStrictFDerivAt
        (fun y => A y i k * B y k l * C y l j)
        (0 : X →L[ℝ] ℝ) x := by
    intro l k
    exact hasStrictFDerivAt_triple_mul_zero
      (fun y => A y i k) (fun y => B y k l) (fun y => C y l j)
      (hA i k) (hB k l) (hC l j) (hA0 i k) (hC0 l j)

  have hsum :=
    HasStrictFDerivAt.sum (u := Finset.univ) (fun l _ =>
      HasStrictFDerivAt.sum (u := Finset.univ) (fun k _ => hterm l k))

  have heq :
      (fun y => (A y * B y * C y) i j)
        = fun y => ∑ l : p, ∑ k : n,
            A y i k * B y k l * C y l j := by
    funext y
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Matrix.mul_apply, Finset.sum_mul]
    simp [mul_assoc]

  simpa [heq, Finset.sum_apply] using hsum
```

Then prove these blocks entrywise:

```lean
K  := Z1 * P00⁻¹ * Y0
R  := Z1 * A1⁻¹ * A0⁻¹ * Y0
U  := Z1 * A1⁻¹ * Y1
S1 := T1 - U
W  := 1 + R
Br := (1 - K) * S1 + U + R * T1
```

Use the triple helper for `K`, `R`, `U`: outer factors vanish. For `R`, take the middle matrix as `A1⁻¹ * A0⁻¹`, whose entries are `ContDiffAt` by `contDiffAt_matrix_mul_entry`.

Algebraically normalize:

```lean
Br - T1 = -(K * S1) + R * T1
T1' - T1 = (W⁻¹ - 1) * Br + (Br - T1)
```

Prove these as matrix equalities with `calc`, `rw [sub_mul, one_mul]`, and `abel`; if dependent shapes fight, do `ext i j` and then `simp [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]`.

Then:

- `D(K*S1)=0` by `matrix_mul_entry_of_left_zero`.
- `D(R*T1)=0` by `matrix_mul_entry_of_left_zero`.
- `D((W⁻¹-1)*Br)=0` by `matrix_mul_entry_of_left_zero`, once `D(W⁻¹-1)=0`.

For `W⁻¹`, avoid determinant/adjugate derivative bookkeeping. Since `W = 1 + R`, `R(0)=0`, `DR(0)=0`, and `det W(0)=1`, use eventual invertibility and the local identity

```lean
W⁻¹ - 1 = -(W⁻¹ * (W - 1)) = -(W⁻¹ * R)
```

on a neighborhood of `0`. Then `D(W⁻¹-1)=0` follows from the right-zero matrix-product helper: left factor `W⁻¹` is merely `ContDiffAt`, right factor `R` has value and strict derivative zero.

So yes, `D(W⁻¹)(0)=0` is true, but I would not prove it via `det⁻¹ * adjugate`. Your existing `contDiffAt_matrix_inv_entry_of_det_ne_zero` gives smoothness of `W⁻¹`; the inverse identity gives the zero derivative with much less algebra.

Finally,

```lean
Y1' - Y1 = A0⁻¹ * Y0 * (T1 - T1')
```

Let `C := A0⁻¹ * Y0`. Its entries are `ContDiffAt`. Since `T1 - T1' = -(T1' - T1)` has value `0` and strict derivative `0`, apply `matrix_mul_entry_of_right_zero` to `C * (T1 - T1')`.

For the final matrix/flat-coordinate result, descend with nested `hasStrictFDerivAt_pi'`; keep all hard work entrywise.