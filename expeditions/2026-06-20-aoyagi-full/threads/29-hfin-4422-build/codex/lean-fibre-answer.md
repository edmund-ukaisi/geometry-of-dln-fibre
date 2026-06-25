**1. Ranking**

Rank: **F1 (with max-pivot hidden inside a global corollary) < F3 < F2**.

Pick **F1**, but do **not** split the outer assembly. Prove a max-pivot shear lemma, then immediately wrap it in a global `∀ Y` fibre lemma using `Finset.exists_max_image`; the chosen pivot never appears in the statement, so no measurability of the choice is needed.

```lean
noncomputable def matBox (p n : ℕ) (T : ℝ) : Set (Fin p → Fin n → ℝ) :=
  {X | ∀ i k, X i k ∈ Set.Icc (-T) T}

noncomputable def frobSq {a b : Type*} [Fintype a] [Fintype b]
    (M : a → b → ℝ) : ℝ :=
  ∑ i, ∑ j, (M i j)^2

noncomputable def rmatMul {p n q : ℕ}
    (X : Fin p → Fin n → ℝ) (Y : Fin n → Fin q → ℝ) :
    Fin p → Fin q → ℝ :=
  fun i j => ∑ k, X i k * Y k j

noncomputable def fibreConst (m r s : ℕ) (T c' : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((((r + 1) * (s + 1) : ℕ) : ℝ) ^ c')) *
    Kbound (m + 1) c' ((((r + 1 : ℕ) : ℝ) * T)) *
    volume (morseBox ((m + 1) * r) T)

theorem fibre_lintegral_mul_le
    {m r s : ℕ} {T c' : ℝ} (hT : 0 < T) (hc0 : 0 ≤ c')
    (hc : c' < (m + 1 : ℝ) / 2)
    (Y : Fin (r + 1) → Fin (s + 1) → ℝ) :
    ∫⁻ X in matBox (m + 1) (r + 1) T,
      ENNReal.ofReal ((frobSq (rmatMul X Y)) ^ (-c'))
    ≤ fibreConst m r s T c' *
      ENNReal.ofReal ((frobSq Y) ^ (-c')) := by
  ...
```

If you use a true extended kernel that is `⊤` at zero, add `(hY : Y ≠ 0)` to this theorem. With your current `ENNReal.ofReal (Real.rpow ...)` convention, the all-`Y` statement is cleanest.

**2. Mechanics**

Use the **hand-built normalized shear**, not the determinant linear-map route.

For a max pivot `(ℓ,j)` with `Y ℓ j ≠ 0` and `∀ k j', |Y k j'| ≤ |Y ℓ j|`, set per row

```lean
u_i = X i ℓ + ∑ k ≠ ℓ, X i k * (Y k j / Y ℓ j)
```

Then `(X ⬝ Y) i j = Y ℓ j * u_i`, hence

```lean
frobSq (X ⬝ Y) ≥ (Y ℓ j)^2 * ∑ i, u_i^2
```

The change of variables is determinant `1`; `|Y ℓ j|^{-2c'}` enters from this algebraic inequality, not from the Jacobian.

Lean route:

```lean
measurePreserving_shearAt
MeasurePreserving.comp
MeasurePreserving.setLIntegral_comp_preimage
volume_measurePreserving_piCongrLeft
```

Flatten or reindex the matrix coordinates, apply `measurePreserving_shearAt` once for each row coordinate `(i, ℓ)`, and compose. Show `matBox` is contained in the preimage of the target box

```lean
u ∈ [-((r+1)T), (r+1)T]^(m+1),
spectators ∈ [-T,T]^((m+1)r)
```

The linear-map lemma does exist locally as

```lean
MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
```

and can be combined with `lintegral_map`, but it is worse here. The unnormalised map gives determinant `|Y ℓ j|^p`, which is the wrong power until you prove extra translated-box scaling estimates. The normalised linear map has determinant `1`, but then it is just the shear with heavier determinant bookkeeping.

**3. Telescoping**

Yes: the constants are fixed and `Y`-independent.

Let

```lean
C0 := fibreConst 3 3 1 1 c'   -- A0 fibre: p=4, n=4, q=2
C1 := fibreConst 3 1 1 1 c'   -- A1 fibre: p=4, n=2, q=2
```

Then Tonelli plus the fibre lemma gives

```lean
∫⁻ A2 in B₂₂, ∫⁻ A1 in B₄₂, ∫⁻ A0 in B₄₄,
    ‖A0 * A1 * A2‖_F^(-2c')
≤ C0 * ∫⁻ A2 in B₂₂, ∫⁻ A1 in B₄₂,
    ‖A1 * A2‖_F^(-2c')
≤ C0 * C1 * ∫⁻ A2 in B₂₂,
    ‖A2‖_F^(-2c')
< ⊤.
```

The final radial step is dimension `4`, so instantiate

```lean
radial_ball_iff 3 R (-(2 * c')) hR
```

with any `R > 2` containing the `2 × 2` box, for example `R = 3`. The condition is

```lean
-(4 : ℝ) < -(2 * c')
```

which is exactly `c' < 2` by `linarith`. You can also use your existing boxed version directly as `sumSqND_box_lt_top 3 1 one_pos c' hc`.