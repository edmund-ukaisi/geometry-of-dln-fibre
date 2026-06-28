Cleanest route: prove `δ`, not the raw map, through two decoded “delta payloads”, then re-encode by the CLEs. This avoids most `Function.update` and `match` pain.

**Main Decomposition**
Yes to reducing products/Pi coordinates, but I would not first prove the full raw `psiSplitRawL2Core` is smooth. Instead prove:

```lean
-- decoded core correction: zero on all layers except last
noncomputable def l2CoreΔTuple ... (q : DeepestSplit H r (deepestNGauge H r)) :
    Params (deepestM H r) :=
  Function.update 0 (lastLayer hL)
    (l2T1p H r hr hL hL2 q - coreLast H r hL q)

-- decoded reg/spec correction: zero on all tags except last-layer Y
noncomputable def l2GaugeΔ ... (q : DeepestSplit H r (deepestNGauge H r)) :
    RegGaugeIdx H r → ℝ := fun idx =>
  match idx with
  | ⟨s, Sum.inl (Sum.inr (i, j))⟩ =>
      if h : s = lastLayer hL then
        (l2Y1p H r hr hL hL2 q - l2Y1 H r hr hL q) i (h ▸ j)
      else 0
  | _ => 0
```

Then prove one payload equality:

```lean
private theorem psiSplitDeltaL2Core_eq_payload ... :
    (fun q => psiSplitRawL2Core H r hr hL hL2 q - q)
      =
    fun q =>
      let rgΔ := (regGaugeSlotCLE H r hr hL).symm (l2GaugeΔ H r hr hL hL2 q)
      let cΔ  := paramsEquivFlatCLE (deepestM H r) (l2CoreΔTuple H r hr hL hL2 q)
      (rgΔ.1, (cΔ, rgΔ.2)) := by
  funext q
  -- core: rewrite `q.2.1 = paramsEquivFlatCLE _ ((paramsEquivFlatCLE _).symm q.2.1)`,
  -- use `map_sub`, then prove the tuple identity by `funext s; by_cases s = lastLayer hL`.
  -- gauge: rewrite both `regGaugeSlotEquiv.symm` as `regGaugeSlotCLE.symm`,
  -- use linearity `map_sub`, then prove `g' - g = l2GaugeΔ` by `funext idx; rcases idx`.
  ...
```

Add the two symm-coe helper lemmas once:

```lean
private theorem paramsEquivFlatCLE_symm_coe (M : Fin (L + 1) → ℕ) :
    ⇑(paramsEquivFlatCLE M).symm = ⇑(paramsEquivFlat M).symm := by
  funext y
  apply (paramsEquivFlat M).injective
  rw [(paramsEquivFlat M).apply_symm_apply]
  rw [← paramsEquivFlatCLE_coe M, (paramsEquivFlatCLE M).apply_symm_apply]

private theorem regGaugeSlotCLE_symm_coe ... :
    ⇑(regGaugeSlotCLE H r hr hL).symm = ⇑(regGaugeSlotEquiv H r hr hL).symm := by
  funext g
  apply (regGaugeSlotEquiv H r hr hL).injective
  rw [(regGaugeSlotEquiv H r hr hL).apply_symm_apply]
  rw [← regGaugeSlotCLE_coe H r hr hL, (regGaugeSlotCLE H r hr hL).apply_symm_apply]
```

**S2 Smoothness**
Prove smoothness of the two payloads.

For the core payload, after you have:

```lean
hΔT : ContDiffAt ℝ ⊤
  (fun q => l2T1p H r hr hL hL2 q - coreLast H r hL q) q
```

use fixed-zero update:

```lean
have hcoreTuple :
    ContDiffAt ℝ ⊤ (l2CoreΔTuple H r hr hL hL2) q :=
  ((contDiff_update (⊤ : ℕ∞) (0 : Params (deepestM H r)) (lastLayer hL)).contDiffAt).comp q hΔT

have hcore :
    ContDiffAt ℝ ⊤
      (fun q => paramsEquivFlatCLE (deepestM H r)
        (l2CoreΔTuple H r hr hL hL2 q)) q :=
  (paramsEquivFlatCLE (deepestM H r)).contDiff.contDiffAt.comp q hcoreTuple
```

For the gauge payload:

```lean
have hgauge :
    ContDiffAt ℝ ⊤ (l2GaugeΔ H r hr hL hL2) q := by
  refine contDiffAt_pi.mpr ?_
  intro idx
  rcases idx with ⟨s, tag⟩
  rcases tag with tagXY | tagZ
  · rcases tagXY with tagX | tagY
    · simp [l2GaugeΔ]
    · rcases tagY with ⟨i, j⟩
      by_cases h : s = lastLayer hL
      · subst h
        simpa [l2GaugeΔ] using hΔY i j
      · simp [l2GaugeΔ, h]
  · simp [l2GaugeΔ]
```

Then compose with `regGaugeSlotCLE.symm`.

Important flag: the existing `contDiffAt_matrix_inv_entry_of_det_ne_zero` is enough for `A0⁻¹`, `A1⁻¹`, and `P00⁻¹` because those matrices have globally smooth entries. For `W⁻¹`, `W` itself contains `A0⁻¹/A1⁻¹`, so you likely want an at-level variant:

```lean
theorem contDiffAt_matrix_inv_entry_of_det_ne_zero_at
    (hA : ∀ i j, ContDiffAt ℝ ⊤ (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (i j : n) :
    ContDiffAt ℝ ⊤ (fun y => (A y)⁻¹ i j) x := ...
```

Same proof as the landed global-entry lemma, but with `ContDiffAt` determinant/adjugate.

**S4 Strict Derivative**
Do not prove `T1'` has derivative `0`; that is false. Prove:

```lean
HasStrictFDerivAt
  (fun q => l2T1p H r hr hL hL2 q - coreLast H r hL q)
  0 0
```

Best proof shape: show `D T1'(0) = D T1(0)`, then subtract.

Use generic matrix product lemmas:

```lean
-- if A(0)=I and B(0)=0, then D(A*B) entry = D B entry
private theorem hasStrictFDerivAt_matrix_mul_left_id_entry ...

-- if A(0)=0 and B(0)=0, then D(A*B) entry = 0
private theorem hasStrictFDerivAt_matrix_mul_zero_entry ...
```

Then the chain is:

```lean
-- K = Z1 * P00⁻¹ * Y0 has derivative 0
hK0deriv

-- Z1 * A1⁻¹ * Y1 has derivative 0
hZA1Y0deriv

-- S1 = T1 - Z1*A1⁻¹*Y1 has same derivative as T1
hS1deriv

-- (1 - K) * S1 has same derivative as T1
-- because (1-K)(0)=1 and S1(0)=0
hMainDeriv

-- remaining bracket terms have derivative 0
hBracketDerivSameAsT1

-- W⁻¹(0)=1 and bracket(0)=0, so W⁻¹ * bracket has same derivative as bracket
hT1pDerivSameAsT1

exact hT1pDerivSameAsT1.sub hT1
```

For `Y1' - Y1`:

```lean
Y1' - Y1 = A0⁻¹ * Y0 * (T1 - T1')
```

Here `Y0(0)=0` and `(T1 - T1')(0)=0`, so each entry has strict derivative `0` by the matrix-product zero lemma, or by expanding to scalar sums and reusing `hasStrictFDerivAt_triple_mul_zero`.

**Elaborator Idioms**
Use `subst h` immediately after `by_cases h : s = lastLayer hL`; do not leave `h ▸ j` around.

Do not unfold `regGaugeSlotEquiv.symm` under the `match`. Prove `g' - g = l2GaugeΔ` at the `RegGaugeIdx → ℝ` level, then use `regGaugeSlotCLE.symm.map_sub`.

For core updates, either use the fixed-zero payload plus `contDiff_update`, or prove a tiny helper:

```lean
theorem contDiffAt_update₂ [DecidableEq ι]
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => Function.update (f y) i g y) x := by
  refine contDiffAt_pi.mpr ?_
  intro j
  by_cases h : j = i
  · subst h; simpa using hg
  · simpa [Function.update_of_ne h] using (contDiffAt_pi.mp hf j)
```

But for these two leaves, the delta-payload form is cleaner.