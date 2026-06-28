I verified locally that Mathlib v4.29 has the CoV/Tonelli lemma names you cited, and that local `schur_minorPivot_split` has the exact N2b top/bottom shape. I did not find the newer `RmatGnorm`/`zEG`/`stepShearG`/`resolvedShiftRG_le` names in this checkout, so below I treat those signatures as given by your active branch.

**Top Level**

Use these abbreviations:

```lean
let E := zEG r N hN hr p
let zbox := Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)
let Mbox := Set.univ.pi (fun _ : Fin (r-1) × Fin (r-1) => Set.Icc (-1 : ℝ) 1)
let vbox := Set.univ.pi (fun _ : Fin (r-1) ⊕ Fin (r-1) => Set.Icc (-1 : ℝ) 1)
let qbox := Mbox ×ˢ vbox
```

The top skeleton is:

```lean
rw [setLIntegral_congr_fun (by exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  (fun z hz => innerSGen_eq_norm r N hN hr p c' T z)]

have hpre : zbox = E ⁻¹' qbox := by
  -- either your `zEG_box_preimage`, or inline from `zEG_symm_apply`/`zσG` bijectivity.

have H :
    ((Fin (r-1) × Fin (r-1) → ℝ) × ((Fin (r-1) ⊕ Fin (r-1)) → ℝ)) → ℝ≥0∞ :=
  fun q =>
    ∫⁻ S in matBox r 4 T,
      ENNReal.ofReal
        ((frobSq (rmatMul
          (fun a b => RmatGnorm r N hN hr p (E.symm q) a b) S)) ^ (-c'))

rw [hpre]

have hcov :=
  (measurePreserving_zEG r N hN hr p).setLIntegral_comp_preimage_emb
    E.measurableEmbedding H qbox
rw [hcov]

rw [Measure.volume_eq_prod,
    setLIntegral_prod _ hH.aemeasurable,
    lintegral_lintegral_swap hH.aemeasurable]
```

After this, the goal is shaped as

```lean
∫⁻ v in vbox, ∫⁻ M in Mbox, H (M, v) < ⊤
```

where `hH` is the joint measurability of `H`. Usually `fun_prop` should prove it after unfolding `frobSq`, `rmatMul`, and `RmatGnorm` measurability; otherwise isolate it as a helper.

**Per `(M,v)` Chain**

Instantiate N2b once, outside the `M,v,S` work:

```lean
have h1r : 1 ≤ r := le_trans (by norm_num) hr
obtain ⟨c₀, c₁, hc₀, hc₁, hN2b⟩ :=
  schur_minorPivot_split (r := r) (p := 4) 1 h1r
```

For fixed `M ∈ Mbox`, `v ∈ vbox`, set

```lean
let z := E.symm (M, v)
let R : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun a b => RmatGnorm r N hN hr p z a b)
```

The N2b hypotheses are:

```lean
have hz : z ∈ zbox := by
  -- from `hpre` applied to `(M,v) ∈ qbox`, using `E (E.symm (M,v)) = (M,v)`.

have hbd : ∀ a b : Fin r, |R a b| ≤ 1 := by
  intro a b
  simpa [R] using RmatGnorm_offpivot_le r N hN hr p z hz a b

have hpivdet :
    (Matrix.of (fun a b : Fin 1 =>
      R ⟨a, lt_of_lt_of_le a.2 h1r⟩
        ⟨b, lt_of_lt_of_le b.2 h1r⟩)).det = 1 := by
  rw [Matrix.det_fin_one]
  simpa [R] using RmatGnorm_pivot r N hN hr p z

have hpivot : ∀ I J : Fin 1 → Fin r,
    |(R.submatrix I J).det| ≤
      |(Matrix.of (fun a b : Fin 1 =>
        R ⟨a, lt_of_lt_of_le a.2 h1r⟩
          ⟨b, lt_of_lt_of_le b.2 h1r⟩)).det| := by
  intro I J
  rw [Matrix.det_fin_one, hpivdet, abs_one]
  simpa [Matrix.submatrix_apply] using hbd (I 0) (J 0)

have hne :
    (Matrix.of (fun a b : Fin 1 =>
      R ⟨a, lt_of_lt_of_le a.2 h1r⟩
        ⟨b, lt_of_lt_of_le b.2 h1r⟩)).det ≠ 0 := by
  rw [hpivdet]
  norm_num
```

Extract `Sc` once using dummy `S`, then reuse by structural uniqueness:

```lean
obtain ⟨Sc, hSceq, _hdet, _, _⟩ :=
  hN2b R (fun _ _ => 0) hbd hpivot hne

have hbounds : ∀ S : Fin r → Fin 4 → ℝ,
    c₀ * (frobSq (fun a : Fin 1 =>
        rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 h1r⟩)
      + frobSq (rmatMul (fun a b => Sc a b)
          (fun a : Fin (r-1) => S ⟨1 + a, by omega⟩)))
      ≤ frobSq (rmatMul (fun a b => R a b) S := by
  intro S
  obtain ⟨Sc', hSceq', _, hlo, _hup⟩ := hN2b R S hbd hpivot hne
  have : Sc' = Sc := by rw [hSceq', ← hSceq]
  subst this
  simpa using hlo
```

Also keep the upper bound for the zero guard:

```lean
have hbounds₂ : ∀ S, frobSq (rmatMul (fun a b => R a b) S) ≤ c₁ * X S := ...
```

where `X S` is the N2b split expression.

Then apply your rpow helper pointwise:

```lean
have hpt : ∀ S,
    ENNReal.ofReal ((F S) ^ (-c')) ≤
      ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
  intro S
  refine ofReal_rpow_le_const_mul (X S) (F S) c₀ c'
    (by linarith [hc2]) hc₀ (hX_nonneg S) (frobSq_nonneg _)
    (hbounds S) ?_
  intro hX0
  exact le_antisymm (by simpa [hX0] using hbounds₂ S) (frobSq_nonneg _)
```

Pull the constant with:

```lean
lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
```

**The Bridge**

Do not use `Fin.sum_univ_succ` first on the raw N2b term. N2b is indexed by `Fin r`; use the local repo lemma:

```lean
fin_sum_block_split 1 h1r
```

The bridge helper should be:

```lean
have htopRow :
    frobSq (fun a : Fin 1 =>
      rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 h1r⟩)
    =
    ∑ q : Fin 4,
      (S 0 q + ∑ a : Fin (r-1),
        R 0 ⟨1 + a, by omega⟩ * S ⟨1 + a, by omega⟩ q) ^ 2 := by
  unfold frobSq
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  unfold rmatMul
  rw [fin_sum_block_split 1 h1r
    (fun k : Fin r => R 0 k * S k q)]
  have htop :
      (∑ a : Fin 1,
        R 0 ⟨a, lt_of_lt_of_le a.2 h1r⟩ *
          S ⟨a, lt_of_lt_of_le a.2 h1r⟩ q)
      = S 0 q := by
    rw [Fin.sum_univ_one]
    simpa [R, RmatGnorm_pivot r N hN hr p z] -- may need a tiny `Fin.ext`
  rw [htop]
```

Then the `stepShearG` mismatch is real: it wants `S : Fin ((r-1)+1) → Fin 4 → ℝ` and uses `S a.succ`. Your N2b integral has `S : Fin r → Fin 4 → ℝ` and bottom row `S ⟨1+a, by omega⟩`.

You need one of these helpers:

```lean
let er : Fin ((r-1)+1) ≃ Fin r := finCongr (Nat.sub_add_cancel h1r)

-- prove matBox/volume invariance under row reindex by `er`
```

or a wrapper lemma `stepShearG_finCongr` whose statement is exactly the N2b `Fin r` version. Without this, the bricks do not compose definitionally.

For `Sc`, prove or use:

```lean
have hSc_carve :
    Sc = (fun a b => matOfG M a b - bgShiftG (r-1) v a b) := by
  rw [hSceq]
  ext a b
  -- collapse the `Fin 1` products and use `[1]⁻¹ = [1]`
  simp [Matrix.mul_apply, Matrix.det_fin_one,
        RmatGnorm_carve_M22, RmatGnorm_carve_g, RmatGnorm_carve_b,
        RmatGnorm_pivot, bgShiftG, matOfG]
```

If `simp` does not close `[1]⁻¹ = [1]`, isolate:

```lean
have hM11_one :
    Matrix.of (fun a b : Fin 1 =>
      R ⟨a, lt_of_lt_of_le a.2 h1r⟩
        ⟨b, lt_of_lt_of_le b.2 h1r⟩)
    = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simpa [R] using RmatGnorm_pivot r N hN hr p z
```

then `rw [hM11_one]` before simplifying.

**Radius**

Use

```lean
let K : ℝ := max 1 ((r : ℝ) * T)
```

not `T`, and not merely `max 1 T`.

You need enlargements before `resolvedShiftRG_le`:

```lean
have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
have hTleK : T ≤ K := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1r
  exact le_trans (by nlinarith [mul_le_mul_of_nonneg_right hr1 hT.le])
                 (le_max_right 1 ((r : ℝ) * T))

have hrTleK : (r : ℝ) * T ≤ K := le_max_right _ _
```

Then enlarge:

```lean
Mbox radius 1       ⊆ matBox (r-1) (r-1) K
Sbox radius T       ⊆ matBox (r-1) 4 K
Tbox radius r*T     ⊆ morseBox 4 K
```

using nested `lintegral_mono_set`. This enlargement is required because `stepShearG` outputs `morseBox 4 ((m+1)*T)`, i.e. `morseBox 4 (r*T)` after the `m = r-1` cast.

Finally apply:

```lean
have hvabs : ∀ s, |v s| ≤ 1 := ...
have hSh : ∀ i j, |bgShiftG (r-1) v i j| ≤ (1 : ℝ) :=
  bgShiftG_entry_le hvabs

have hres :=
  resolvedShiftRG_le r hr (bgShiftG (r-1) v) 1 hSh K hK c' hc2
```

**Final v-Integration**

The bound is uniform in `v` because `resolvedShiftRG_le` only sees `v` through `B = 1`, and its RHS is

```lean
ENNReal.ofReal (Cresid 4 c') *
  coreSchurGenVal (r-1) (c' - 2) (K + 1)
```

Use:

```lean
have hc''0 : 0 < c' - 2 := sub_pos.mpr hc2
have hc''lam : c' - 2 < schurLambda (r-1) := by
  -- use `schurLambda r = 2*r - 2` and `schurLambda (r-1) = schurLambda r - 2`

have hcore :
    coreSchurGenVal (r-1) (c' - 2) (K + 1) < ⊤ :=
  coreSchurGenVal_lt_top hr hIH (c' - 2) hc''0 hc''lam (K + 1) (by positivity)

have hconst_lt :
    ENNReal.ofReal (c₀ ^ (-c')) *
      (ENNReal.ofReal (Cresid 4 c') *
        coreSchurGenVal (r-1) (c' - 2) (K + 1)) < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcore)
```

Then:

```lean
calc
  ∫⁻ v in vbox, ... ≤ ∫⁻ _v in vbox, CONST := ...
  _ = CONST * volume vbox := by rw [setLIntegral_const]
  _ < ⊤ := ENNReal.mul_lt_top hconst_lt
      ((isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top)
```

Concrete gaps to watch:

1. `Fin r` vs `Fin ((r-1)+1)` for `stepShearG`: needs a row-`finCongr` transport or wrapper lemma.
2. `Sc = matOfG M - bgShiftG v`: needs the `[1]⁻¹ = [1]` pivot-minor simplification in addition to carve readbacks.
3. If `M` is uncurried, resolved needs a general `matOfEquivG` measure-preserving curry step.
4. Radius must be `K = max 1 ((r : ℝ) * T)` with `lintegral_mono_set` enlargements before `resolvedShiftRG_le`.
5. CoV needs an explicit `zEG_box_preimage`; `zEG_symm_apply` alone is not enough unless you inline the box proof.