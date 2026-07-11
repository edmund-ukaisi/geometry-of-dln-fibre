import DLNFibre.DLN.RLCT.Validate.RouteMSJCorner334

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJOnePeel334` — the `(3,3,3,4)` `t=1` ONE-PEEL finiteness

**Thread `genm-onepeel334`, the (□)-core level above `corner334`.** Builds the NEXT level over the
banked fixed-`A₂` corner slice (`RouteMSJCorner334`): the `(3,3,3,4)`, binding-cut `t=1` **one-peel**
finiteness — the corner slice **integrated over the deep data**. Design spec:
`expeditions/2026-06-20-aoyagi-full/threads/genm-vsastruct/onepeel-tonelli-cert.md`.

## What one-peel adds over corner334

`corner334` proved the fixed-slice `∫⁻_{unit box} (u₀²·U₀ + u₁²·U₁)^{−c'}·|u₀|³|u₁|²` finite when the
units `U₀,U₁` are bounded below by a positive constant (the SECTOR where `A₂` has full row rank), and
showed the fixed slice DIVERGES when a unit vanishes (the `A₂`-rank-drop). This module closes the
**joint** integral where the units themselves are integrated over the deep data — the rank-drop tube
`{U_k → 0}` is now RESCUED by codimension, not deferred.

## The unit-as-norm casting and the codim rescue (cert §4–§5)

The deep data enters through the units as **squared norms of deep-linear images** (cert §5): with the
generic (basis) test directions the map `A₂ ↦ (w₁A₂, δw₂A₂, a_piv·v̄A₂)` is a linear iso of the
deep-matrix space, and in those honest coordinates

    U₀ = ‖w₁A₂‖² + δ²‖w₂A₂‖² = ‖X‖²   (X ∈ ℝ^{d₀}, the `(w₁,w₂)`-block),
    U₁ = a_piv²·‖v̄A₂‖²          = ‖Z‖²   (Z ∈ ℝ^{d₁}, the `v̄`-block),

with `X ⊥ Z` on disjoint coordinate blocks — literally the row blocks of `A₂` when the test directions
are coordinate-aligned (e.g. `v̄ = e₃`, `w₁ = e₁`, `w₂ = e₂` for a `3×4` `A₂`: then `U₁` reads row 3,
`U₀` reads rows 1–2). For general generic directions the block decomposition is the same up to an
orthogonal (measure-preserving) rotation of the row space; that final casting from a literal
`A₂`-matrix Lebesgue integral to the `(X,Z)` clean coordinates is the one piece left as follow-on
(§ "what the recursion still needs"). Here the deep integral is posed **in the clean coordinates
`(X,Z)`**, which is the faithful mathematical content of cert §2.

## The mechanism — weighted-AM-GM decoupling (the codimensions ADD, and the rescue is non-binding)

The whole one-peel integral closes at `c' < 7/2` by a SINGLE pointwise weighted AM-GM at the min-cut
weights `w = ((h₀+1)/s, (h₁+1)/s)`, `s = h₀+h₁+2` (`= (4/7, 3/7)` for `(h₀,h₁)=(3,2)`) — the same
weights `corner334`/`Slice334` use, now coupling the `u`-radial variables to the deep-data norms:

    (u₀²‖X‖² + u₁²‖Z‖²)^{−c'} ≤ ‖X‖^{−2w₀c'}·‖Z‖^{−2w₁c'}·|u₀|^{−2w₀c'}·|u₁|^{−2w₁c'}.

Tonelli then FACTORS the joint integral into four independent finite pieces — the two `u`-marginals
`∫₀¹|u_k|^{h_k − 2w_k c'}` (finite ⟺ `c' < s/2 = 7/2`, the BINDING sector-slice endpoint), and the two
deep **Morse** integrals `∫_{box}(∑X_i²)^{−w₀c'}`, `∫_{box}(∑Z_i²)^{−w₁c'}` (the banked
`sumSqND_box_lt_top`, finite ⟺ `w_k c' < d_k/2`). The deep Morse pieces are the **codim rescue**: they
are finite precisely when the vanishing-locus codimensions `d₀,d₁` are large enough (`d_k ≥ h_k+1`), and
in that regime they are NON-binding — the binding threshold stays the `u`-marginal `7/2`. This is
"the complement is a Morse codim-rescue, not a deeper peel" (cert §3), made precise: the rank-drop tube
`{X→0}` (resp. `{Z→0}`) is closed because `∫(∑X²)^{−w₀c'}` converges near the origin, not because the
integrand is bounded there.

S2-FREE: no `monomial_rlct`, no `cited_aoyagi_dln`. This proves box-finiteness of the one-peel integral
at the branch threshold `7/2 = ½·minAdm(3,3,3,4)`; the `rlct = ½·codim` reading stays Cited.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real
open scoped ENNReal BigOperators

/-! ## 1. The corner slice as a function of explicit units, and the bridge to `corner334` -/

/-- **The corner slice at explicit units.** The `corner334` fixed-slice integrand with the deep-data
units `U₀,U₁` supplied as explicit reals (constant in the radial variables) and general accumulated
Jacobian powers `h₀,h₁`. For `(h₀,h₁)=(3,2)` and `U_k = cornerUnit_k A₂` this is definitionally the
banked `cornerSlice334Integral` (`cornerSlice334Integral_eq_atUnits`). -/
noncomputable def cornerSliceAtUnits (h0 h1 : ℕ) (U0 U1 : ℝ) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in unitBox 2,
    ENNReal.ofReal ((u 0 ^ 2 * U0 + u 1 ^ 2 * U1) ^ (-c') * (|u 0| ^ h0 * |u 1| ^ h1))

/-- **Bridge to the banked `corner334` slice.** The `corner334` fixed-`A₂` slice integral is exactly
`cornerSliceAtUnits` at Jacobian powers `(3,2)` and the concrete deep-data units. -/
theorem cornerSlice334Integral_eq_atUnits {q : ℕ} (A₂ : Matrix (Fin 2) (Fin q) ℝ)
    (w₁ w₂ vbar : Fin 2 → ℝ) (δ apiv : ℝ) (c' : NNReal) :
    cornerSlice334Integral A₂ w₁ w₂ vbar δ apiv c'
      = cornerSliceAtUnits 3 2 (cornerUnit0 A₂ w₁ w₂ δ) (cornerUnit1 A₂ vbar apiv) (c' : ℝ) :=
  rfl

/-! ## 2. The weighted-AM-GM slice bound (the codim-decoupling) -/

/-- **The weighted-AM-GM slice bound (the codim-decoupling).** For strictly positive units `A = ‖X‖²`,
`B = ‖Z‖²` and any weights `w₀,w₁ ∈ [0,1]` summing to `1`, the corner slice is dominated by a product
of a deep-norm power in each block and a `u`-only monomial integral. The domination is the pointwise
weighted AM-GM `(u₀²A+u₁²B)^{−c'} ≤ (u₀²A)^{−w₀c'}(u₁²B)^{−w₁c'}` (a.e. on the open box); the deep
powers `A^{−w₀c'},B^{−w₁c'}` factor out as constants (constant in `u`), leaving the separated
`u`-monomial integral. This is the pointwise engine of the one-peel factoring: the deep powers are
later integrated (the codim rescue), while the `u`-monomial carries the binding `7/2` threshold. -/
theorem cornerSliceAtUnits_le (h0 h1 : ℕ) (c' : ℝ) (hc0 : 0 ≤ c')
    (w0 w1 : ℝ) (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw0le : w0 ≤ 1) (hw1le : w1 ≤ 1)
    (hwsum : w0 + w1 = 1) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    cornerSliceAtUnits h0 h1 A B c'
      ≤ ENNReal.ofReal (A ^ (-(w0 * c'))) * ENNReal.ofReal (B ^ (-(w1 * c')))
        * ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
            ENNReal.ofReal (|u 0| ^ ((h0 : ℝ) - 2 * w0 * c')
              * |u 1| ^ ((h1 : ℝ) - 2 * w1 * c')) := by
  unfold cornerSliceAtUnits
  rw [restrict_unitBox_eq_open 2]
  set e0 : ℝ := (h0 : ℝ) - 2 * w0 * c' with he0_def
  set e1 : ℝ := (h1 : ℝ) - 2 * w1 * c' with he1_def
  -- pointwise domination on the open box (all `u_k > 0`)
  have hbound : (fun u : Fin 2 → ℝ =>
        ENNReal.ofReal ((u 0 ^ 2 * A + u 1 ^ 2 * B) ^ (-c') * (|u 0| ^ h0 * |u 1| ^ h1)))
      ≤ᵐ[volume.restrict (Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1))]
      (fun u : Fin 2 → ℝ =>
        ENNReal.ofReal (A ^ (-(w0 * c')) * B ^ (-(w1 * c')))
          * ENNReal.ofReal (|u 0| ^ e0 * |u 1| ^ e1)) := by
    refine ae_restrict_of_forall_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)) ?_
    intro u hu
    dsimp only
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hu
    have hx : 0 < u 0 := (hu 0).1
    have hy : 0 < u 1 := (hu 1).1
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A ^ (-(w0 * c')) * B ^ (-(w1 * c')))]
    apply ENNReal.ofReal_le_ofReal
    set X : ℝ := |u 0| with hX_def
    set Y : ℝ := |u 1| with hY_def
    have hXpos : 0 < X := by rw [hX_def]; exact abs_pos.mpr (ne_of_gt hx)
    have hYpos : 0 < Y := by rw [hY_def]; exact abs_pos.mpr (ne_of_gt hy)
    have hsqX : u 0 ^ 2 = X ^ 2 := by rw [hX_def, sq_abs]
    have hsqY : u 1 ^ 2 = Y ^ 2 := by rw [hY_def, sq_abs]
    rw [hsqX, hsqY]
    -- weighted AM-GM: `(X²A)^{w₀}(Y²B)^{w₁} ≤ X²A + Y²B`
    have hp1 : (0 : ℝ) ≤ X ^ 2 * A := by positivity
    have hp2 : (0 : ℝ) ≤ Y ^ 2 * B := by positivity
    have hgm := Real.geom_mean_le_arith_mean2_weighted hw0 hw1 hp1 hp2 hwsum
    have hle2 : w0 * (X ^ 2 * A) + w1 * (Y ^ 2 * B) ≤ X ^ 2 * A + Y ^ 2 * B := by
      have ha := mul_le_of_le_one_left hp1 hw0le
      have hb := mul_le_of_le_one_left hp2 hw1le
      linarith
    have hbase_le : (X ^ 2 * A) ^ w0 * (Y ^ 2 * B) ^ w1 ≤ X ^ 2 * A + Y ^ 2 * B :=
      le_trans hgm hle2
    have hbase_pos : 0 < (X ^ 2 * A) ^ w0 * (Y ^ 2 * B) ^ w1 := by positivity
    have hrp : (X ^ 2 * A + Y ^ 2 * B) ^ (-c') ≤ ((X ^ 2 * A) ^ w0 * (Y ^ 2 * B) ^ w1) ^ (-c') :=
      Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by linarith)
    -- expand the dominating power × the Jacobian into the separated form (split forms below keep
    -- each `rw` chain small enough to avoid a `whnf` heartbeat blowup)
    have hbase_eq : (X ^ 2 * A) ^ w0 * (Y ^ 2 * B) ^ w1
        = (A ^ w0 * B ^ w1) * (X ^ (2 * w0) * Y ^ (2 * w1)) := by
      rw [Real.mul_rpow (sq_nonneg X) hA.le, Real.mul_rpow (sq_nonneg Y) hB.le,
        ← Real.rpow_natCast X 2, ← Real.rpow_mul hXpos.le,
        ← Real.rpow_natCast Y 2, ← Real.rpow_mul hYpos.le,
        show ((2 : ℕ) : ℝ) * w0 = 2 * w0 from by push_cast; ring,
        show ((2 : ℕ) : ℝ) * w1 = 2 * w1 from by push_cast; ring]
      ring
    have hAB : (A ^ w0 * B ^ w1) ^ (-c') = A ^ (-(w0 * c')) * B ^ (-(w1 * c')) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA.le w0) (Real.rpow_nonneg hB.le w1),
        ← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le, mul_neg, mul_neg]
    have hXY : (X ^ (2 * w0) * Y ^ (2 * w1)) ^ (-c') * (X ^ h0 * Y ^ h1) = X ^ e0 * Y ^ e1 := by
      rw [Real.mul_rpow (Real.rpow_nonneg hXpos.le (2 * w0)) (Real.rpow_nonneg hYpos.le (2 * w1)),
        ← Real.rpow_mul hXpos.le, ← Real.rpow_mul hYpos.le,
        ← Real.rpow_natCast X h0, ← Real.rpow_natCast Y h1,
        show X ^ (2 * w0 * -c') * Y ^ (2 * w1 * -c') * (X ^ ((h0 : ℕ) : ℝ) * Y ^ ((h1 : ℕ) : ℝ))
            = (X ^ (2 * w0 * -c') * X ^ ((h0 : ℕ) : ℝ))
                * (Y ^ (2 * w1 * -c') * Y ^ ((h1 : ℕ) : ℝ)) from by ring,
        ← Real.rpow_add hXpos, ← Real.rpow_add hYpos,
        show 2 * w0 * -c' + ((h0 : ℕ) : ℝ) = e0 from by rw [he0_def]; ring,
        show 2 * w1 * -c' + ((h1 : ℕ) : ℝ) = e1 from by rw [he1_def]; ring]
    have hexp : ((X ^ 2 * A) ^ w0 * (Y ^ 2 * B) ^ w1) ^ (-c') * (X ^ h0 * Y ^ h1)
        = A ^ (-(w0 * c')) * B ^ (-(w1 * c')) * (X ^ e0 * Y ^ e1) := by
      rw [hbase_eq, Real.mul_rpow (by positivity) (by positivity), mul_assoc, hAB, hXY]
    calc (X ^ 2 * A + Y ^ 2 * B) ^ (-c') * (X ^ h0 * Y ^ h1)
        ≤ ((X ^ 2 * A) ^ w0 * (Y ^ 2 * B) ^ w1) ^ (-c') * (X ^ h0 * Y ^ h1) :=
          mul_le_mul_of_nonneg_right hrp (by positivity)
      _ = A ^ (-(w0 * c')) * B ^ (-(w1 * c')) * (X ^ e0 * Y ^ e1) := hexp
  calc ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal ((u 0 ^ 2 * A + u 1 ^ 2 * B) ^ (-c') * (|u 0| ^ h0 * |u 1| ^ h1))
      ≤ ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
          ENNReal.ofReal (A ^ (-(w0 * c')) * B ^ (-(w1 * c')))
            * ENNReal.ofReal (|u 0| ^ e0 * |u 1| ^ e1) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal (A ^ (-(w0 * c')) * B ^ (-(w1 * c')))
          * ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
            ENNReal.ofReal (|u 0| ^ e0 * |u 1| ^ e1) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (A ^ (-(w0 * c'))) * ENNReal.ofReal (B ^ (-(w1 * c')))
          * ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
            ENNReal.ofReal (|u 0| ^ e0 * |u 1| ^ e1) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ A ^ (-(w0 * c')))]

/-! ## 3. The one-peel integral and its finiteness -/

/-- **The `(3,3,3,4)`-shape one-peel integral** (deep data in the clean `(X,Z)` coordinates). The
corner slice `cornerSliceAtUnits` with the two units cast as squared Euclidean norms `U₀ = ∑X_i²`
(`X ∈ [−T,T]^{d₀}`, `d₀ = m₀+1`) and `U₁ = ∑Z_i²` (`Z ∈ [−T,T]^{d₁}`, `d₁ = m₁+1`), integrated over
the deep boxes. This is the corner slice integrated over the deep data (cert §1); the blocks `X ⊥ Z`
are the honest deep coordinates of the generic-directions casting (module docstring). -/
noncomputable def onePeelIntegral (h0 h1 m0 m1 : ℕ) (T c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ X in morseBox (m0 + 1) T, ∫⁻ Z in morseBox (m1 + 1) T,
    cornerSliceAtUnits h0 h1 (∑ i, X i ^ 2) (∑ i, Z i ^ 2) c'

set_option maxHeartbeats 800000 in
-- reason: the nested-`lintegral` Tonelli factoring (two `lintegral_mono_ae` + `lintegral_const_mul'`
-- steps over the deep boxes, with the `set` Morse / `u`-monomial atoms) drives the elaboration defeq
-- cost above the default heartbeat budget; the proof is otherwise linear.
/-- **The one-peel finiteness (width-general).** The one-peel integral is finite for every
`c' < (h₀+h₁+2)/2` as soon as the vanishing-locus codimensions are full enough — `h₀ ≤ m₀` and
`h₁ ≤ m₁` (i.e. `d_k = m_k+1 ≥ h_k+1`). The binding threshold `(h₀+h₁+2)/2` comes from the two
`u`-marginals; the deep Morse integrals (the codim rescue) are non-binding under the codim hypotheses.
Proof: pointwise weighted AM-GM at the min-cut weights (`cornerSliceAtUnits_le`) + Tonelli factoring
into the two deep Morse integrals (`sumSqND_box_lt_top`) and the `u`-monomial box integral
(`prod_rpow_lintegral_Ioo_box_lt_top`). -/
theorem onePeelIntegral_lt_top (h0 h1 m0 m1 : ℕ) (hm0 : h0 ≤ m0) (hm1 : h1 ≤ m1)
    (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < ((h0 : ℝ) + (h1 : ℝ) + 2) / 2) :
    onePeelIntegral h0 h1 m0 m1 T c' < ⊤ := by
  -- min-cut weights
  set s : ℝ := (h0 : ℝ) + (h1 : ℝ) + 2 with hs_def
  have hs : 0 < s := by rw [hs_def]; positivity
  set w0 : ℝ := ((h0 : ℝ) + 1) / s with hw0_def
  set w1 : ℝ := ((h1 : ℝ) + 1) / s with hw1_def
  have hw0pos : 0 < w0 := by rw [hw0_def]; positivity
  have hw1pos : 0 < w1 := by rw [hw1_def]; positivity
  have hwsum : w0 + w1 = 1 := by rw [hw0_def, hw1_def]; field_simp; rw [hs_def]; ring
  have hw0le : w0 ≤ 1 := by
    rw [hw0_def, div_le_one hs, hs_def]; linarith [(Nat.cast_nonneg h1 : (0 : ℝ) ≤ (h1 : ℝ))]
  have hw1le : w1 ≤ 1 := by
    rw [hw1_def, div_le_one hs, hs_def]; linarith [(Nat.cast_nonneg h0 : (0 : ℝ) ≤ (h0 : ℝ))]
  -- the axis-exponent bounds `2·w_k·c' < h_k+1` (⟺ `c' < s/2`)
  have h2ccs : 2 * c' < s := by rw [hs_def]; linarith [hc']
  have hw0s : w0 * s = (h0 : ℝ) + 1 := by rw [hw0_def]; field_simp
  have hw1s : w1 * s = (h1 : ℝ) + 1 := by rw [hw1_def]; field_simp
  have hw0lt : 2 * w0 * c' < (h0 : ℝ) + 1 := by
    have hstep : w0 * (2 * c') < w0 * s := mul_lt_mul_of_pos_left h2ccs hw0pos
    rw [hw0s] at hstep; nlinarith [hstep]
  have hw1lt : 2 * w1 * c' < (h1 : ℝ) + 1 := by
    have hstep : w1 * (2 * c') < w1 * s := mul_lt_mul_of_pos_left h2ccs hw1pos
    rw [hw1s] at hstep; nlinarith [hstep]
  -- the deep-Morse (codim-rescue) thresholds `w_k·c' < (m_k+1)/2`
  have hw0m : w0 * c' < ((m0 : ℝ) + 1) / 2 := by
    have : (h0 : ℝ) + 1 ≤ (m0 : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hm0 1
    nlinarith [hw0lt, this]
  have hw1m : w1 * c' < ((m1 : ℝ) + 1) / 2 := by
    have : (h1 : ℝ) + 1 ≤ (m1 : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hm1 1
    nlinarith [hw1lt, this]
  -- the three finite factors
  set e0 : ℝ := (h0 : ℝ) - 2 * w0 * c' with he0_def
  set e1 : ℝ := (h1 : ℝ) - 2 * w1 * c' with he1_def
  have he0 : (-1 : ℝ) < e0 := by rw [he0_def]; linarith [hw0lt]
  have he1 : (-1 : ℝ) < e1 := by rw [he1_def]; linarith [hw1lt]
  set Ix : ℝ≥0∞ := ∫⁻ X in morseBox (m0 + 1) T, ENNReal.ofReal ((∑ i, X i ^ 2) ^ (-(w0 * c')))
    with hIx_def
  set Iz : ℝ≥0∞ := ∫⁻ Z in morseBox (m1 + 1) T, ENNReal.ofReal ((∑ i, Z i ^ 2) ^ (-(w1 * c')))
    with hIz_def
  set Iu : ℝ≥0∞ := ∫⁻ u in Set.univ.pi (fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1),
      ENNReal.ofReal (|u 0| ^ e0 * |u 1| ^ e1) with hIu_def
  have hIx : Ix < ⊤ := by rw [hIx_def]; exact sumSqND_box_lt_top m0 T hT (w0 * c') hw0m
  have hIz : Iz < ⊤ := by rw [hIz_def]; exact sumSqND_box_lt_top m1 T hT (w1 * c') hw1m
  have hIu : Iu < ⊤ := by
    rw [hIu_def]
    have hvec : ∀ j : Fin 2, (-1 : ℝ) < (![e0, e1] : Fin 2 → ℝ) j := by
      rw [Fin.forall_fin_two]
      exact ⟨by simpa using he0, by simpa using he1⟩
    have h := prod_rpow_lintegral_Ioo_box_lt_top (d := 2) 1 one_pos ![e0, e1] hvec
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h
  -- inner bound (for A > 0)
  have hinner : ∀ A : ℝ, 0 < A →
      (∫⁻ Z in morseBox (m1 + 1) T, cornerSliceAtUnits h0 h1 A (∑ i, Z i ^ 2) c')
        ≤ ENNReal.ofReal (A ^ (-(w0 * c'))) * (Iu * Iz) := by
    intro A hA
    -- a.e.-Z domination via `cornerSliceAtUnits_le`
    have hZbound : (fun Z : Fin (m1 + 1) → ℝ => cornerSliceAtUnits h0 h1 A (∑ i, Z i ^ 2) c')
        ≤ᵐ[volume.restrict (morseBox (m1 + 1) T)]
        (fun Z : Fin (m1 + 1) → ℝ =>
          (ENNReal.ofReal (A ^ (-(w0 * c'))) * Iu)
            * ENNReal.ofReal ((∑ i, Z i ^ 2) ^ (-(w1 * c')))) := by
      have hae : ∀ᵐ Z : Fin (m1 + 1) → ℝ, (∑ i, Z i ^ 2) ≠ 0 := by
        rw [ae_iff]
        have hsub : {Z : Fin (m1 + 1) → ℝ | ¬ (∑ i, Z i ^ 2) ≠ 0} ⊆ {(0 : Fin (m1 + 1) → ℝ)} := by
          intro Z hZ
          simp only [Set.mem_setOf_eq, not_not] at hZ
          have hall : ∀ i, Z i ^ 2 = 0 :=
            fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hZ i
              (Finset.mem_univ i)
          simp only [Set.mem_singleton_iff]
          funext i; exact pow_eq_zero_iff (by norm_num) |>.1 (hall i)
        exact measure_mono_null hsub (measure_singleton _)
      refine (ae_restrict_of_ae hae).mono (fun Z hZ => ?_)
      have hBpos : 0 < ∑ i, Z i ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hZ)
      have hle := cornerSliceAtUnits_le h0 h1 c' hc0 w0 w1 hw0pos.le hw1pos.le hw0le hw1le hwsum
        A (∑ i, Z i ^ 2) hA hBpos
      calc cornerSliceAtUnits h0 h1 A (∑ i, Z i ^ 2) c'
          ≤ ENNReal.ofReal (A ^ (-(w0 * c'))) * ENNReal.ofReal ((∑ i, Z i ^ 2) ^ (-(w1 * c')))
              * Iu := hle
        _ = (ENNReal.ofReal (A ^ (-(w0 * c'))) * Iu)
              * ENNReal.ofReal ((∑ i, Z i ^ 2) ^ (-(w1 * c'))) := mul_right_comm _ _ _
    calc (∫⁻ Z in morseBox (m1 + 1) T, cornerSliceAtUnits h0 h1 A (∑ i, Z i ^ 2) c')
        ≤ ∫⁻ Z in morseBox (m1 + 1) T,
            (ENNReal.ofReal (A ^ (-(w0 * c'))) * Iu)
              * ENNReal.ofReal ((∑ i, Z i ^ 2) ^ (-(w1 * c'))) := lintegral_mono_ae hZbound
      _ = (ENNReal.ofReal (A ^ (-(w0 * c'))) * Iu) * Iz := by
          rw [lintegral_const_mul' _ _ (by
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIu.ne), hIz_def]
      _ = ENNReal.ofReal (A ^ (-(w0 * c'))) * (Iu * Iz) := mul_assoc _ _ _
  -- outer bound
  have hOuter : (fun X : Fin (m0 + 1) → ℝ =>
        ∫⁻ Z in morseBox (m1 + 1) T, cornerSliceAtUnits h0 h1 (∑ i, X i ^ 2) (∑ i, Z i ^ 2) c')
      ≤ᵐ[volume.restrict (morseBox (m0 + 1) T)]
      (fun X : Fin (m0 + 1) → ℝ =>
        (Iu * Iz) * ENNReal.ofReal ((∑ i, X i ^ 2) ^ (-(w0 * c')))) := by
    have hae : ∀ᵐ X : Fin (m0 + 1) → ℝ, (∑ i, X i ^ 2) ≠ 0 := by
      rw [ae_iff]
      have hsub : {X : Fin (m0 + 1) → ℝ | ¬ (∑ i, X i ^ 2) ≠ 0} ⊆ {(0 : Fin (m0 + 1) → ℝ)} := by
        intro X hX
        simp only [Set.mem_setOf_eq, not_not] at hX
        have hall : ∀ i, X i ^ 2 = 0 :=
          fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hX i
            (Finset.mem_univ i)
        simp only [Set.mem_singleton_iff]
        funext i; exact pow_eq_zero_iff (by norm_num) |>.1 (hall i)
      exact measure_mono_null hsub (measure_singleton _)
    refine (ae_restrict_of_ae hae).mono (fun X hX => ?_)
    have hApos : 0 < ∑ i, X i ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hX)
    calc (∫⁻ Z in morseBox (m1 + 1) T, cornerSliceAtUnits h0 h1 (∑ i, X i ^ 2) (∑ i, Z i ^ 2) c')
        ≤ ENNReal.ofReal ((∑ i, X i ^ 2) ^ (-(w0 * c'))) * (Iu * Iz) := hinner _ hApos
      _ = (Iu * Iz) * ENNReal.ofReal ((∑ i, X i ^ 2) ^ (-(w0 * c'))) := mul_comm _ _
  calc onePeelIntegral h0 h1 m0 m1 T c'
      = ∫⁻ X in morseBox (m0 + 1) T,
          ∫⁻ Z in morseBox (m1 + 1) T, cornerSliceAtUnits h0 h1 (∑ i, X i ^ 2) (∑ i, Z i ^ 2) c' :=
        rfl
    _ ≤ ∫⁻ X in morseBox (m0 + 1) T,
          (Iu * Iz) * ENNReal.ofReal ((∑ i, X i ^ 2) ^ (-(w0 * c'))) := lintegral_mono_ae hOuter
    _ = (Iu * Iz) * Ix := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hIu.ne hIz.ne), hIx_def]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hIu hIz) hIx

/-- **The `(3,3,3,4)` `t=1` one-peel finiteness at the branch threshold `7/2`.** With the accumulated
Jacobian powers `(h₀,h₁) = (3,2)` and the honest vanishing-locus codimensions `d₀ = 8` (`m₀ = 7`,
the `(w₁,w₂)`-block), `d₁ = 4` (`m₁ = 3`, the `v̄`-block), the one-peel integral is finite for every
`c' < 7/2 = ½·minAdm(3,3,3,4)`. Both codim conditions `h_k ≤ m_k` (`3 ≤ 7`, `2 ≤ 3`) hold with room:
the codim rescue is non-binding, the binding is the sector-slice endpoint `7/2`. -/
theorem onePeel334_cleanCoords_lt_top (T : ℝ) (hT : 0 < T) (c' : ℝ) (hc0 : 0 ≤ c')
    (hc' : c' < 7 / 2) :
    onePeelIntegral 3 2 7 3 T c' < ⊤ :=
  onePeelIntegral_lt_top 3 2 7 3 (by norm_num) (by norm_num) T hT c' hc0 (by norm_num; linarith)

/-! ## 4. Non-vacuity -/

/-- **Non-vacuity witness.** The `(3,3,3,4)` one-peel integral over the deep boxes at half-width
`T = 1` is finite for `c' = 3` (`< 7/2`) — the hypotheses are jointly satisfiable and the finiteness
is not vacuously true. -/
example : onePeelIntegral 3 2 7 3 1 3 < ⊤ :=
  onePeel334_cleanCoords_lt_top 1 (by norm_num) 3 (by norm_num) (by norm_num)

/-- **The threshold `7/2` IS `½·minAdm(3,3,3,4)`** (re-exposed from `RouteMSJSlice334`), so the
one-peel finiteness reads at the honest "branch threshold = ½·minAdm" precision. -/
theorem onePeel334_threshold_eq_half_minAdm :
    (7 : ℝ) / 2 = (minAdm (![3, 3, 3, 4] : Fin 4 → ℕ) : ℝ) / 2 := by
  rw [sjSlice334_minAdm_eq]; norm_num

end DLNFibre.DLN.RLCT
