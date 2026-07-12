import DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBPos

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorBorderline` — the off-sector BORDERLINE θ-interpolation

**Thread `genm-sj5-domination` off-sector, borderline of Obligations 1 & 2.** The convergent
corank-integrability lemmas (`corankOffSector_b1_le` for `b=1`, `corankOffSector_bpos_le` for `b>1`)
EXCLUDE their borderline cut: `a = M₂` for `b=1`, `a = M₂ − b + 1` for `b>1`. At the borderline the
convergent corank weight `∫_{matBox b M₂ 1} det((A·Z)(A·Z)ᵀ)^{−a/2}` LOG-diverges (`a = M₂ − b + 1`
sits exactly on the integrability boundary of `det^{−s/2}`, which needs `s < M₂ − b + 1`). This module
closes the borderline via the **θ-interpolation** of the two banked bricks.

## The mechanism (`offsector-il-design-cert.md` §2a/§2b; `codex/obl2-scoping-answer.md` Q5, decorrelated-concurred)

On the full-row-rank set (a.e. via `corank_survival_ae`) the freed-corner inner integral `F A` admits
TWO banked pointwise upper bounds:

* **ATOM** (`corankBlock_morsePeel_setLE`, `Apiv := 0`, core `≥ w`): `F A ≤ det((A·Z)(A·Z)ᵀ)^{−a/2} ·
  Cresid(ab) · w^{−(c'−ab/2)}`. Its weight `∫ det^{−a/2}` DIVERGES at the borderline.
* **BOUNDED** (`corankBlock_boundedGen_le`): `F A ≤ w^{−c'} · vol(sΓ)`. Flat in `A`.

Since `F A ≥ 0` lies below BOTH, it lies below any weighted geometric mean
`F A ≤ (ATOM)^θ · (BOUNDED)^{1−θ}` (`enn_geom_interp`), which equals
`det^{−θa/2} · [Cresid(ab)^θ · vol(sΓ)^{1−θ}] · w^{−(c'−θab/2)}` (`borderline_real_identity`). Integrating
over the free corank block, the θ-scaled weight `∫_{matBox b M₂ 1} det^{−θa/2}` is FINITE for
`θ·a < M₂ − b + 1` (`corankWeight_bpos_lt_top` at `s = θ·a`) — at the borderline `a = M₂ − b + 1` this is
exactly `θ < 1`. So for every `θ < 1` the bound is LOG-FREE with a finite `w`-independent constant,
carrying the reduced `w`-charge `c' − θab/2`.

**Landing below `carrierThreshold`.** The strict margin `c' < carrierThreshold(M) = ½·minAdm(M) =
½(ab + minAdm(redChain))` gives, downstream, slack to pick `θ < 1` close enough to `1` that
`c' − θab/2 < ½·minAdm(redChain) = carrierThreshold(redChain)` (the reduced IH's threshold): indeed
`c' − ab/2 < ½·minAdm(redChain)` already (binding identity), so any `θ ∈ ((2c'−minAdm(redChain))/ab, 1)`
works and this interval is nonempty. The weight `θ` and the threshold comparison are the downstream
consumer's (it knows `minAdm(redChain)`); this module supplies the log-free bound with the exposed
reduced charge `θab/2`.

S2-FREE: the two banked bricks + the real-exponent corank weight (`corankWeight_bpos_lt_top`) +
`corank_survival_ae` + `enn_geom_interp` (pure `ℝ≥0∞` rpow). No `monomial_rlct`. Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The `ℝ≥0∞` weighted-geometric-mean interpolation of two upper bounds -/

/-- **Geometric interpolation of two `ℝ≥0∞` upper bounds.** If `x ≤ A` and `x ≤ B` and `θ ∈ [0,1]`,
then `x ≤ A^θ · B^{1−θ}`. Proof: `x = x^θ · x^{1−θ}` (`ENNReal.rpow_add_of_nonneg`, valid for all `x`
including `0`, `⊤` since both exponents are nonneg), then monotonicity of `·^θ`, `·^{1−θ}`. The
convexity that lets the borderline back off the divergent atom weight to any `θ < 1`. -/
theorem enn_geom_interp {x A B : ℝ≥0∞} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hxA : x ≤ A) (hxB : x ≤ B) : x ≤ A ^ θ * B ^ (1 - θ) := by
  have h1θ : (0 : ℝ) ≤ 1 - θ := by linarith
  calc x = x ^ (1 : ℝ) := (ENNReal.rpow_one x).symm
    _ = x ^ (θ + (1 - θ)) := by congr 1; ring
    _ = x ^ θ * x ^ (1 - θ) := ENNReal.rpow_add_of_nonneg θ (1 - θ) hθ0 h1θ
    _ ≤ A ^ θ * B ^ (1 - θ) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hxA hθ0) (ENNReal.rpow_le_rpow hxB h1θ)

/-! ## The real θ-interpolation identity (the exponent bookkeeping, `ℝ`-only) -/

/-- **The real θ-interpolation identity.** The geometric mean of the atom value
`d^{−a/2}·(Cr·w^{−(c'−ab/2)})` (charge `ab/2` on `w`) and the bounded value's `w^{−c'}` (charge `c'`),
with weights `θ` / `1−θ`, collapses to `d^{−θa/2}·(Cr^θ·w^{−(c'−θab/2)})`: the `det` exponent scales by
`θ`, and the `w`-charge interpolates to `c' − θab/2`. Pure `ℝ` rpow bookkeeping (`d, w, Cr ≥ 0`,
`w > 0`); the exponent arithmetic is `ring`. -/
theorem borderline_real_identity {d w Cr θ c' : ℝ} (hd0 : 0 ≤ d) (hw : 0 < w) (hCr : 0 ≤ Cr)
    (a b : ℕ) :
    (d ^ (-(a : ℝ) / 2) * (Cr * w ^ (-(c' - (a * b : ℝ) / 2)))) ^ θ * (w ^ (-c')) ^ (1 - θ)
      = d ^ (-(θ * (a : ℝ)) / 2) * (Cr ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2))) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hd0 _) (mul_nonneg hCr (Real.rpow_nonneg hw.le _)),
      Real.mul_rpow hCr (Real.rpow_nonneg hw.le _),
      ← Real.rpow_mul hd0, ← Real.rpow_mul hw.le, ← Real.rpow_mul hw.le,
      mul_assoc, mul_assoc, ← Real.rpow_add hw]
  rw [show (-(a : ℝ) / 2) * θ = -(θ * (a : ℝ)) / 2 from by ring,
      show (-(c' - (a * b : ℝ) / 2)) * θ + (-c') * (1 - θ) = -(c' - θ * (a * b : ℝ) / 2) from by ring]

/-! ## The general-`b` bounded corank atom (the flat brick) -/

/-- **The general-`b` bounded corank atom.** Over any domain `s`, dropping the nonneg corank term, the
freed `Γ`-integral is bounded by the constant `w^{−c'}` times `volume s`: the core `w` lower-bounds the
integrand and `−c' ≤ 0` makes it `≤ w^{−c'}`. The `Fin b` generalisation of `corankBlock_bounded_le`
(the `b=1` version); the flat brick the θ-interpolation combines with the atom. -/
theorem corankBlock_boundedGen_le {a b n : ℕ} (Ccross : Matrix (Fin a) (Fin n) ℝ)
    (Qb : Matrix (Fin b) (Fin n) ℝ) (c' : ℝ) (hc0 : 0 ≤ c') (w : ℝ) (hw : 0 < w)
    (s : Set (Fin a → Fin b → ℝ)) :
    ∫⁻ Γ in s, ENNReal.ofReal ((w + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      ≤ ENNReal.ofReal (w ^ (-c')) * volume s := by
  have hle : ∀ Γ : Fin a → Fin b → ℝ, w ≤ w + frobSq (Ccross + (Matrix.of Γ) * Qb) :=
    fun Γ => le_add_of_nonneg_right (frobSq_nonneg _)
  calc ∫⁻ Γ in s, ENNReal.ofReal ((w + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      ≤ ∫⁻ _Γ in s, ENNReal.ofReal (w ^ (-c')) := by
        refine lintegral_mono (fun Γ => ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_nonpos hw (hle Γ) (neg_nonpos.mpr hc0)
    _ = ENNReal.ofReal (w ^ (-c')) * volume s := setLIntegral_const s _

/-! ## The borderline θ-interpolation bound (general `b`) -/

/-- **The off-sector borderline θ-interpolation bound (general `b`).** For a corank block of `b` rows,
a fixed pivot energy `w > 0`, cross-shift `Ccross`, the deeper product `Z` on the full-rank tail chart
(`Z.rank = M₂`, `b ≤ M₂`), `c'` above the block Morse threshold `ab/2`, an interpolation weight
`θ ∈ [0,1)` with the θ-scaled weight integrable (`θ·a < M₂ − b + 1`), and a finite-measure freed-corner
domain `sΓ`, the corank-block integral is bounded by a finite, `w`-independent constant times the
θ-reduced power of `w`:

    ∫_{A_cor} [ ∫_{Γ∈sΓ} (w + frobSq (Ccross + Γ·(A_cor·Z)))^{−c'} ] dA_cor  ≤  C₁ · w^{−(c'−θ·ab/2)}.

This covers BOTH borderlines (`b=1, a=M₂` and `b>1, a=M₂−b+1`), where the convergent (`θ=1`) weight
`∫ det^{−a/2}` log-diverges: at the borderline `θ·a < M₂ − b + 1 ⟺ θ < 1`, so any `θ < 1` gives a
log-free bound. On the a.e. full-row-rank set the atom (`corankBlock_morsePeel_setLE`, core `≥ w`) and
the bounded brick (`corankBlock_boundedGen_le`) both bound the inner integral; `enn_geom_interp` takes
their geometric mean (`borderline_real_identity` collapses the powers), the θ-scaled corank weight is
finite (`corankWeight_bpos_lt_top` at `s = θ·a`), and the rank-drop locus is null (`corank_survival_ae`). -/
theorem corankOffSector_borderline_le {a b M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (w c' θ : ℝ)
    (hw : 0 < w) (hbM : b ≤ M₂) (hZrank : Z.rank = M₂) (hc' : (a * b : ℝ) / 2 < c')
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hθa : θ * (a : ℝ) < (M₂ : ℝ) - b + 1)
    (sΓ : Set (Fin a → Fin b → ℝ)) (hsΓ : volume sΓ < ⊤) :
    ∃ C₁ : ℝ≥0∞, C₁ < ⊤ ∧
      ∫⁻ A_cor in matBox b M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ C₁ * ENNReal.ofReal (w ^ (-(c' - θ * (a * b : ℝ) / 2))) := by
  classical
  have hc0 : (0 : ℝ) ≤ c' := le_of_lt (lt_of_le_of_lt (by positivity) hc')
  have h1θ : (0 : ℝ) ≤ 1 - θ := by linarith
  -- the inner freed-corner integral as a function of the corank block `A_cor`
  set F : (Fin b → Fin M₂ → ℝ) → ℝ≥0∞ := fun A =>
    ∫⁻ Γ in sΓ, ENNReal.ofReal
      ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) with hFdef
  -- the θ-scaled corank weight (finite: `θ·a < M₂ − b + 1`)
  set Wθ : ℝ≥0∞ := ∫⁻ A in matBox b M₂ 1,
      ENNReal.ofReal (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2)) with hWdef
  have hWfin : Wθ < ⊤ := corankWeight_bpos_lt_top Z hbM (s₀ := θ * (a : ℝ)) hθa hZrank
  -- the `A_cor`-independent constant (the Cresid factor + the bounded brick's volume)
  set Kconst : ℝ≥0∞ :=
      ENNReal.ofReal (Cresid (a * b) c' ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2)))
        * (volume sΓ) ^ (1 - θ) with hKdef
  have hKfin : Kconst < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg h1θ (ne_of_lt hsΓ))
  refine ⟨Wθ * ENNReal.ofReal (Cresid (a * b) c' ^ θ) * (volume sΓ) ^ (1 - θ), ?_, ?_⟩
  · -- finiteness of `C₁`
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hWfin ENNReal.ofReal_lt_top) ?_
    exact ENNReal.rpow_lt_top_of_nonneg h1θ (ne_of_lt hsΓ)
  -- the main bound
  have hmeasbox : MeasurableSet (matBox b M₂ 1) := matBox_measurableSet b M₂ 1
  have hbZ : b ≤ Z.rank := by rw [hZrank]; exact hbM
  have hfz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
  -- the shifted core (`≥ w`, exponent `≤ 0`) is dominated by `w^{−(c'−ab/2)}`
  have hcorepow : ∀ X : Matrix (Fin a) (Fin n) ℝ,
      (w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) + frobSq X) ^ (-(c' - (a * b : ℝ) / 2))
        ≤ w ^ (-(c' - (a * b : ℝ) / 2)) := fun X =>
    Real.rpow_le_rpow_of_nonpos hw
      (by rw [hfz, add_zero]; exact le_add_of_nonneg_right (frobSq_nonneg _))
      (by linarith [hc'])
  -- the two banked pointwise bounds on the full-row-rank set + their geometric interpolation
  have hpt : ∀ A : Fin b → Fin M₂ → ℝ, (Matrix.of A * Z).rank = b →
      F A ≤ ENNReal.ofReal
              (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2)) * Kconst := by
    intro A hrank
    have hPD := posDef_gram_of_rank_eq (Matrix.of A * Z) hrank
    have hatom := corankBlock_morsePeel_setLE (Apiv := (0 : Matrix (Fin 0) (Fin n) ℝ))
      (Ccross := Ccross) (Qb := Matrix.of A * Z) hPD c' hc' w hw sΓ
    -- fold the corank Gram determinant to `d` (atom obtained BEFORE `set`, so it folds too)
    set d : ℝ := ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det with hddef
    have hd0 : 0 ≤ d := by rw [hddef]; exact (posSemidef_mul_transpose _).det_nonneg
    have hFeq : F A = ∫⁻ Γ in sΓ, ENNReal.ofReal
        ((w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ)
          + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) := by
      simp only [hFdef]
      exact lintegral_congr (fun Γ => by rw [hfz, add_zero])
    -- ATOM (core dropped to `w`)
    have hAtomBound : F A ≤ ENNReal.ofReal
        (d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))) := by
      rw [hFeq]
      refine le_trans hatom ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [show d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))
            = d ^ (-(a : ℝ) / 2) * Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)) from by ring]
      exact mul_le_mul_of_nonneg_left (hcorepow _)
        (mul_nonneg (Real.rpow_nonneg hd0 _) (Cresid_nonneg _ _))
    -- BOUNDED brick
    have hBddBound : F A ≤ ENNReal.ofReal (w ^ (-c')) * volume sΓ := by
      simp only [hFdef]
      exact corankBlock_boundedGen_le Ccross (Matrix.of A * Z) c' hc0 w hw sΓ
    -- geometric interpolation, then collapse the `ℝ≥0∞`/`ℝ` powers
    refine (enn_geom_interp hθ0 hθ1.le hAtomBound hBddBound).trans (le_of_eq ?_)
    have hBatom_nn : (0 : ℝ)
        ≤ d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))) :=
      mul_nonneg (Real.rpow_nonneg hd0 _)
        (mul_nonneg (Cresid_nonneg _ _) (Real.rpow_nonneg hw.le _))
    calc (ENNReal.ofReal (d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2))))) ^ θ
            * (ENNReal.ofReal (w ^ (-c')) * volume sΓ) ^ (1 - θ)
        = ENNReal.ofReal
              ((d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))) ^ θ)
            * (ENNReal.ofReal ((w ^ (-c')) ^ (1 - θ)) * (volume sΓ) ^ (1 - θ)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hBatom_nn hθ0, ENNReal.mul_rpow_of_nonneg _ _ h1θ,
              ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hw.le _) h1θ]
      _ = ENNReal.ofReal
              ((d ^ (-(a : ℝ) / 2) * (Cresid (a * b) c' * w ^ (-(c' - (a * b : ℝ) / 2)))) ^ θ
                * (w ^ (-c')) ^ (1 - θ)) * (volume sΓ) ^ (1 - θ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hBatom_nn _)]
      _ = ENNReal.ofReal
              (d ^ (-(θ * (a : ℝ)) / 2)
                * (Cresid (a * b) c' ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2)))) * (volume sΓ) ^ (1 - θ) := by
          rw [borderline_real_identity hd0 hw (Cresid_nonneg _ _) a b]
      _ = ENNReal.ofReal (d ^ (-(θ * (a : ℝ)) / 2))
              * (ENNReal.ofReal (Cresid (a * b) c' ^ θ * w ^ (-(c' - θ * (a * b : ℝ) / 2)))
                  * (volume sΓ) ^ (1 - θ)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hd0 _), mul_assoc]
      _ = ENNReal.ofReal (d ^ (-(θ * (a : ℝ)) / 2)) * Kconst := by rw [← hKdef]
  -- integrate the a.e. pointwise bound, pull out `Kconst`, box-clip the weight
  calc ∫⁻ A in matBox b M₂ 1, F A
      ≤ ∫⁻ A in matBox b M₂ 1, ENNReal.ofReal
            (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2)) * Kconst := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeasbox).mpr ?_)
        filter_upwards [corank_survival_ae Z hbZ] with A hrank _hAbox
        exact hpt A hrank
    _ = (∫⁻ A in matBox b M₂ 1, ENNReal.ofReal
            (((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det ^ (-(θ * (a : ℝ)) / 2))) * Kconst :=
        lintegral_mul_const' Kconst _ (ne_of_lt hKfin)
    _ = Wθ * Kconst := by rw [← hWdef]
    _ = Wθ * ENNReal.ofReal (Cresid (a * b) c' ^ θ) * (volume sΓ) ^ (1 - θ)
          * ENNReal.ofReal (w ^ (-(c' - θ * (a * b : ℝ) / 2))) := by
        rw [hKdef, ENNReal.ofReal_mul (Real.rpow_nonneg (Cresid_nonneg _ _) _)]
        ring

/-! ## The borderline, named -/

/-- **The off-sector borderline (`a = M₂ − b + 1`), both cases.** The convergent lemmas exclude the
equality cut `a = M₂ − b + 1` (which for `b=1` is `a = M₂`): their corank weight needs the strict
`a < M₂ − b + 1`. The θ-interpolation closes it for any `θ < 1`, since at `a = M₂ − b + 1`,
`θ·a < M₂ − b + 1 ⟺ θ < 1`. Covers `b=1, a=M₂` and `b>1, a=M₂−b+1` uniformly. Bound:
`∫∫ ≤ C₁ · w^{−(c'−θ·ab/2)}`. -/
theorem corankOffSector_borderline_atBorder_le {a b M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (w c' θ : ℝ)
    (hw : 0 < w) (hbM : b ≤ M₂) (hborder : a = M₂ - b + 1) (hZrank : Z.rank = M₂)
    (hc' : (a * b : ℝ) / 2 < c') (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (sΓ : Set (Fin a → Fin b → ℝ)) (hsΓ : volume sΓ < ⊤) :
    ∃ C₁ : ℝ≥0∞, C₁ < ⊤ ∧
      ∫⁻ A_cor in matBox b M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ C₁ * ENNReal.ofReal (w ^ (-(c' - θ * (a * b : ℝ) / 2))) := by
  have hbR : (b : ℝ) ≤ M₂ := by exact_mod_cast hbM
  have hacast : (a : ℝ) = (M₂ : ℝ) - b + 1 := by
    rw [hborder, Nat.cast_add, Nat.cast_sub hbM, Nat.cast_one]
  have hθa : θ * (a : ℝ) < (M₂ : ℝ) - b + 1 := by
    rw [hacast]; nlinarith [hθ1, hbR]
  exact corankOffSector_borderline_le Z Ccross w c' θ hw hbM hZrank hc' hθ0 hθ1 hθa sΓ hsΓ

end DLNFibre.DLN.RLCT
