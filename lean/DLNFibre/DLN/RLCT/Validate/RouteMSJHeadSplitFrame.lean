import DLNFibre.DLN.RLCT.Validate.RouteMSJShellCover
import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJMeasurableEigendecomp
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option linter.style.longLine false

/-!
# `RouteMSJHeadSplitFrame` — Brick F: the measurable piecewise `m`-frame selector

**Thread `genm-inj-injon` (aoyagi-full Stage 2), build-path #3 of `s1-spine-headsplit-cert` §B.3.**
The S1 head-split's `U_s` frame: a measurable piecewise `(Zf, U_sf)` that equals the deep matrix
family `Zdeep` on the good set `G = {z | weakEigCount ε' (Zdeep z) ≤ M₂ − m}` and a fixed full-rank
frame off `G`, with an orthonormal `m`-frame, rank `≥ m`, and the Loewner floor
`Zf·Zfᵀ ⪰ ε'²·U_sf·U_sfᵀ` UNCONDITIONALLY.

This module reproduces `RouteMSJDeeperFlagCore.exists_headSplitFrame` verbatim as
`exists_headSplitFrame_impl`; the controller wires it into the aggregator.

## The one isolated primitive (Mathlib v4.29 spectral-measurability gap)

Everything is built sorry-free on top of a SINGLE isolated primitive `measurableEigendecomp` — a
measurable Hermitian eigendecomposition of a measurable family. That statement is TRUE (witnessed
pointwise by `IsHermitian.eigenvectorUnitary`/`eigenvalues₀`); only the MEASURABILITY is absent at the
pin (eigenvectors are choice-defined; no measurable Borel functional calculus / eigenvalue continuity).
It is now imported sorry-free from `RouteMSJMeasurableEigendecomp` (the F2 assembly of the F2a
`measurableEigenvalues₀` + F2b `exists_measurableEigenframe` sub-bricks).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-! ## Small reusable helpers -/

/-- A matrix-valued map is measurable iff each entry is measurable (the `Matrix`-synonym
`measurable_pi_iff`, applied twice). -/
lemma measurable_matrix_iff {X : Type*} [MeasurableSpace X] {a b : ℕ}
    {f : X → Matrix (Fin a) (Fin b) ℝ} :
    Measurable f ↔ ∀ i j, Measurable (fun z => f z i j) := by
  constructor
  · intro h i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp h)
  · intro h
    exact measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => h i j))

/-- Antitone tuple with few small entries: if at most `M₂ - m` coordinates fall below `c`, the first
`m` coordinates (in the sorted, antitone order) are all `≥ c`. -/
lemma antitone_tail_bound {M₂ : ℕ} {lam : Fin M₂ → ℝ} (hanti : Antitone lam) {c : ℝ} {m : ℕ}
    (hcount : (Finset.univ.filter (fun i => lam i < c)).card ≤ M₂ - m) (hm : m ≤ M₂)
    (i : Fin M₂) (hi : (i : ℕ) < m) : c ≤ lam i := by
  by_contra hlt
  rw [not_le] at hlt
  have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun j => lam j < c) := by
    intro j hj
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, lt_of_le_of_lt (hanti (Finset.mem_Ici.mp hj)) hlt⟩
  have hcard := Finset.card_le_card hsub
  rw [Fin.card_Ici] at hcard
  omega

/-! ## The fixed off-`G` data (`U₀ = [I_m ; 0]`, `V₀ = ε'·[I_m ; 0]`-shaped) -/

/-- The fixed off-`G` orthonormal `m`-frame `[I_m ; 0]`: the first `m` standard basis columns of
`Fin M₂`, as the identity submatrix. -/
def frame0 {M₂ m : ℕ} (h : m ≤ M₂) : Matrix (Fin M₂) (Fin m) ℝ :=
  (1 : Matrix (Fin M₂) (Fin M₂) ℝ).submatrix id (Fin.castLE h)

/-- The fixed off-`G` full-rank matrix `V₀ = ε'·[I_m ; 0]` (an `M₂ × n` matrix of rank `m`). -/
def mat0 {M₂ n m : ℕ} (ε' : ℝ) : Matrix (Fin M₂) (Fin n) ℝ :=
  Matrix.of (fun i j => if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < m then ε' else 0)

@[simp] lemma frame0_apply {M₂ m : ℕ} (h : m ≤ M₂) (i : Fin M₂) (k : Fin m) :
    frame0 h i k = if i = Fin.castLE h k then (1 : ℝ) else 0 := by
  simp [frame0, Matrix.one_apply]

/-- The off-`G` frame is orthonormal: `frame0ᵀ * frame0 = 1`. -/
lemma frame0_transpose_mul {M₂ m : ℕ} (h : m ≤ M₂) :
    (frame0 h)ᵀ * frame0 h = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, frame0_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.castLE h k)]
  · rcases eq_or_ne k l with rfl | hkl
    · simp
    · have : Fin.castLE h k ≠ Fin.castLE h l := fun hc => hkl ((Fin.castLE_injective h) hc)
      simp [hkl, this]
  · intro b _ hb
    simp [hb]
  · intro hcontra
    exact absurd (Finset.mem_univ _) hcontra

/-- `frame0 * frame0ᵀ` is the `m`-leading diagonal projection `diagonal (𝟙_{· < m})`. -/
lemma frame0_mul_transpose {M₂ m : ℕ} (h : m ≤ M₂) :
    frame0 h * (frame0 h)ᵀ = Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then (1 : ℝ) else 0) := by
  ext i i'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, frame0_apply]
  by_cases hi : (i : ℕ) < m
  · rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin m)]
    · have hcast : Fin.castLE h (⟨(i : ℕ), hi⟩ : Fin m) = i := Fin.ext (by simp)
      rw [hcast]
      by_cases hii' : i = i'
      · subst hii'; simp [hi]
      · simp [hii', Ne.symm hii']
    · intro b _ hb
      have hne : i ≠ Fin.castLE h b := by
        intro hc; apply hb
        have hv : (i : ℕ) = (b : ℕ) := by rw [hc]; simp
        exact Fin.ext hv.symm
      rw [if_neg hne]; ring
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro k _
      have hne : i ≠ Fin.castLE h k := by
        intro hc; apply hi; rw [hc]; simp
      rw [if_neg hne, zero_mul]
    · by_cases hii' : i = i'
      · subst hii'; rw [if_pos rfl, if_neg hi]
      · rw [if_neg hii']

@[simp] lemma mat0_apply {M₂ n m : ℕ} (ε' : ℝ) (i : Fin M₂) (j : Fin n) :
    mat0 (m := m) ε' i j = if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < m then ε' else 0 := rfl

/-- `mat0 * mat0ᵀ` is the `m`-leading diagonal `diagonal (ε'²·𝟙_{· < m})`. -/
lemma mat0_mul_transpose {M₂ n m : ℕ} (h' : m ≤ n) (ε' : ℝ) :
    (mat0 (M₂ := M₂) (n := n) (m := m) ε') * (mat0 (M₂ := M₂) (n := n) (m := m) ε')ᵀ
      = Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then ε' ^ 2 else 0) := by
  ext i i'
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [Matrix.transpose_apply, mat0_apply]
  by_cases hi : (i : ℕ) < m
  · rw [Finset.sum_eq_single (⟨(i : ℕ), lt_of_lt_of_le hi h'⟩ : Fin n)]
    · have hc1 : ((i : ℕ) = ((⟨(i : ℕ), lt_of_lt_of_le hi h'⟩ : Fin n) : ℕ) ∧ (i : ℕ) < m) :=
        ⟨rfl, hi⟩
      rw [if_pos hc1]
      by_cases hii' : i = i'
      · subst hii'; rw [if_pos hc1, if_pos rfl, if_pos hi]; ring
      · have hne : ¬ ((i' : ℕ) = ((⟨(i : ℕ), lt_of_lt_of_le hi h'⟩ : Fin n) : ℕ) ∧ (i' : ℕ) < m) := by
          rintro ⟨he, _⟩; exact hii' (Fin.ext he).symm
        rw [if_neg hne, if_neg hii', mul_zero]
    · intro b _ hb
      have hne : ¬ ((i : ℕ) = (b : ℕ) ∧ (i : ℕ) < m) := by
        rintro ⟨he, _⟩; exact hb (Fin.ext he.symm)
      rw [if_neg hne, zero_mul]
    · intro hc; exact absurd (Finset.mem_univ _) hc
  · refine (Finset.sum_eq_zero ?_).trans ?_
    · intro j _
      have hne : ¬ ((i : ℕ) = (j : ℕ) ∧ (i : ℕ) < m) := by rintro ⟨_, h2⟩; exact hi h2
      rw [if_neg hne, zero_mul]
    · by_cases hii' : i = i'
      · subst hii'; rw [if_pos rfl, if_neg hi]
      · rw [if_neg hii']

/-! ## Two helpers for the on-`G` assembly -/

/-- Selecting the first `m` columns of `U` is right-multiplication by the fixed frame `frame0`. -/
lemma submatrix_castLE_eq_mul_frame0 {M₂ m : ℕ} (h : m ≤ M₂) (U : Matrix (Fin M₂) (Fin M₂) ℝ) :
    U.submatrix id (Fin.castLE h) = U * frame0 h := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, id_eq, frame0_apply]
  rw [Finset.sum_eq_single (Fin.castLE h k)]
  · rw [if_pos rfl, mul_one]
  · intro b _ hb; rw [if_neg hb, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ _) hc

/-- A conjugated nonnegative diagonal is positive semidefinite. -/
lemma floor_psd_aux {M₂ : ℕ} (Um : Matrix (Fin M₂) (Fin M₂) ℝ) (d : Fin M₂ → ℝ)
    (hd : ∀ i, 0 ≤ d i) : (Um * Matrix.diagonal d * Umᴴ).PosSemidef :=
  (Matrix.posSemidef_diagonal_iff.mpr hd).mul_mul_conjTranspose_same Um

/-! ## Brick F -/

/-- **Brick F (`exists_headSplitFrame`, `s1-spine-headsplit-cert` §B.3) — the measurable piecewise
`m`-frame selector.** For a measurable deep-matrix family `Zdeep : X → M₂×n`, with `m ≤ M₂`, `m ≤ n`,
and a floor `ε' > 0`, there is a piecewise `(Zf, U_sf)` — `= Zdeep` on the good set `G = {z |
weakEigCount ε' (Zdeep z) ≤ M₂ − m}`, a fixed full-rank `V` off `G` — that is measurable, carries an
orthonormal `m`-frame `U_sf`, rank `≥ m`, and the Loewner floor `Zf·Zfᵀ ⪰ ε'²·U_sf·U_sfᵀ`
UNCONDITIONALLY. Built sorry-free on the one isolated primitive `measurableEigendecomp`. -/
theorem exists_headSplitFrame_impl {X : Type*} [MeasurableSpace X] {M₂ n m : ℕ}
    (hmM₂ : m ≤ M₂) (hmn : m ≤ n) {ε' : ℝ} (hε' : 0 < ε')
    (Zdeep : X → Matrix (Fin M₂) (Fin n) ℝ) (hZ : Measurable Zdeep) :
    ∃ (Zf : X → Matrix (Fin M₂) (Fin n) ℝ) (U_sf : X → Matrix (Fin M₂) (Fin m) ℝ),
      Measurable Zf ∧ Measurable U_sf
      ∧ (∀ z, (U_sf z)ᵀ * U_sf z = 1)
      ∧ (∀ z, m ≤ (Zf z).rank)
      ∧ (∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
      ∧ (∀ z, weakEigCount ε' (Zdeep z) ≤ M₂ - m → Zf z = Zdeep z) := by
  classical
  -- The measurable, positive-semidefinite Gram family `A z = Zdeep z · (Zdeep z)ᴴ`.
  set A : X → Matrix (Fin M₂) (Fin M₂) ℝ := fun z => Zdeep z * (Zdeep z)ᴴ with hAdef
  have hpsd : ∀ z, (A z).PosSemidef := fun z => Matrix.posSemidef_self_mul_conjTranspose (Zdeep z)
  have hherm : ∀ z, (A z).IsHermitian := fun z => (hpsd z).isHermitian
  have hAmeas : Measurable A := by
    refine measurable_matrix_iff.mpr (fun i j => ?_)
    have hEnt : (fun z => A z i j) = fun z => ∑ k, Zdeep z i k * Zdeep z j k := by
      funext z
      simp only [hAdef, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
    rw [hEnt]
    exact Finset.measurable_sum _ (fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hZ)).mul
        ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hZ)))
  -- The isolated primitive: a measurable orthogonal diagonalizer + measurable sorted eigenvalues.
  obtain ⟨hMeasEig, U, hMeasU, hUortho, hdiag⟩ := measurableEigendecomp A hAmeas hherm
  set lam : X → Fin M₂ → ℝ :=
    fun z i => (hherm z).eigenvalues₀ (finCongr (Fintype.card_fin M₂).symm i) with hlamdef
  have hdiag' : ∀ z, A z = U z * Matrix.diagonal (lam z) * (U z)ᵀ := hdiag
  have hlam_meas : ∀ i, Measurable (fun z => lam z i) :=
    fun i => (measurable_pi_apply (finCongr (Fintype.card_fin M₂).symm i)).comp hMeasEig
  have hlam_anti : ∀ z, Antitone (lam z) := by
    intro z i j hij
    refine (hherm z).eigenvalues₀_antitone ?_
    rw [Fin.le_iff_val_le_val, finCongr_apply_coe, finCongr_apply_coe, ← Fin.le_iff_val_le_val]
    exact hij
  -- `diagonal lam = Uᴴ · A · U` is PSD, hence `lam ≥ 0` pointwise.
  have hD_psd : ∀ z, (Matrix.diagonal (lam z)).PosSemidef := by
    intro z
    have hEq : Matrix.diagonal (lam z) = (U z)ᴴ * A z * U z := by
      rw [hdiag' z, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.mul_assoc (U z) (Matrix.diagonal (lam z)) ((U z)ᵀ),
        ← Matrix.mul_assoc ((U z)ᵀ) (U z) (Matrix.diagonal (lam z) * (U z)ᵀ),
        hUortho z, Matrix.one_mul,
        Matrix.mul_assoc (Matrix.diagonal (lam z)) ((U z)ᵀ) (U z), hUortho z, Matrix.mul_one]
    rw [hEq]; exact (hpsd z).conjTranspose_mul_mul_same (U z)
  have hlam_nonneg : ∀ z i, 0 ≤ lam z i := fun z i =>
    (Matrix.posSemidef_diagonal_iff.mp (hD_psd z)) i
  -- The weak-eigenvalue count as a `Fin M₂` filter card.
  have hcount : ∀ z, weakEigCount ε' (Zdeep z)
      = (Finset.univ.filter (fun i : Fin M₂ => lam z i < ε' ^ 2)).card := by
    intro z
    unfold weakEigCount
    rw [Finset.card_filter, Finset.card_filter]
    exact (Equiv.sum_comp (finCongr (Fintype.card_fin M₂).symm)
      (fun j => if (hherm z).eigenvalues₀ j < ε' ^ 2 then (1 : ℕ) else 0)).symm
  -- The good set.
  set G : Set X := {z | weakEigCount ε' (Zdeep z) ≤ M₂ - m} with hGdef
  have hGmeas : MeasurableSet G := by
    have hGeq : G = ⋃ (S : Finset (Fin M₂)) (_ : S.card = m), ⋂ i ∈ S, {z | ε' ^ 2 ≤ lam z i} := by
      ext z
      simp only [hGdef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, hcount z]
      have hsplit : (Finset.univ.filter (fun i : Fin M₂ => lam z i < ε' ^ 2)).card
          + (Finset.univ.filter (fun i : Fin M₂ => ε' ^ 2 ≤ lam z i)).card = M₂ := by
        have h1 := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin M₂))) (fun i => lam z i < ε' ^ 2)
        simpa only [Finset.card_univ, Fintype.card_fin, not_lt] using h1
      constructor
      · intro hle
        obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
          (show m ≤ (Finset.univ.filter (fun i : Fin M₂ => ε' ^ 2 ≤ lam z i)).card by omega)
        exact ⟨S, hScard, fun i hi => (Finset.mem_filter.mp (hSsub hi)).2⟩
      · rintro ⟨S, hScard, hSmem⟩
        have hsub : S ⊆ Finset.univ.filter (fun i : Fin M₂ => ε' ^ 2 ≤ lam z i) :=
          fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSmem i hi⟩
        have := hScard ▸ Finset.card_le_card hsub
        omega
    rw [hGeq]
    refine MeasurableSet.iUnion (fun S => MeasurableSet.iUnion (fun _ => ?_))
    refine MeasurableSet.biInter (S.countable_toSet) (fun i _ => ?_)
    exact measurableSet_le measurable_const (hlam_meas i)
  -- On `G`, the top-`m` sorted eigenvalues are `≥ ε'²`.
  have htopm : ∀ z ∈ G, ∀ i : Fin M₂, (i : ℕ) < m → ε' ^ 2 ≤ lam z i := by
    intro z hz i hi
    exact antitone_tail_bound (hlam_anti z) (by rw [← hcount z]; exact hz) hmM₂ i hi
  -- Units from orthogonality.
  have hUdet : ∀ z, IsUnit (U z).det := by
    intro z
    have h1 : (U z).det * (U z).det = 1 := by
      have h2 : ((U z)ᵀ).det * (U z).det = 1 := by
        rw [← Matrix.det_mul, hUortho z, Matrix.det_one]
      rwa [Matrix.det_transpose] at h2
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  have hUTdet : ∀ z, IsUnit ((U z)ᵀ).det := fun z => by rw [Matrix.det_transpose]; exact hUdet z
  -- The witnesses.
  refine ⟨Set.piecewise G Zdeep (fun _ => mat0 (m := m) ε'),
    Set.piecewise G (fun z => (U z).submatrix id (Fin.castLE hmM₂)) (fun _ => frame0 hmM₂),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Measurable.piecewise hGmeas hZ measurable_const
  · refine Measurable.piecewise hGmeas ?_ measurable_const
    exact measurable_matrix_iff.mpr
      (fun i j => (measurable_matrix_iff.mp hMeasU) i (Fin.castLE hmM₂ j))
  · intro z
    by_cases hz : z ∈ G
    · rw [Set.piecewise_eq_of_mem _ _ _ hz, submatrix_castLE_eq_mul_frame0,
        Matrix.transpose_mul,
        Matrix.mul_assoc ((frame0 hmM₂)ᵀ) ((U z)ᵀ) (U z * frame0 hmM₂),
        ← Matrix.mul_assoc ((U z)ᵀ) (U z) (frame0 hmM₂), hUortho z, Matrix.one_mul,
        frame0_transpose_mul]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, frame0_transpose_mul]
  · intro z
    by_cases hz : z ∈ G
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
      have hcard_ge : m ≤ (Finset.univ.filter (fun i : Fin M₂ => lam z i ≠ 0)).card := by
        have hsub : (Finset.univ.map ⟨Fin.castLE hmM₂, Fin.castLE_injective hmM₂⟩ : Finset (Fin M₂))
            ⊆ Finset.univ.filter (fun i => lam z i ≠ 0) := by
          intro i hi
          simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and] at hi
          obtain ⟨k, rfl⟩ := hi
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hlt : ((Fin.castLE hmM₂ k : Fin M₂) : ℕ) < m := by simp
          exact ne_of_gt (lt_of_lt_of_le (by positivity) (htopm z hz _ hlt))
        calc m = (Finset.univ.map ⟨Fin.castLE hmM₂, Fin.castLE_injective hmM₂⟩ : Finset (Fin M₂)).card := by
                rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := Finset.card_le_card hsub
      have hAeq : Zdeep z * (Zdeep z)ᴴ = U z * Matrix.diagonal (lam z) * (U z)ᵀ := hdiag' z
      rw [← Matrix.rank_self_mul_conjTranspose (Zdeep z), hAeq, Matrix.mul_assoc,
        rank_mul_eq_right_of_isUnit_det (U z) _ (hUdet z),
        rank_mul_eq_left_of_isUnit_det ((U z)ᵀ) _ (hUTdet z), Matrix.rank_diagonal,
        Fintype.card_subtype]
      exact hcard_ge
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz,
        ← Matrix.rank_self_mul_conjTranspose (mat0 (m := m) ε'),
        Matrix.conjTranspose_eq_transpose_of_trivial, mat0_mul_transpose hmn,
        Matrix.rank_diagonal, Fintype.card_subtype]
      have hsub : (Finset.univ.map ⟨Fin.castLE hmM₂, Fin.castLE_injective hmM₂⟩ : Finset (Fin M₂))
          ⊆ Finset.univ.filter (fun i : Fin M₂ => (if (i : ℕ) < m then ε' ^ 2 else 0) ≠ 0) := by
        intro i hi
        simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and] at hi
        obtain ⟨k, rfl⟩ := hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hlt : ((Fin.castLE hmM₂ k : Fin M₂) : ℕ) < m := by simp
        rw [if_pos hlt]; positivity
      calc m = (Finset.univ.map ⟨Fin.castLE hmM₂, Fin.castLE_injective hmM₂⟩ : Finset (Fin M₂)).card := by
              rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
  · intro z
    by_cases hz : z ∈ G
    · rw [Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ hz,
        submatrix_castLE_eq_mul_frame0]
      have hZZ : Zdeep z * (Zdeep z)ᵀ = U z * Matrix.diagonal (lam z) * (U z)ᵀ := by
        rw [← Matrix.conjTranspose_eq_transpose_of_trivial (Zdeep z)]; exact hdiag' z
      have hUU : (U z * frame0 hmM₂) * (U z * frame0 hmM₂)ᵀ
          = U z * Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then (1 : ℝ) else 0) * (U z)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc (frame0 hmM₂) ((frame0 hmM₂)ᵀ) ((U z)ᵀ), frame0_mul_transpose,
          ← Matrix.mul_assoc]
      rw [hZZ, hUU]
      have hMeq : Matrix.diagonal (lam z)
            - (ε' ^ 2) • Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then (1 : ℝ) else 0)
          = Matrix.diagonal (fun i : Fin M₂ => lam z i - ε' ^ 2 * (if (i : ℕ) < m then (1 : ℝ) else 0)) := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      have hfloor_eq : U z * Matrix.diagonal (lam z) * (U z)ᵀ
          - (ε' ^ 2) • (U z * Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then (1 : ℝ) else 0) * (U z)ᵀ)
          = U z * (Matrix.diagonal (lam z)
              - (ε' ^ 2) • Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then (1 : ℝ) else 0)) * (U z)ᴴ := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial (U z), mul_sub, sub_mul]
        congr 1
        rw [Matrix.mul_smul, Matrix.smul_mul]
      rw [hfloor_eq, hMeq]
      refine floor_psd_aux (U z) _ (fun i => ?_)
      by_cases hi : (i : ℕ) < m
      · rw [if_pos hi, mul_one]; linarith [htopm z hz i hi]
      · rw [if_neg hi, mul_zero, sub_zero]; exact hlam_nonneg z i
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, Set.piecewise_eq_of_notMem _ _ _ hz,
        mat0_mul_transpose hmn, frame0_mul_transpose]
      rw [show Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then ε' ^ 2 else 0)
          - (ε' ^ 2) • Matrix.diagonal (fun i : Fin M₂ => if (i : ℕ) < m then (1 : ℝ) else 0)
          = 0 from by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.zero_apply,
          smul_eq_mul]
        by_cases hij : i = j
        · subst hij; by_cases hi : (i : ℕ) < m <;> simp [hi]
        · simp [hij]]
      exact Matrix.PosSemidef.zero
  · intro z hw
    exact Set.piecewise_eq_of_mem _ _ _ hw

end DLNFibre.DLN.RLCT
