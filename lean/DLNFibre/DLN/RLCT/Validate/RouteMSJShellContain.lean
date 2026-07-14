import DLNFibre.DLN.RLCT.Validate.RouteMSJKyFan
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option linter.style.longLine false

/-!
# `RouteMSJShellContain` — the D-C containment corollary `shell_subset_goodSet` (Brick D-C)

**Thread `genm-sj5` (aoyagi-full Stage 2), Brick D-C sub-brick.** The good-set clause Brick F provides /
Brick D-assembly consumes: on the count-shell `{A'₀·Z_deep ∈ singularShell ε r j}` (`j < r`) with `A'₀`
in the entry-box, the deep factor has `weakEigCount ε' Z_deep ≤ M₂ − m`, where `ε' = ε/√(M₁·M₂)` and
`m = min(M₁,n) − j`.

Consumes the BANKED spectral core `RouteMSJKyFan.finrank_add_weakCount_le` (for a Hermitian `H` and a
subspace `U` with Rayleigh `⟪u,Hu⟫ ≥ c‖u‖²`, `finrank U + #{eigenvalues < c} ≤ k`) and its eigenbasis
helpers (`rayleigh_expansion`, `sum_sq_inner_eigenvectorBasis`), plus `RouteMSJProductTube`
(`posSemidef_mul_transpose`).

Three mechanical pieces (D-C recon):

* **`exists_strong_eigenspace`** (Fact S) — the DUAL of the banked core: a subspace of dim
  `#{eigenvalues ≥ c}` with Rayleigh `≥ c`, the span of the strong eigenvectors.
* **transport + Cauchy–Schwarz** — `U := (A'₀ᴴ)''(strong eigenspace of the full Gram)`; `A'₀ᴴ` is
  injective there (Gram nonvanishing), so `dim U = M₁ − j`; on the box `‖A'₀ᴴ v‖² ≤ M₁M₂·‖v‖²`
  (`sum_mul_sq_le_sq_mul_sq`), giving Rayleigh `≥ ε'²` for the deep Gram; the banked core then bounds
  the deep weak-count.
* **`card_filter_eigenvalues_eq`** — the `eigenvalues ↔ eigenvalues₀` count bridge (the core uses the
  `Fin k`-indexed `eigenvalues`; `weakEigCount` uses the sorted `eigenvalues₀`).

Network-free spectral linear algebra. Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-- `ofLp (toEuclideanLin M v) = M *ᵥ ofLp v` (a `rfl`, restated to avoid the deprecated
`ofLp_toEuclideanLin_apply` and its instance friction). -/
theorem ofLp_toEuclideanLin' {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (v : EuclideanSpace ℝ (Fin q)) :
    WithLp.ofLp (Matrix.toEuclideanLin M v) = M *ᵥ WithLp.ofLp v := rfl

/-- **The `eigenvalues ↔ eigenvalues₀` count bridge.** For a Hermitian `H`, the number of `Fin k`-indexed
eigenvalues `< c` equals the number of sorted eigenvalues `< c` (the two indexings differ by the sorting
bijection). Connects the banked core's `#{eigenvalues < c}` to `weakEigCount`'s `#{eigenvalues₀ < c}`. -/
theorem card_filter_eigenvalues_eq {p : ℕ} {H : Matrix (Fin p) (Fin p) ℝ}
    (hH : H.IsHermitian) (c : ℝ) :
    (Finset.univ.filter (fun i => hH.eigenvalues i < c)).card
      = (Finset.univ.filter (fun i => hH.eigenvalues₀ i < c)).card := by
  classical
  set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))).symm with he
  have key : ∀ i, hH.eigenvalues i = hH.eigenvalues₀ (e i) := fun _ => rfl
  refine Finset.card_bij' (fun i _ => e i) (fun k _ => e.symm k) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, by rw [← key i]; exact hi.2⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [key (e.symm k), Equiv.apply_symm_apply]; exact hk.2
  · intro i _; exact e.symm_apply_apply i
  · intro k _; exact e.apply_symm_apply k

/-- **The Gram quadratic form as a dot product.** `⟪x, (M Mᴴ) x⟫ = ‖Mᴴ x‖²` in raw-vector form:
`⟪x, toEuclideanLin (M Mᴴ) x⟫ = (Mᴴ *ᵥ ofLp x) ⬝ᵥ (Mᴴ *ᵥ ofLp x)`. -/
theorem gram_inner_eq {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    inner ℝ x (Matrix.toEuclideanLin (M * Mᴴ) x)
      = (Mᴴ *ᵥ WithLp.ofLp x) ⬝ᵥ (Mᴴ *ᵥ WithLp.ofLp x) := by
  have h1 : inner ℝ x (Matrix.toEuclideanLin (M * Mᴴ) x)
      = WithLp.ofLp x ⬝ᵥ ((M * Mᴴ) *ᵥ WithLp.ofLp x) := by
    have hr : inner ℝ x (Matrix.toEuclideanLin (M * Mᴴ) x)
        = ((M * Mᴴ) *ᵥ WithLp.ofLp x) ⬝ᵥ star (WithLp.ofLp x) := rfl
    rw [hr, dotProduct_comm]
    have hstar : star (WithLp.ofLp x) = WithLp.ofLp x := by funext i; exact star_trivial _
    rw [hstar]
  rw [h1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      ← Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **Fact S — the strong eigenspace (the DUAL of the banked counting core).** For a Hermitian `H` on
`EuclideanSpace ℝ (Fin p)` and threshold `c`, the span of the eigenvectors with eigenvalue `≥ c` has
dimension `#{eigenvalues ≥ c}` and Rayleigh quotient `≥ c` on it. -/
theorem exists_strong_eigenspace {p : ℕ} (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian) (c : ℝ) :
    ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin p)),
      Module.finrank ℝ V = (Finset.univ.filter (fun i => c ≤ hH.eigenvalues i)).card ∧
      ∀ v ∈ V, c * ‖v‖ ^ 2 ≤ inner ℝ v (Matrix.toEuclideanLin H v) := by
  classical
  set T : Finset (Fin p) := Finset.univ.filter (fun i => c ≤ hH.eigenvalues i) with hT
  set b : {i // i ∈ T} → EuclideanSpace ℝ (Fin p) := fun i => hH.eigenvectorBasis (i : Fin p) with hb
  have hbli : LinearIndependent ℝ b :=
    (hH.eigenvectorBasis.orthonormal.linearIndependent).comp _ Subtype.val_injective
  refine ⟨Submodule.span ℝ (Set.range b), ?_, ?_⟩
  · rw [finrank_span_eq_card hbli, Fintype.card_coe]
  · intro u huV
    -- orthogonality: `⟪eigenvectorBasis j, u⟫ = 0` for `j ∉ T` (u in the span of the strong eigenvectors)
    have hortho : ∀ j : Fin p, j ∉ T → inner ℝ (hH.eigenvectorBasis j) u = 0 := by
      intro j hj
      refine Submodule.span_induction (p := fun u _ => inner ℝ (hH.eigenvectorBasis j) u = 0)
        ?_ ?_ ?_ ?_ huV
      · rintro _ ⟨i, rfl⟩
        have hne : j ≠ (i : Fin p) := fun h => hj (h ▸ i.2)
        have hpair := orthonormal_iff_ite.1 hH.eigenvectorBasis.orthonormal j (i : Fin p)
        rw [if_neg hne] at hpair
        exact hpair
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    rw [rayleigh_expansion H hH u]
    have key : ∀ i, c * (inner ℝ (hH.eigenvectorBasis i) u) ^ 2
        ≤ hH.eigenvalues i * (inner ℝ (hH.eigenvectorBasis i) u) ^ 2 := by
      intro i
      by_cases hi : i ∈ T
      · exact mul_le_mul_of_nonneg_right (Finset.mem_filter.1 hi).2 (sq_nonneg _)
      · rw [hortho i hi]; simp
    calc c * ‖u‖ ^ 2
        = c * ∑ i, (inner ℝ (hH.eigenvectorBasis i) u) ^ 2 := by
          rw [← sum_sq_inner_eigenvectorBasis H hH u]
      _ = ∑ i, c * (inner ℝ (hH.eigenvectorBasis i) u) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ i, hH.eigenvalues i * (inner ℝ (hH.eigenvectorBasis i) u) ^ 2 :=
          Finset.sum_le_sum (fun i _ => key i)

/-- **The box Cauchy–Schwarz bound.** For `A'₀` with entries `≤ 1` in absolute value,
`‖A'₀ᴴ v‖² ≤ M₁·M₂·‖v‖²` (row-wise Cauchy–Schwarz + the `M₁·M₂` entry bound). -/
theorem norm_sq_toEuclideanLin_le {M₁ M₂ : ℕ} (A'₀ : Matrix (Fin M₁) (Fin M₂) ℝ)
    (hbox : ∀ i k, |A'₀ i k| ≤ 1) (v : EuclideanSpace ℝ (Fin M₁)) :
    ‖Matrix.toEuclideanLin (A'₀ᴴ) v‖ ^ 2 ≤ ((M₁ : ℝ) * M₂) * ‖v‖ ^ 2 := by
  set w : Fin M₁ → ℝ := WithLp.ofLp v with hw
  have hcoe : ∀ i, (Matrix.toEuclideanLin (A'₀ᴴ) v) i = (A'₀ᴴ *ᵥ w) i :=
    fun i => congrArg (fun z => z i) (ofLp_toEuclideanLin' (A'₀ᴴ) v)
  have hnv : ∑ l, (w l) ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact (Finset.sum_congr rfl (fun l _ => by rw [Real.norm_eq_abs, sq_abs])).symm
  have hfrob : (∑ i : Fin M₂, ∑ l : Fin M₁, (A'₀ᴴ i l) ^ 2) ≤ (M₁ : ℝ) * M₂ := by
    calc (∑ i : Fin M₂, ∑ l : Fin M₁, (A'₀ᴴ i l) ^ 2)
        ≤ ∑ _i : Fin M₂, ∑ _l : Fin M₁, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun l _ => ?_))
          have hb : |A'₀ᴴ i l| ≤ 1 := by
            rw [Matrix.conjTranspose_apply, star_trivial]; exact hbox l i
          nlinarith [hb, abs_nonneg (A'₀ᴴ i l), sq_abs (A'₀ᴴ i l)]
      _ = (M₁ : ℝ) * M₂ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          ring
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖(Matrix.toEuclideanLin (A'₀ᴴ) v) i‖ ^ 2
      = ∑ i, (∑ l, A'₀ᴴ i l * w l) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hcoe i, Real.norm_eq_abs, sq_abs, Matrix.mulVec]
        rfl
    _ ≤ ∑ i, (∑ l, (A'₀ᴴ i l) ^ 2) * (∑ l, (w l) ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _)
    _ = (∑ i, ∑ l, (A'₀ᴴ i l) ^ 2) * (∑ l, (w l) ^ 2) := by rw [← Finset.sum_mul]
    _ ≤ ((M₁ : ℝ) * M₂) * ‖v‖ ^ 2 := by
        rw [hnv]
        exact mul_le_mul_of_nonneg_right hfrob (by positivity)

/-- **The D-C containment corollary `shell_subset_goodSet`.** On the single-`ε` count-shell
`{A'₀·Z_deep ∈ singularShell ε r j}` (`j < r`) with `A'₀` in the entry-box (`|A'₀ i k| ≤ 1`), the deep
factor has few small singular values at the rescaled threshold: `weakEigCount ε' Z_deep ≤ M₂ − m`,
where `ε' = ε/√(M₁·M₂)` and `m = min(M₁,n) − j`. The good-set clause Brick D-assembly consumes. -/
theorem shell_subset_goodSet {M₁ M₂ n r : ℕ} {ε : ℝ} (hε : 0 < ε)
    (j : Fin (r + 1)) (hjr : (j : ℕ) < r)
    (A'₀ : Matrix (Fin M₁) (Fin M₂) ℝ) (Zd : Matrix (Fin M₂) (Fin n) ℝ)
    (hbox : ∀ i k, |A'₀ i k| ≤ 1)
    (hshell : A'₀ * Zd ∈ singularShell ε r j) :
    weakEigCount (ε / Real.sqrt ((M₁ : ℝ) * M₂)) Zd ≤ M₂ - (min M₁ n - (j : ℕ)) := by
  classical
  set ε' : ℝ := ε / Real.sqrt ((M₁ : ℝ) * M₂) with hε'def
  -- the weak count is always `≤ M₂`
  have hcard : weakEigCount ε' Zd ≤ M₂ := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos M₂ with hM2 | hM2
  · omega
  -- the full product and its Gram
  set Zf : Matrix (Fin M₁) (Fin n) ℝ := A'₀ * Zd with hZf
  set hHf := (Matrix.posSemidef_self_mul_conjTranspose Zf).isHermitian with hHfdef
  -- on the shell (`j < r`), exactly `j` small singular values of the full product
  have hj_eq : weakEigCount ε Zf = (j : ℕ) := by
    have hmem := hshell
    simp only [singularShell, Set.mem_setOf_eq] at hmem
    omega
  -- Fact S: the strong eigenspace of the full Gram at threshold `ε²`
  obtain ⟨V, hVdim, hVray⟩ := exists_strong_eigenspace (Zf * Zfᴴ) hHf (ε ^ 2)
  -- its dimension is `M₁ − j`
  have hVdim' : Module.finrank ℝ V = M₁ - (j : ℕ) := by
    rw [hVdim]
    have hcompl := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin M₁))) (fun i => ε ^ 2 ≤ hHf.eigenvalues i)
    have hnot : (Finset.univ.filter (fun i => ¬ (ε ^ 2 ≤ hHf.eigenvalues i))).card
        = (Finset.univ.filter (fun i => hHf.eigenvalues i < ε ^ 2)).card := by
      congr 1; ext i; simp only [not_le]
    have hbridge := card_filter_eigenvalues_eq hHf (ε ^ 2)
    have hwe : weakEigCount ε Zf
        = (Finset.univ.filter (fun i => hHf.eigenvalues₀ i < ε ^ 2)).card := rfl
    rw [Finset.card_univ, Fintype.card_fin] at hcompl
    omega
  -- transport map `A'₀ᴴ` is injective on `V`, so `finrank (V.map A'₀ᴴ) = M₁ − j`
  have hdisj : V ⊓ LinearMap.ker (Matrix.toEuclideanLin (A'₀ᴴ)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨hwV, hwK⟩ := Submodule.mem_inf.1 hw
    by_contra hne
    have hAw : A'₀ᴴ *ᵥ WithLp.ofLp w = 0 := by
      have h0 := LinearMap.mem_ker.1 hwK
      calc A'₀ᴴ *ᵥ WithLp.ofLp w
          = WithLp.ofLp (Matrix.toEuclideanLin (A'₀ᴴ) w) := (ofLp_toEuclideanLin' (A'₀ᴴ) w).symm
        _ = WithLp.ofLp (0 : EuclideanSpace ℝ (Fin M₂)) := by rw [h0]
        _ = 0 := by simp
    have hinner0 : inner ℝ w (Matrix.toEuclideanLin (Zf * Zfᴴ) w) = 0 := by
      rw [gram_inner_eq Zf w]
      have hz : Zfᴴ *ᵥ WithLp.ofLp w = 0 := by
        rw [hZf, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hAw, Matrix.mulVec_zero]
      rw [hz, dotProduct_zero]
    have hpos : 0 < ε ^ 2 * ‖w‖ ^ 2 := by
      have : 0 < ‖w‖ := norm_pos_iff.mpr hne
      positivity
    have hle := hVray w hwV
    rw [hinner0] at hle
    linarith
  have hinj : Function.Injective ((Matrix.toEuclideanLin (A'₀ᴴ)).domRestrict V) :=
    LinearMap.injective_domRestrict_iff.mpr hdisj
  have hUdim : Module.finrank ℝ (V.map (Matrix.toEuclideanLin (A'₀ᴴ))) = M₁ - (j : ℕ) := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj, hVdim']
  -- the deep Gram has Rayleigh `≥ ε'²` on `U := V.map A'₀ᴴ`
  have hUray : ∀ x ∈ V.map (Matrix.toEuclideanLin (A'₀ᴴ)),
      ε' ^ 2 * ‖x‖ ^ 2 ≤ inner ℝ x (Matrix.toEuclideanLin (Zd * Zdᴴ) x) := by
    intro x hx
    obtain ⟨v, hvV, rfl⟩ := Submodule.mem_map.1 hx
    have heq : inner ℝ (Matrix.toEuclideanLin (A'₀ᴴ) v)
          (Matrix.toEuclideanLin (Zd * Zdᴴ) (Matrix.toEuclideanLin (A'₀ᴴ) v))
        = inner ℝ v (Matrix.toEuclideanLin (Zf * Zfᴴ) v) := by
      rw [gram_inner_eq Zd, gram_inner_eq Zf, ofLp_toEuclideanLin']
      have hmv : Zdᴴ *ᵥ (A'₀ᴴ *ᵥ WithLp.ofLp v) = Zfᴴ *ᵥ WithLp.ofLp v := by
        rw [hZf, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec]
      rw [hmv]
    rw [heq]
    have hCS := norm_sq_toEuclideanLin_le A'₀ hbox v
    have hray := hVray v hvV
    have hε'sq : ε' ^ 2 = ε ^ 2 / ((M₁ : ℝ) * M₂) := by
      rw [hε'def, div_pow, Real.sq_sqrt (by positivity)]
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (M₁ : ℝ) * M₂) with h0 | h0
    · -- `M₁M₂ = 0`: then `‖A'₀ᴴ v‖ = 0`
      have hLv0 : ‖Matrix.toEuclideanLin (A'₀ᴴ) v‖ ^ 2 ≤ 0 := by
        rw [← h0] at hCS; simpa using hCS
      have hchain : ε' ^ 2 * ‖Matrix.toEuclideanLin (A'₀ᴴ) v‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hLv0
      have hinn : 0 ≤ inner ℝ v (Matrix.toEuclideanLin (Zf * Zfᴴ) v) :=
        le_trans (mul_nonneg (sq_nonneg ε) (sq_nonneg ‖v‖)) hray
      linarith
    · -- `M₁M₂ > 0`: `ε'²‖A'₀ᴴ v‖² ≤ ε²‖v‖² ≤ inner`
      have hchain : ε' ^ 2 * ‖Matrix.toEuclideanLin (A'₀ᴴ) v‖ ^ 2 ≤ ε ^ 2 * ‖v‖ ^ 2 := by
        rw [hε'sq, div_mul_eq_mul_div, div_le_iff₀ h0]
        nlinarith [mul_le_mul_of_nonneg_left hCS (sq_nonneg ε)]
      linarith
  -- apply the banked counting core to the deep Gram at `c = ε'²`
  have hcore := finrank_add_weakCount_le (Zd * Zdᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose Zd).isHermitian (ε' ^ 2)
    (V.map (Matrix.toEuclideanLin (A'₀ᴴ))) hUray
  -- bridge the deep count to `weakEigCount ε' Zd`
  have hbridged := card_filter_eigenvalues_eq
    (Matrix.posSemidef_self_mul_conjTranspose Zd).isHermitian (ε' ^ 2)
  have hwed : weakEigCount ε' Zd
      = (Finset.univ.filter
          (fun i => (Matrix.posSemidef_self_mul_conjTranspose Zd).isHermitian.eigenvalues₀ i
            < ε' ^ 2)).card := rfl
  -- `min M₁ n ≤ M₁`, so `M₂ − (M₁−j) ≤ M₂ − (min M₁ n − j)`
  have hmin : min M₁ n ≤ M₁ := min_le_left _ _
  omega

end DLNFibre.DLN.RLCT
