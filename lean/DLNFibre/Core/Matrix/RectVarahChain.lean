import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.StarOrdered

/-!
# `Core.Matrix.RectVarahChain` — the RECTANGULAR Varah chain: `det(P₁ᵀP₁) ≠ 0` for a front product

A network-free engine brick. The boundary-SMEARED achiever chart at `L ≥ 3` needs the rank-block
nondegeneracy `det(P₁ᵀP₁) ≠ 0` where `P₁ = (A⁽⁰⁾·A⁽¹⁾···A⁽ᵏ⁾)[:, :r]` is a **product** of front
factors (`M₀ × r`, `r ≤ every factor width` — the front bottleneck), UNCONDITIONALLY on a conditioned
box (not merely a.e.). At `L = 2` the front product is a SINGLE factor, `P₁` square, and
`StrictRowDominant.det_ne_zero` closes it directly (`RouteMSmearedSquareL2`); at `L ≥ 3` the product
`P₁` is rectangular and this brick is the new content.

The route (Codex-recommended, map-first — inject, then PosDef):

* **Endgame** (`gram_det_ne_of_mulVec_injective`) — an injective `P₁.mulVec` gives `PosDef (P₁ᵀP₁)`
  (`Matrix.PosDef.conjTranspose_mul_self`, with `P₁ᴴ = P₁ᵀ` over `ℝ`), hence `IsUnit`, hence
  `det ≠ 0`. Reusable and short.

* **Per-factor dominance** (`FactorDominant` + `factorDominant_of_box`) — each factor's leading `r×r`
  block is strictly row-diagonally dominant (diagonal `≥ d/2`, every off-block/trailing entry `≤ η`,
  margin `(2m−1)η ≤ d/2`). `factorDominant_of_box` is the box-membership readoff (the `L=2`
  `P1u_diag_ge_of_mem`/`P1u_offdiag_le_of_mem` shape).

* **Propagation** (`factorStep`) — the invariant `LeadCert hrm w V` ("a leading coord attains the
  global max value `V`") propagates: `A *ᵥ w` carries `LeadCert hrn (A*ᵥw) W` with `γ·V ≤ W`,
  `γ = d/2−(m−1)η > 0`. The margin forces trailing rows `≤ m·η·V ≤ γ·V`, so the argmax STAYS leading
  ("the leading coordinate stays dominant through the chain"). The leading row's diagonal-vs-off split
  is the elementary argmax bound, factor by factor.

* **Terminal** (`leadCert_embed` → `factorStep`×k → `mulVec_injective_of_leadCert` /
  `frontGram_det_ne_of_leadCert`) — a zero-padded input has a positive-value `LeadCert`; threading it
  through the factors keeps the value positive (each `γⱼ > 0`), so `P₁.mulVec x ≠ 0` for `x ≠ 0`,
  giving injectivity and `det(P₁ᵀP₁) ≠ 0`.

Non-vacuity: `frontGram_det_ne_231` closes the chain on the `(2,3,1,2,1)` front shape (wide factor +
interior bottleneck, `r=1`), the sharpest surface.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.Core.Matrix

/-! ## Endgame: injective `mulVec` ⟹ `det(AᵀA) ≠ 0` (reusable, `ℝ`) -/

/-- **The Gram determinant is nonzero when `A.mulVec` is injective** (over `ℝ`). `A.mulVec` injective
⟹ `PosDef (Aᴴ · A)` (`Matrix.PosDef.conjTranspose_mul_self`); over `ℝ` the conjugate transpose is the
transpose (`conjTranspose_eq_transpose_of_trivial`), so `PosDef (Aᵀ · A)`, hence `IsUnit`, hence
`det ≠ 0`. This is the clean map-first endgame for a rank-block nondegeneracy: prove `A` injective as
an operator, get the square Gram nonsingular. -/
theorem gram_det_ne_of_mulVec_injective {m r : ℕ} (A : Matrix (Fin m) (Fin r) ℝ)
    (hinj : Function.Injective A.mulVec) :
    (Aᵀ * A).det ≠ 0 := by
  have hpd : (Aᴴ * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hinj
  rw [conjTranspose_eq_transpose_of_trivial] at hpd
  have hunit : IsUnit (Aᵀ * A) := hpd.isUnit
  exact ((Matrix.isUnit_iff_isUnit_det (Aᵀ * A)).mp hunit).ne_zero

/-! ## The leading-dominance certificate `LeadCert` and its per-factor propagation

The chain invariant: a vector `w : Fin m → ℝ` carries `LeadCert hrm w V` when every coordinate is
`≤ V` in absolute value AND some LEADING coordinate (index in `Fin r`, embedded via `Fin.castLE hrm`)
attains `V`. This "leading coordinate stays dominant, with a realized value `V`" is what propagates
through the front product and threads a positive lower bound (hence nonzero-ness) to the terminal. -/

/-- **Leading-block strict dominance of a rectangular factor.** For `A : Fin n × Fin m` with
`r ≤ n, m`: each leading diagonal entry is `≥ d/2` and every non-(leading-diagonal) entry is `≤ η`,
with the margin `(2·m − 1)·η ≤ d/2` and `0 < d`. This is the box-membership readoff (diagonal front
coords in `[δ/2, δ]`, the rest in `[−η, η]`) at one factor. -/
structure FactorDominant {n m r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (d η : ℝ) : Prop where
  /-- Positive scale. -/
  hd : 0 < d
  /-- Nonneg off-bound. -/
  hη : 0 ≤ η
  /-- Margin: the off-block sum over `m` columns cannot beat the diagonal. -/
  hmargin : (2 * (m : ℝ) - 1) * η ≤ d / 2
  /-- Leading diagonal entries dominate: `|A (castLE i) (castLE i)| ≥ d/2`. -/
  hdiag : ∀ i : Fin r, d / 2 ≤ |A (Fin.castLE hrn i) (Fin.castLE hrm i)|
  /-- Every entry OFF a leading diagonal pair is `≤ η` — split into: (a) a leading row `i < r`,
  column `≠ i`; (b) a trailing row `i ≥ r` (embedded), any column. -/
  hoff_lead : ∀ (i : Fin r) (j : Fin m), (j : ℕ) ≠ (i : ℕ) →
    |A (Fin.castLE hrn i) j| ≤ η
  hoff_trail : ∀ (i : Fin n), (r : ℕ) ≤ (i : ℕ) → ∀ j : Fin m, |A i j| ≤ η

/-- **The box-membership readoff of `FactorDominant`.** For a factor `A` whose leading diagonal entries
lie in `[δ/2, δ]` and whose every other (leading-off / trailing) entry lies in `[−η, η]`, with the
margin `(2m−1)·η ≤ δ/2` and `0 < δ`: `A` is `FactorDominant` with `d = δ`. This is the box-classified
readoff (the `L = 2` `P1u_diag_ge_of_mem` / `P1u_offdiag_le_of_mem` shape, per factor at `L ≥ 3`); the
plumbing supplies the two `Icc` memberships from the conditioned box, this packages them. -/
theorem factorDominant_of_box {n m r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (δ η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hmargin : (2 * (m : ℝ) - 1) * η ≤ δ / 2)
    (hdiag : ∀ i : Fin r, A (Fin.castLE hrn i) (Fin.castLE hrm i) ∈ Set.Icc (δ / 2) δ)
    (hoff_lead : ∀ (i : Fin r) (j : Fin m), (j : ℕ) ≠ (i : ℕ) →
      A (Fin.castLE hrn i) j ∈ Set.Icc (-η) η)
    (hoff_trail : ∀ (i : Fin n), (r : ℕ) ≤ (i : ℕ) → ∀ j : Fin m,
      A i j ∈ Set.Icc (-η) η) :
    FactorDominant hrn hrm A δ η where
  hd := hδ
  hη := hη
  hmargin := hmargin
  hdiag := fun i => by
    have hi := (Set.mem_Icc.mp (hdiag i))
    rw [abs_of_nonneg (by linarith [hi.1])]; exact hi.1
  hoff_lead := fun i j hj => by
    rw [abs_le]; exact Set.mem_Icc.mp (hoff_lead i j hj)
  hoff_trail := fun i hi j => by
    rw [abs_le]; exact Set.mem_Icc.mp (hoff_trail i hi j)

/-! ### The per-factor propagation step -/

/-- **Absolute value of a `mulVec` row, split off the diagonal term.** For a leading row `i < r`:
`|(A *ᵥ w) (castLE i)| ≥ |A_{ii}·w_i| − ∑_{j≠i} |A_{ij}·w_j|`, and each off term is `≤ η·V` when
`|w j| ≤ V`. -/
private theorem leadRow_lb {n m r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    {A : Matrix (Fin n) (Fin m) ℝ} {d η : ℝ} (hA : FactorDominant hrn hrm A d η)
    (w : Fin m → ℝ) {V : ℝ} (hV : ∀ j, |w j| ≤ V) (hVpos : 0 ≤ V) (i : Fin r) :
    d / 2 * |w (Fin.castLE hrm i)| - ((m : ℝ) - 1) * η * V
      ≤ |(A *ᵥ w) (Fin.castLE hrn i)| := by
  -- (A *ᵥ w) (castLE i) = ∑ j, A (castLE i) j * w j = A_{ii} w_i + ∑_{j≠castLE i} A_{ii'} w_j
  have hsplit : (A *ᵥ w) (Fin.castLE hrn i)
      = A (Fin.castLE hrn i) (Fin.castLE hrm i) * w (Fin.castLE hrm i)
        + ∑ j ∈ Finset.univ.erase (Fin.castLE hrm i), A (Fin.castLE hrn i) j * w j := by
    have : (A *ᵥ w) (Fin.castLE hrn i) = ∑ j, A (Fin.castLE hrn i) j * w j := rfl
    rw [this, Finset.sum_erase_eq_sub (Finset.mem_univ _)]; ring
  -- diagonal lower bound: |A_{ii} w_i| ≥ (d/2)|w_i|
  have hdiag : d / 2 * |w (Fin.castLE hrm i)| ≤ |A (Fin.castLE hrn i) (Fin.castLE hrm i) * w (Fin.castLE hrm i)| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hA.hdiag i) (abs_nonneg _)
  -- off-diagonal sum bound: ∑_{j≠i} |A_{ij} w_j| ≤ (m-1)·η·V
  have hoff : |∑ j ∈ Finset.univ.erase (Fin.castLE hrm i), A (Fin.castLE hrn i) j * w j|
      ≤ ((m : ℝ) - 1) * η * V := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbound : ∀ j ∈ Finset.univ.erase (Fin.castLE hrm i),
        |A (Fin.castLE hrn i) j * w j| ≤ η * V := by
      intro j hj
      rw [abs_mul]
      have hjne : (j : ℕ) ≠ (i : ℕ) := by
        intro h
        exact (Finset.mem_erase.mp hj).1 (by
          apply Fin.ext; simpa [Fin.castLE] using h)
      exact mul_le_mul (hA.hoff_lead i j hjne) (hV j) (abs_nonneg _) hA.hη
    calc ∑ j ∈ Finset.univ.erase (Fin.castLE hrm i), |A (Fin.castLE hrn i) j * w j|
        ≤ ∑ _j ∈ Finset.univ.erase (Fin.castLE hrm i), η * V := Finset.sum_le_sum hbound
      _ = (Finset.univ.erase (Fin.castLE hrm i)).card • (η * V) := by rw [Finset.sum_const]
      _ ≤ ((m : ℝ) - 1) * η * V := by
          rw [nsmul_eq_mul]
          have hm1 : 1 ≤ m := by have := i.2; omega
          have hcard : ((Finset.univ.erase (Fin.castLE hrm i)).card : ℝ) ≤ (m : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
              Nat.cast_sub hm1]
            simp
          have hηV : 0 ≤ η * V := mul_nonneg hA.hη hVpos
          calc ((Finset.univ.erase (Fin.castLE hrm i)).card : ℝ) * (η * V)
              ≤ ((m : ℝ) - 1) * (η * V) := mul_le_mul_of_nonneg_right hcard hηV
            _ = ((m : ℝ) - 1) * η * V := by ring
  -- combine via reverse triangle inequality
  rw [hsplit]
  calc d / 2 * |w (Fin.castLE hrm i)| - ((m : ℝ) - 1) * η * V
      ≤ |A (Fin.castLE hrn i) (Fin.castLE hrm i) * w (Fin.castLE hrm i)|
        - |∑ j ∈ Finset.univ.erase (Fin.castLE hrm i), A (Fin.castLE hrn i) j * w j| := by
        linarith [hdiag, hoff]
    _ ≤ |A (Fin.castLE hrn i) (Fin.castLE hrm i) * w (Fin.castLE hrm i)
          + ∑ j ∈ Finset.univ.erase (Fin.castLE hrm i), A (Fin.castLE hrn i) j * w j| := by
        -- `|diag| - |off| ≤ |diag + off|`: from `|diag| = |(diag+off) - off| ≤ |diag+off| + |off|`
        set diag := A (Fin.castLE hrn i) (Fin.castLE hrm i) * w (Fin.castLE hrm i) with hdiagset
        set off := ∑ j ∈ Finset.univ.erase (Fin.castLE hrm i), A (Fin.castLE hrn i) j * w j with hoffset
        have htri : |diag| ≤ |diag + off| + |off| := by
          calc |diag| = |(diag + off) - off| := by ring_nf
            _ ≤ |diag + off| + |off| := abs_sub _ _
        linarith

/-- **Any output coordinate is bounded by `m·η·V`** — a uniform row bound: every entry of `A`'s row `i`
is `≤ η` UNLESS `(i,j)` is a leading diagonal pair. Applied here where we don't need the diagonal:
`|(A *ᵥ w) i| ≤ (∑_j |A i j|)·V`, and each `|A i j| ≤ η` except at most one (the leading diagonal),
which is `≤ d`. We only invoke this at TRAILING rows (`i ≥ r`), where ALL entries are `≤ η`. -/
private theorem trailRow_ub {n m r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    {A : Matrix (Fin n) (Fin m) ℝ} {d η : ℝ} (hA : FactorDominant hrn hrm A d η)
    (w : Fin m → ℝ) {V : ℝ} (hV : ∀ j, |w j| ≤ V)
    (i : Fin n) (hi : (r : ℕ) ≤ (i : ℕ)) :
    |(A *ᵥ w) i| ≤ (m : ℝ) * η * V := by
  have : (A *ᵥ w) i = ∑ j, A i j * w j := rfl
  rw [this]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |A i j * w j|
      ≤ ∑ _j : Fin m, η * V := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hA.hoff_trail i hi j) (hV j) (abs_nonneg _) hA.hη
    _ = (m : ℝ) * η * V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **`LeadMax` with a realized positive value.** `LeadCert hrm w V` bundles the leading-dominance
invariant with an explicit lower bound `V` realized in the leading block: every coord `|w j| ≤ V`, and
some leading coord attains `V ≤ |w (castLE k₀)|`. This threads a concrete positive value through the
chain (so `w ≠ 0` is witnessed by `V > 0`). -/
def LeadCert {m r : ℕ} (hrm : r ≤ m) (w : Fin m → ℝ) (V : ℝ) : Prop :=
  (∀ j, |w j| ≤ V) ∧ ∃ k : Fin r, V ≤ |w (Fin.castLE hrm k)|

/-- **The per-factor propagation step.** If `w` carries a `LeadCert` with value `V` and `A` is
`FactorDominant`, then `A *ᵥ w` carries a `LeadCert` with SOME value `W ≥ γ·V` where
`γ = d/2 − (m−1)η > 0`. The leading row `k*` (a `V`-attaining leading coord) gives `|(A w)_{k*}| ≥
γ·V`; every trailing row is `≤ m·η·V`, and the margin `(2m−1)η ≤ d/2` forces `m·η·V ≤ γ·V`, so the
global max `W = |(A w)_{kmax}|` of `|A w|` sits in the leading block and dominates `γ·V`. Returning `W`
(the actual max, not `γ·V`) keeps `LeadCert`'s "value = max" contract; `γ·V ≤ W` threads positivity. -/
theorem factorStep {n m r : ℕ} (hrn : r ≤ n) (hrm : r ≤ m)
    {A : Matrix (Fin n) (Fin m) ℝ} {d η : ℝ} (hA : FactorDominant hrn hrm A d η)
    {w : Fin m → ℝ} {V : ℝ} (hw : LeadCert hrm w V) :
    ∃ W : ℝ, (d / 2 - ((m : ℝ) - 1) * η) * V ≤ W ∧ LeadCert hrn (A *ᵥ w) W := by
  classical
  obtain ⟨hVall, kstar, hkstar⟩ := hw
  haveI : Nonempty (Fin r) := ⟨kstar⟩
  have hVpos : 0 ≤ V := le_trans (abs_nonneg (w (Fin.castLE hrm kstar))) (hVall (Fin.castLE hrm kstar))
  set γ : ℝ := d / 2 - ((m : ℝ) - 1) * η with hγdef
  have hγpos : 0 ≤ γ := by
    have := hA.hmargin; rw [hγdef]; nlinarith [hA.hη]
  -- lower bound at the leading row kstar: |(A w)_{castLE kstar}| ≥ γ·V
  have hlead : γ * V ≤ |(A *ᵥ w) (Fin.castLE hrn kstar)| := by
    have hrow := leadRow_lb hrn hrm hA w hVall hVpos kstar
    -- d/2 |w (castLE kstar)| - (m-1)ηV ≤ |(Aw)…|; and |w (castLE kstar)| ≥ V
    have hdlow : d / 2 * V ≤ d / 2 * |w (Fin.castLE hrm kstar)| :=
      mul_le_mul_of_nonneg_left hkstar (by linarith [hA.hd])
    calc γ * V = d / 2 * V - ((m : ℝ) - 1) * η * V := by rw [hγdef]; ring
      _ ≤ d / 2 * |w (Fin.castLE hrm kstar)| - ((m : ℝ) - 1) * η * V := by linarith [hdlow]
      _ ≤ |(A *ᵥ w) (Fin.castLE hrn kstar)| := hrow
  -- trailing rows ≤ m η V ≤ γ V
  have hmηV_le_γV : (m : ℝ) * η * V ≤ γ * V := by
    have hmar : (m : ℝ) * η ≤ γ := by have := hA.hmargin; rw [hγdef]; nlinarith [hA.hη]
    exact mul_le_mul_of_nonneg_right hmar hVpos
  -- every OUTPUT coord ≤ γ·V (leading rows via ≤; trailing rows via the trail bound)
  -- but for LeadCert we need ALL coords ≤ some W and a leading coord ≥ that W.  Take W := leading max.
  obtain ⟨kmax, -, hkmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin r))
    (fun k : Fin r => |(A *ᵥ w) (Fin.castLE hrn k)|)
  have hkmax_max : ∀ k : Fin r,
      |(A *ᵥ w) (Fin.castLE hrn k)| ≤ |(A *ᵥ w) (Fin.castLE hrn kmax)| := by
    intro k; rw [← hkmax]
    exact Finset.le_sup' (fun k : Fin r => |(A *ᵥ w) (Fin.castLE hrn k)|) (Finset.mem_univ k)
  have hWge : γ * V ≤ |(A *ᵥ w) (Fin.castLE hrn kmax)| := le_trans hlead (hkmax_max kstar)
  refine ⟨|(A *ᵥ w) (Fin.castLE hrn kmax)|, hWge, fun idx => ?_, kmax, le_refl _⟩
  -- every output coord ≤ the leading max `W`
  by_cases hidx : (idx : ℕ) < r
  · have hk' : idx = Fin.castLE hrn (⟨idx, hidx⟩ : Fin r) := by apply Fin.ext; rfl
    rw [hk']; exact hkmax_max _
  · have hge : (r : ℕ) ≤ (idx : ℕ) := by omega
    exact le_trans (le_trans (trailRow_ub hrn hrm hA w hVall idx hge) hmηV_le_γV) hWge

/-! ### The chain terminal: `LeadCert` with a positive value ⟹ nonzero ⟹ injective -/

/-- **A `LeadCert` with positive value forces the vector nonzero.** Some leading coord has
`|w (castLE k)| ≥ V > 0`, so `w ≠ 0`. -/
theorem LeadCert.ne_zero {m r : ℕ} {hrm : r ≤ m} {w : Fin m → ℝ} {V : ℝ}
    (h : LeadCert hrm w V) (hV : 0 < V) : w ≠ 0 := by
  obtain ⟨-, k, hk⟩ := h
  intro hw
  rw [hw] at hk
  simp only [Pi.zero_apply, abs_zero] at hk
  linarith

/-- **The base `LeadCert` of a zero-padded embedding.** For `x : Fin r → ℝ` embedded into `Fin m` as
the leading coords (`x` on `Fin r`, `0` on the tail), with `V := ⨆|x|` attained at `x`'s own argmax:
the embedding carries `LeadCert hrm (embed x) V`. Here `embed x j = if h : (j:ℕ) < r then x ⟨j,h⟩ else 0`.
-/
theorem leadCert_embed {m r : ℕ} (hrm : r ≤ m) [Nonempty (Fin r)] (x : Fin r → ℝ)
    (embed : Fin m → ℝ)
    (hembed_lead : ∀ k : Fin r, embed (Fin.castLE hrm k) = x k)
    (hembed_tail : ∀ j : Fin m, (r : ℕ) ≤ (j : ℕ) → embed j = 0) :
    ∃ V : ℝ, LeadCert hrm embed V ∧ (x ≠ 0 → 0 < V) := by
  classical
  obtain ⟨kmax, -, hkmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin r))
    (fun k : Fin r => |x k|)
  refine ⟨|x kmax|, ⟨fun j => ?_, kmax, ?_⟩, fun hx => ?_⟩
  · -- every embed coord ≤ |x kmax|
    by_cases hj : (j : ℕ) < r
    · have hk' : j = Fin.castLE hrm (⟨j, hj⟩ : Fin r) := by apply Fin.ext; rfl
      rw [hk', hembed_lead, ← hkmax]
      exact Finset.le_sup' (fun k : Fin r => |x k|) (Finset.mem_univ _)
    · rw [hembed_tail j (by omega)]; simp
  · rw [hembed_lead]
  · -- x ≠ 0 ⟹ |x kmax| = ⨆|x| > 0
    by_contra hle
    have hxk : |x kmax| ≤ 0 := not_lt.mp hle
    apply hx
    funext k
    have : |x k| ≤ |x kmax| := by rw [← hkmax]; exact Finset.le_sup' (fun k : Fin r => |x k|) (Finset.mem_univ _)
    have : |x k| = 0 := le_antisymm (le_trans this hxk) (abs_nonneg _)
    simpa using this

/-- **`mulVec` injectivity from a `LeadCert` with positive value on every nonzero input.** If for every
`x : Fin r → ℝ`, `x ≠ 0`, the vector `P.mulVec x` carries a `LeadCert` with a POSITIVE value, then
`P.mulVec` is injective (linear map with trivial kernel: `P.mulVec x = 0` forces `x = 0` since a
`LeadCert` with `V > 0` gives `P.mulVec x ≠ 0`). -/
theorem mulVec_injective_of_leadCert {m r : ℕ} (P : Matrix (Fin m) (Fin r) ℝ) (hrm : r ≤ m)
    (hcert : ∀ x : Fin r → ℝ, x ≠ 0 → ∃ V : ℝ, 0 < V ∧ LeadCert hrm (P.mulVec x) V) :
    Function.Injective P.mulVec := by
  intro x y hxy
  by_contra hne
  have hxyne : x - y ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  obtain ⟨V, hV, hcertxy⟩ := hcert (x - y) hxyne
  -- P.mulVec (x - y) = P.mulVec x - P.mulVec y = 0
  have hzero : P.mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact (hcertxy.ne_zero hV) hzero

/-! ## The end-to-end brick: `det(P₁ᵀP₁) ≠ 0` from the per-factor certificate

The complete RectVarah chain packaged: given the per-factor `LeadCert` chain producing a positive
value on every nonzero input, `det(P₁ᵀP₁) ≠ 0`. The plumbing supplies `hcert` by threading
`leadCert_embed` (base) through `factorStep` (one per factor) — each `factorStep` scales the value by a
positive `γⱼ`, so the terminal value stays positive. -/

/-- **`det(P₁ᵀP₁) ≠ 0` from a positive-value `LeadCert` on every nonzero input** — the RectVarah chain
endpoint. Combines `mulVec_injective_of_leadCert` (injectivity) with `gram_det_ne_of_mulVec_injective`
(the PosDef endgame). This is the shape the smeared chart's `hUpos`/`det P₁ ≠ 0` field consumes at
`L ≥ 3`: the front product `P₁` is rectangular, and `det(P₁ᵀP₁) ≠ 0` follows from the leading-block
dominance chain (the plumbing builds `hcert` from `leadCert_embed` + a `factorStep` per front factor). -/
theorem frontGram_det_ne_of_leadCert {m r : ℕ} (P : Matrix (Fin m) (Fin r) ℝ) (hrm : r ≤ m)
    (hcert : ∀ x : Fin r → ℝ, x ≠ 0 → ∃ V : ℝ, 0 < V ∧ LeadCert hrm (P.mulVec x) V) :
    (Pᵀ * P).det ≠ 0 :=
  gram_det_ne_of_mulVec_injective P (mulVec_injective_of_leadCert P hrm hcert)

/-! ## Non-vacuity: the brick THREADS on the `(2,3,1,2,1)` front shape (`r = 1`, 3 factors)

The bedrock companion: the chain closes end-to-end on the sharpest surface — the `(2,3,1,2,1)` front
product `P₁ = A⁰·A¹·A²[:, :1]` (shapes `2×3`, `3×1`, `1×2`), the one case with BOTH a WIDE front factor
(`A¹` has 3 rows) and an INTERIOR bottleneck (the width-1 passthrough at `A²`'s row / `A¹`'s column,
`= r`). Threads `leadCert_embed` (base, `Fin 1 ↪ Fin 2`) through `factorStep ×3` (each scales the
value by a positive `γⱼ`) into `frontGram_det_ne_of_leadCert`. This mirrors exactly what the
opaque-width plumbing does. -/

/-- **Non-vacuity — `det(P₁ᵀP₁) ≠ 0` on the `(2,3,1,2,1)` front shape.** The RectVarah chain closes on
the wide-factor + interior-bottleneck case, from per-factor `FactorDominant` of `A⁰,A¹,A²`. -/
theorem frontGram_det_ne_231
    (A0 : Matrix (Fin 2) (Fin 3) ℝ) (A1 : Matrix (Fin 3) (Fin 1) ℝ) (A2 : Matrix (Fin 1) (Fin 2) ℝ)
    {d η : ℝ}
    (hA0 : FactorDominant (by norm_num : (1:ℕ) ≤ 2) (by norm_num : (1:ℕ) ≤ 3) A0 d η)
    (hA1 : FactorDominant (by norm_num : (1:ℕ) ≤ 3) (by norm_num : (1:ℕ) ≤ 1) A1 d η)
    (hA2 : FactorDominant (by norm_num : (1:ℕ) ≤ 1) (by norm_num : (1:ℕ) ≤ 2) A2 d η) :
    (((A0 * A1 * A2).submatrix (id : Fin 2 → Fin 2) (Fin.castLE (by norm_num : (1:ℕ) ≤ 2)))ᵀ *
      ((A0 * A1 * A2).submatrix (id : Fin 2 → Fin 2)
        (Fin.castLE (by norm_num : (1:ℕ) ≤ 2)))).det ≠ 0 := by
  set P₁ := (A0 * A1 * A2).submatrix (id : Fin 2 → Fin 2)
    (Fin.castLE (by norm_num : (1:ℕ) ≤ 2)) with hP₁
  refine frontGram_det_ne_of_leadCert P₁ (by norm_num : (1:ℕ) ≤ 2) (fun x hx => ?_)
  haveI : Nonempty (Fin 1) := ⟨0⟩
  set embed : Fin 2 → ℝ := fun j => if h : (j : ℕ) < 1 then x ⟨j, h⟩ else 0 with hembed
  obtain ⟨V0, hcert0, hV0pos⟩ := leadCert_embed (by norm_num : (1:ℕ) ≤ 2) x embed
    (fun k => by
      simp only [hembed]
      rw [dif_pos (show ((Fin.castLE (by norm_num : (1:ℕ) ≤ 2) k : Fin 2) : ℕ) < 1 by
        simpa using k.2)]
      congr 1)
    (fun j hj => by simp only [hembed]; rw [dif_neg (by omega)])
  obtain ⟨W2, hW2ge, hcert2⟩ :=
    factorStep (by norm_num : (1:ℕ) ≤ 1) (by norm_num : (1:ℕ) ≤ 2) hA2 hcert0
  obtain ⟨W1, hW1ge, hcert1⟩ :=
    factorStep (by norm_num : (1:ℕ) ≤ 3) (by norm_num : (1:ℕ) ≤ 1) hA1 hcert2
  obtain ⟨W0, hW0ge, hcert3⟩ :=
    factorStep (by norm_num : (1:ℕ) ≤ 2) (by norm_num : (1:ℕ) ≤ 3) hA0 hcert1
  -- A0·A1·A2·embed = P₁·x  (fold mulVec chain; embed = zero-padded x)
  have hcompose : A0 *ᵥ A1 *ᵥ A2 *ᵥ embed = P₁.mulVec x := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP₁]
    ext i
    simp only [Matrix.mulVec, Matrix.submatrix_apply, dotProduct, id_eq]
    rw [Fin.sum_univ_two, Fin.sum_univ_one]
    simp only [hembed]
    rw [show ((0 : Fin 2) : ℕ) = 0 from rfl, show ((1 : Fin 2) : ℕ) = 1 from rfl,
      dif_pos (by norm_num : (0:ℕ) < 1), dif_neg (by norm_num : ¬ (1:ℕ) < 1)]
    simp only [mul_zero, add_zero]
    congr 1
  -- positivity: each γⱼ > 0 from the margin + d > 0, and V0 > 0
  have hγ2s : 0 < d / 2 - (((2:ℕ):ℝ) - 1) * η := by
    have := hA2.hmargin; push_cast at this ⊢; nlinarith [hA2.hη, hA2.hd]
  have hγ1s : 0 < d / 2 - (((1:ℕ):ℝ) - 1) * η := by
    have := hA1.hmargin; push_cast at this ⊢; nlinarith [hA1.hη, hA1.hd]
  have hγ0s : 0 < d / 2 - (((3:ℕ):ℝ) - 1) * η := by
    have := hA0.hmargin; push_cast at this ⊢; nlinarith [hA0.hη, hA0.hd]
  refine ⟨W0, ?_, hcompose ▸ hcert3⟩
  have h2 : 0 < W2 := lt_of_lt_of_le (mul_pos hγ2s (hV0pos hx)) hW2ge
  have h1 : 0 < W1 := lt_of_lt_of_le (mul_pos hγ1s h2) hW1ge
  exact lt_of_lt_of_le (mul_pos hγ0s h1) hW0ge

end DLNFibre.Core.Matrix

-- Forced axiom check (FORCES elaboration; per lean/CLAUDE.md the build's exit-0 can mask a sorryAx).
section AxCheck
open DLNFibre.Core.Matrix
#print axioms gram_det_ne_of_mulVec_injective
#print axioms factorStep
#print axioms leadCert_embed
#print axioms mulVec_injective_of_leadCert
#print axioms frontGram_det_ne_of_leadCert
#print axioms frontGram_det_ne_231
end AxCheck
