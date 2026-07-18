import DLNFibre.DLN.RLCT.Foundations.S1Cover

/-!
# `DLNFibre.DLN.RLCT.Engine.PivotCover` — the per-blow-up LOCAL COVERING LEMMA (T3 rung 1)

**Blueprint spine: this statement is a forecast; the proof grind follows a statement review.**

The coverage-theorem's atom (compass fork 12, elder-named): the single uniform blow-up event is
covered by its *pivot charts*. Concretely, the blow-up of `ℝ^d` at the coordinate origin is covered
by its `d` standard affine charts in the **max-modulus normalization**

    pivotChart i u = (fun k => if k = i then u i else u i * u k),

whose Jacobian determinant is `u i ^ (d-1)` (the exceptional divisor `u i`), i.e. exactly Aoyagi's
monomial blow-up chart `β` (`LeafJacobian`, `|det Dβ| = ∏ |u|^{divExp-1}`).

The load-bearing content — the reason coverage is a THEOREM and not an assertion — is that the FULL
residual-`d` family is required: a single fixed "corner" chart misses `{x : x_corner = 0, x ≠ 0}`
(`cert-atlas-probe` Verdict 1(b): `C⁽¹⁾ = [[0,ε],[0,0]]` misses the corner pivot). The cover is
provably NON-TORIC at the tree level, but the per-blow-up ATOM here is the elementary max-modulus
fact: every point of the cube has a coordinate of maximal modulus, and THAT coordinate's pivot chart
reaches it.

`corank ≥ 2` (`d ≥ 2`) is where the corner gap bites; the statement is uniform in `d ≥ 1`.

Numerically sanity-checked (exact rational; reproduces the probe's `(0,ε)` gap witness):
`threads/10-coverage/battery/c-pivot-chart-cover.py` (COVER / BOUND / GAP / JAC).
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT
open Set

variable {d : ℕ}

/-- The `i`-th standard affine blow-up chart of `ℝ^d` at the coordinate origin, in the max-modulus
normalization: the pivot coordinate `i` is free (`u i`), and each other coordinate `k` is the scaled
ratio `u i * u k`. Its Jacobian determinant is `u i ^ (d-1)` — exceptional divisor `{u i = 0}` — so
`pivotChart i` is Aoyagi's monomial blow-up chart `β` (feeds `LeafJacobian`). -/
def pivotChart (i : Fin d) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun k => if k = i then u i else u i * u k

/-- The bounded source box of the `i`-th pivot chart: the pivot `u i` ranges over `[-R, R]`, each
ratio `u k` (`k ≠ i`) over `[-1, 1]`. Bounded in the cube (matches the `ChartBridge` `srcBox`
requirement); the exceptional fibre is `{u i = 0}`. -/
def pivotChartDom (i : Fin d) (R : ℝ) : Set (Fin d → ℝ) :=
  { u | |u i| ≤ R ∧ ∀ k, k ≠ i → |u k| ≤ 1 }

/-- **The per-blow-up LOCAL COVERING LEMMA** (uniform in `d ≥ 1`; content bites at corank `d ≥ 2`).

The `d` standard pivot charts of the origin blow-up of `ℝ^d`, restricted to their bounded domains,
have images whose union is EXACTLY the cube `[-R,R]^d`:
* `⊇` (cover) — the max-modulus argument: every `x` in the cube has a coordinate `i` of maximal
  modulus, and `pivotChart i` reaches `x` from `u = (x i, (x k / x i)ₖ)` inside `pivotChartDom i R`;
* `⊆` (bounded) — each chart image stays in the cube (`|u i · u k| ≤ R·1`).

This is the atom the tree-level cover folds from: a single fixed corner chart does not cover (it
misses `{x : x i = 0, x ≠ 0}`), so the whole residual-`d` family is load-bearing. -/
theorem cubeBox_subset_iUnion_pivotChart_image (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    cubeBox d R ⊆ ⋃ i : Fin d, pivotChart i '' pivotChartDom i R := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  intro x hx
  rw [cubeBox, Set.mem_pi] at hx
  simp only [Set.mem_univ, Set.mem_Icc, forall_true_left] at hx
  have hxabs : ∀ k, |x k| ≤ R := fun k => abs_le.mpr (hx k)
  -- the pivot is a coordinate of maximal modulus
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image Finset.univ (fun k => |x k|) Finset.univ_nonempty
  have hmax : ∀ j, |x j| ≤ |x i| := fun j => hi j (Finset.mem_univ j)
  rw [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  by_cases hxi : x i = 0
  · -- `x = 0`: every coordinate vanishes (modulus ≤ `|x i| = 0`); `u = 0` maps to it
    have hx0 : ∀ k, x k = 0 := by
      intro k
      have hk := hmax k
      rw [hxi, abs_zero] at hk
      exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
    refine ⟨fun _ => 0, ⟨?_, ?_⟩, ?_⟩
    · simpa using hR
    · intro k _; simp
    · funext k
      unfold pivotChart
      by_cases hk : k = i
      · subst hk; simp [hxi]
      · simp [hk, hx0 k]
  · -- `x i ≠ 0`: `u = update (·/x i) i (x i)`; ratios bounded by maximality of `|x i|`
    refine ⟨Function.update (fun k => x k / x i) i (x i), ⟨?_, ?_⟩, ?_⟩
    · rw [Function.update_self]; exact hxabs i
    · intro k hk
      simp only [Function.update_of_ne hk, abs_div]
      rw [div_le_one (abs_pos.mpr hxi)]
      exact hmax k
    · funext k
      unfold pivotChart
      by_cases hk : k = i
      · subst hk; simp [Function.update_self]
      · simp only [if_neg hk, Function.update_self, Function.update_of_ne hk]
        field_simp

/-- **The per-blow-up LOCAL COVERING LEMMA** (uniform in `d ≥ 1`; content bites at corank `d ≥ 2`).
The `d` standard pivot charts of the origin blow-up of `ℝ^d`, on their bounded domains, have images
whose union is EXACTLY the cube `[-R,R]^d`: the `⊇` (cover) half is
`cubeBox_subset_iUnion_pivotChart_image`; the `⊆` (bounded) half is `|u i · u k| ≤ R·1`. -/
theorem iUnion_pivotChart_image_eq_cubeBox (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    ⋃ i : Fin d, pivotChart i '' pivotChartDom i R = cubeBox d R := by
  refine Set.Subset.antisymm ?_ (cubeBox_subset_iUnion_pivotChart_image hd hR)
  rw [Set.iUnion_subset_iff]
  intro i y hy
  obtain ⟨u, ⟨hui, hratio⟩, rfl⟩ := hy
  rw [cubeBox, Set.mem_pi]
  intro k _
  rw [Set.mem_Icc, ← abs_le]
  unfold pivotChart
  by_cases hk : k = i
  · subst hk; simpa using hui
  · simp only [if_neg hk, abs_mul]
    calc |u i| * |u k| ≤ R * 1 := mul_le_mul hui (hratio k hk) (abs_nonneg _) hR
      _ = R := mul_one R

/-- **The corner gap is real** (bedrock: the full family is necessary, not a convenience). At
`corank d = 2`, a single fixed pivot chart does NOT cover: the point `(0, ε)` (`0 < ε`) is NOT in
the image of the corner (pivot-`0`) chart on ANY domain — the pivot coordinate forces `u 0 = 0`,
which zeroes the second coordinate, so `ε` is unreachable. Only the pivot-`1` chart covers it.
Reproduces `cert-atlas-probe` Verdict 1(b) (`C⁽¹⁾ = [[0,ε],[0,0]]` misses the corner pivot). -/
theorem corner_chart_not_cover {ε : ℝ} (hε : 0 < ε) :
    (fun k : Fin 2 => if k = 0 then (0 : ℝ) else ε) ∉
      pivotChart (0 : Fin 2) '' (Set.univ : Set (Fin 2 → ℝ)) := by
  rintro ⟨u, -, hu⟩
  have h0 : u 0 = 0 := by simpa [pivotChart] using congrFun hu 0
  have h1 : u 0 * u 1 = ε := by simpa [pivotChart] using congrFun hu 1
  rw [h0, zero_mul] at h1
  linarith

end DLNFibre.DLN.RLCT.Engine
