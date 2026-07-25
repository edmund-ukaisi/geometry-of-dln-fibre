import DLNFibre.DLN.Aoyagi.LeafCoverTiling

/-!
# `DLN.Aoyagi.Corank2FaithfulHCover` — the FAITHFUL corank-2 L7 `hcover` atom

The L7 measure-zero cover for the **faithful** multi-term corank-2 Schur-clearing shear — rung 5c of
the (3,3,4) Resolution (`hcover-elaboration.md`, OBL-1). Where `Corank2GeoAtlas.coShear` uses the
**Schur update only** (`Δ = C₂₂ − c₂₁⊗c₁₂`, ONE product per corrected slot), the *faithful* per-node
shear additionally carries the **Lemma-2 recoord** `C₂' = Q₂⁻¹ C₂` (the pivot-row combine). The
recoord is `Q₂⁻¹ = I − N` with `N` the single pivot-row block (`N² = 0`, DEGREE 1), so each recoord
entry is a degree-2 product too — the faithful shear is MULTI-TERM (up to `C = block-size` products
per corrected slot) but still DEGREE EXACTLY 2, coefficients ±1. At corank 2, `C = 2`.

**What is REUSED verbatim.** The entire `LeafCoverTiling` engine (`FanTree`, `Covers`,
`covers_subset`, `exists_ball_subset_leafImages`, the argmax block-atom) is generic in the inflation
`f : ℝ → ℝ` and the per-node shear `σ`; it is fed a faithful shear here without change. The real
`blockShear`/`blockShearInv` bijection machinery (`PathAtoms`) is reused too.

**What is NEW (detail-at-scale, this file).**
* `faithfulShear = blockShear faithfulPhi` — the FULL faithful shear on `Fin 14`: the 4 Schur block
  slots `{4,5,6,7}` (ONE product each) PLUS the 2 genuine `Q₂⁻¹` recoord slots `{8,9}` (TWO products
  each). This is the object the go/no-go adjudicated (DETAIL-AT-SCALE, GO), NOT a single-term proxy.
* `faithfulShear_covers` — the per-edge box-containment `closedBall 0 r ⊆ faithfulShear ''
  closedBall 0 (r + 2·r²)` under the `C = 2` inflation `f = r ↦ r + 2·r²`. Same proof shape as
  `Corank2GeoAtlas.coShear_covers`, with the two extra recoord branches carrying the `≤ 2·r²` bound.
* `covers_faithfulTree` — the depth-2, `|S| = 2` acceptance witness `Covers (r ↦ r + 2·r²) · 1`,
  leaf box `closedBall 0 21 = f^[2] 1` (`f 1 = 3`, `f 3 = 21`).

**Coordinate layout on `Fin 14`** (block `2×2`, downstream width `w = 2`).
`0,1 = c₁₂` (pivot column, kept), `2,3 = c₂₁` (pivot row, kept), `4,5,6,7 = C₂₂` (residual block,
written — Schur), `8,9 = s_{0,·}` (downstream pivot-row slot, written — recoord), `10,11 = s_{1,·}`
and `12,13 = s_{2,·}` (downstream non-pivot rows, kept + read by the recoord). Kept = read = fixed
set `{0,1,2,3, 10,11,12,13}`; written = `{4,5,6,7, 8,9}` — disjoint (a valid unipotent shear). All
exactly per the decorrelated exact-algebra probe (`/tmp/probe_hcover_obl1.py`, corank-2: valid
unipotent, degree 2, exact inverse `v ↦ v − φ v`, C = 2).

**Scope (no over-claim).** This is the L7 `hcover`-contribution for the *faithful* corank-2 fan (the
per-edge box-containment + the assembled fan cover). It does NOT rebuild the L6 Jacobian side (that
is `Corank2GeoAtlas.coG_hjac`, shear-independent up to `jacDet (blockShear _) ≡ 1`).
-/

open MeasureTheory Set Filter Topology Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.LeafCoverTiling

namespace DLNFibre.DLN.Aoyagi.Corank2FaithfulHCover

/-! ## §1 — the faithful corank-2 shear `faithfulShear = blockShear faithfulPhi` -/

/-- The kept coordinate set `{0,1,2,3, 10,11,12,13}` (pivot column + row, and the downstream
non-pivot rows): the shear FIXES + READS only these. The written slots are `{4,…,9}`. -/
def faithfulKeep : Fin 14 → Prop := fun i ↦ i.val < 4 ∨ 10 ≤ i.val

/-- The **faithful** corank-2 displacement. The 4 Schur block slots `{4,5,6,7}` carry the rank-1
update `−c₂₁ ⊗ c₁₂` (ONE product each), and the 2 recoord slots `{8,9}` carry the genuine `Q₂⁻¹`
pivot-row combine `+ r₀·s_{1,·} + r₁·s_{2,·}` (TWO products each) — the `C = 2` multi-term
structure. Vanishes on the kept set. -/
def faithfulPhi (x : Fin 14 → ℝ) : Fin 14 → ℝ := fun i ↦
  if i = 4 then - (x 0 * x 2)
  else if i = 5 then - (x 1 * x 2)
  else if i = 6 then - (x 0 * x 3)
  else if i = 7 then - (x 1 * x 3)
  else if i = 8 then x 2 * x 10 + x 3 * x 12
  else if i = 9 then x 2 * x 11 + x 3 * x 13
  else 0

/-- The faithful corank-2 chart shear `faithfulShear = blockShear faithfulPhi`
(`u ↦ u + faithfulPhi u`). -/
def faithfulShear : (Fin 14 → ℝ) → (Fin 14 → ℝ) := blockShear faithfulPhi

/-- `faithfulPhi` fixes the origin. -/
theorem faithfulPhi_zero : faithfulPhi (0 : Fin 14 → ℝ) = 0 := by
  funext i
  simp only [faithfulPhi, Pi.zero_apply, mul_zero, add_zero, neg_zero, ite_self]

/-- `faithfulPhi` VANISHES on the kept set — the `hkeep` clause for the shear. -/
theorem faithfulPhi_keep (u : Fin 14 → ℝ) (i : Fin 14) (hi : faithfulKeep i) :
    faithfulPhi u i = 0 := by
  simp only [faithfulKeep] at hi
  have h4 : i ≠ 4 := by rintro rfl; omega
  have h5 : i ≠ 5 := by rintro rfl; omega
  have h6 : i ≠ 6 := by rintro rfl; omega
  have h7 : i ≠ 7 := by rintro rfl; omega
  have h8 : i ≠ 8 := by rintro rfl; omega
  have h9 : i ≠ 9 := by rintro rfl; omega
  simp [faithfulPhi, h4, h5, h6, h7, h8, h9]

/-- `faithfulPhi` READS ONLY the kept set — the `hread` clause for the shear. -/
theorem faithfulPhi_read (u v : Fin 14 → ℝ) (h : ∀ i, faithfulKeep i → u i = v i) :
    faithfulPhi u = faithfulPhi v := by
  have e0 : u 0 = v 0 := h 0 (by simp [faithfulKeep])
  have e1 : u 1 = v 1 := h 1 (by simp [faithfulKeep])
  have e2 : u 2 = v 2 := h 2 (by simp [faithfulKeep])
  have e3 : u 3 = v 3 := h 3 (by simp [faithfulKeep])
  have e10 : u 10 = v 10 := h 10 (by simp [faithfulKeep])
  have e11 : u 11 = v 11 := h 11 (by simp [faithfulKeep])
  have e12 : u 12 = v 12 := h 12 (by simp [faithfulKeep])
  have e13 : u 13 = v 13 := h 13 (by simp [faithfulKeep])
  funext i
  simp only [faithfulPhi]
  rw [e0, e1, e2, e3, e10, e11, e12, e13]

/-! ## §2 — shear-level facts (origin-fixing, analytic, injective) -/

/-- `faithfulShear` fixes the origin. -/
theorem faithfulShear_zero : faithfulShear (0 : Fin 14 → ℝ) = 0 :=
  blockShear_zero faithfulPhi faithfulPhi_zero

/-- `faithfulShear` is injective (a bijection with inverse `blockShearInv faithfulPhi`). -/
theorem injective_faithfulShear : Function.Injective faithfulShear :=
  injective_blockShear faithfulPhi faithfulKeep faithfulPhi_keep faithfulPhi_read

/-! ## §3 — L7 obligation-1: the per-edge box-containment for the FAITHFUL shear

The un-probed crux (now adjudicated). The faithful shear has SIX written coordinates: 4 Schur block
slots (ONE product each, `≤ r²`) and 2 recoord slots (TWO products each, `≤ 2·r²`). The inflation is
`f = r ↦ r + 2·r²` (`C = 2`), driven by the recoord slots; the block slots satisfy the stronger
`r + r² ≤ r + 2·r²`. -/

/-- **L7 obligation-1 (corank-2 FAITHFUL).** `closedBall 0 r ⊆ faithfulShear '' closedBall 0
(r + 2·r²)` — the per-edge box-containment for the faithful multi-term Schur-clearing shear, under
the `C = 2` inflation `f = r ↦ r + 2·r²`. The preimage of `x` is `blockShearInv faithfulPhi x =
x − faithfulPhi x`; each coordinate is either `x i` (kept, `≤ r`), `x i ± (one product)` (Schur,
`≤ r + r²`), or `x i ± (two products)` (recoord, `≤ r + 2·r²`). This is the exact clause the
`LeafCoverTiling` engine's `Covers` fold consumes per node — the faithful multi-term geometry does
NOT open a box-containment the single-term template misses (the degree stays 2). -/
theorem faithfulShear_covers {r : ℝ} (hr : 0 ≤ r) :
    closedBall (0 : Fin 14 → ℝ) r ⊆ faithfulShear '' closedBall 0 (r + 2 * r ^ 2) := by
  have hrr : (0 : ℝ) ≤ r + 2 * r ^ 2 := by positivity
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hx
  have hb : ∀ i, |x i| ≤ r := fun i ↦ by rw [← Real.norm_eq_abs]; exact hx i
  -- the bilinear bound: `|x a · x b| ≤ r²` (each factor `≤ r`)
  have hbil : ∀ a b : Fin 14, |x a * x b| ≤ r ^ 2 := by
    intro a b; rw [abs_mul, sq]; exact mul_le_mul (hb a) (hb b) (abs_nonneg _) hr
  refine ⟨blockShearInv faithfulPhi x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hrr]
    intro i
    rw [Real.norm_eq_abs]
    simp only [blockShearInv, Pi.sub_apply]
    -- Schur block slot 4 (ONE product)
    by_cases hi4 : i = 4
    · subst hi4
      have h4 := abs_le.mp (hb 4); have hp := abs_le.mp (hbil 0 2)
      change |x 4 - -(x 0 * x 2)| ≤ r + 2 * r ^ 2
      rw [abs_le]; exact ⟨by nlinarith [h4.1, hp.1, hp.2, sq_nonneg r],
        by nlinarith [h4.2, hp.1, hp.2, sq_nonneg r]⟩
    · by_cases hi5 : i = 5
      · subst hi5
        have h5 := abs_le.mp (hb 5); have hp := abs_le.mp (hbil 1 2)
        change |x 5 - -(x 1 * x 2)| ≤ r + 2 * r ^ 2
        rw [abs_le]; exact ⟨by nlinarith [h5.1, hp.1, hp.2, sq_nonneg r],
          by nlinarith [h5.2, hp.1, hp.2, sq_nonneg r]⟩
      · by_cases hi6 : i = 6
        · subst hi6
          have h6 := abs_le.mp (hb 6); have hp := abs_le.mp (hbil 0 3)
          change |x 6 - -(x 0 * x 3)| ≤ r + 2 * r ^ 2
          rw [abs_le]; exact ⟨by nlinarith [h6.1, hp.1, hp.2, sq_nonneg r],
            by nlinarith [h6.2, hp.1, hp.2, sq_nonneg r]⟩
        · by_cases hi7 : i = 7
          · subst hi7
            have h7 := abs_le.mp (hb 7); have hp := abs_le.mp (hbil 1 3)
            change |x 7 - -(x 1 * x 3)| ≤ r + 2 * r ^ 2
            rw [abs_le]; exact ⟨by nlinarith [h7.1, hp.1, hp.2, sq_nonneg r],
              by nlinarith [h7.2, hp.1, hp.2, sq_nonneg r]⟩
          -- recoord slot 8 (TWO products): the genuine multi-term `Q₂⁻¹` combine
          · by_cases hi8 : i = 8
            · subst hi8
              have h8 := abs_le.mp (hb 8)
              have hp1 := abs_le.mp (hbil 2 10); have hp2 := abs_le.mp (hbil 3 12)
              change |x 8 - (x 2 * x 10 + x 3 * x 12)| ≤ r + 2 * r ^ 2
              rw [abs_le]
              exact ⟨by linarith [h8.1, hp1.2, hp2.2], by linarith [h8.2, hp1.1, hp2.1]⟩
            · by_cases hi9 : i = 9
              · subst hi9
                have h9 := abs_le.mp (hb 9)
                have hp1 := abs_le.mp (hbil 2 11); have hp2 := abs_le.mp (hbil 3 13)
                change |x 9 - (x 2 * x 11 + x 3 * x 13)| ≤ r + 2 * r ^ 2
                rw [abs_le]
                exact ⟨by linarith [h9.1, hp1.2, hp2.2], by linarith [h9.2, hp1.1, hp2.1]⟩
              -- kept coords: displacement is 0
              · have hc0 : faithfulPhi x i = 0 := by
                  simp [faithfulPhi, hi4, hi5, hi6, hi7, hi8, hi9]
                rw [hc0, sub_zero]
                exact (hb i).trans (le_add_of_nonneg_right (by positivity))
  · change blockShear faithfulPhi (blockShearInv faithfulPhi x) = x
    exact blockShearInv_rightInverse faithfulPhi faithfulKeep faithfulPhi_keep faithfulPhi_read x

/-! ## §4 — L7 obligation-2 + assembly: the FAITHFUL fan closes `hcover` via `LeafCoverTiling`

Fed to the (verbatim-reused) engine, a depth-2, `|S| = 2` fan with the faithful shear at BOTH levels
closes `Covers (r ↦ r + 2·r²) · 1`. Leaf box `closedBall 0 21 = f^[2] 1` (`f 1 = 3`, `f 3 = 21`) —
the finite-depth inflation of the `C = 2` box. The genuine multi-term shear does not fight: the
engine's
argmax fan-completeness + this box-containment assemble the cover. -/

/-- A depth-2, `|S| = 2` fan tree with the genuine FAITHFUL corank-2 shear `faithfulShear` at both
levels (center `{0,1}`, leaf box `closedBall 0 21 = f^[2] 1` for `f = r ↦ r + 2·r²`). -/
def faithfulTree : FanTree 14 :=
  FanTree.node {0, 1} ⟨0, by decide⟩ (fun _ ↦ faithfulShear)
    (fun _ ↦ FanTree.node {0, 1} ⟨0, by decide⟩ (fun _ ↦ faithfulShear)
      (fun _ ↦ FanTree.leaf (closedBall 0 21)))

/-- **L7 (corank-2 FAITHFUL) — the fan closes.** `Covers (r ↦ r + 2·r²) faithfulTree 1`: the
per-edge shear clause is `faithfulShear_covers` (§3) at each of the two levels, and the leaf box
`closedBall 0 21` covers the twice-inflated radius `f (max 3 1) = f 3 = 21`. Structurally identical
to the `covers_coTree`/`covers_qtree`/`covers_cexTree` acceptance witnesses, but with the genuine
multi-term (`C = 2`) faithful Schur-clearing shear — the un-probed crux, now closed. -/
theorem covers_faithfulTree : FanTree.Covers (fun r ↦ r + 2 * r ^ 2) faithfulTree 1 :=
  ⟨fun _ _ ↦ faithfulShear_covers (zero_le_one.trans (le_max_right _ 1)),
    fun _ _ ↦ ⟨fun _ _ ↦ faithfulShear_covers (zero_le_one.trans (le_max_right _ 1)),
      fun _ _ ↦ Metric.closedBall_subset_closedBall (by norm_num)⟩⟩

/-- **The faithful corank-2 cover — the `hcover` contribution.** The closed unit ball is covered by
the faithful fan's leaf-chart images (`FanTree.covers_subset`). -/
theorem closedBall_subset_faithfulTree_leafImages :
    closedBall (0 : Fin 14 → ℝ) 1 ⊆ faithfulTree.leafImages :=
  FanTree.covers_subset faithfulTree covers_faithfulTree

/-- **The punctured-neighbourhood cover shape** (`∃ ρ > 0`) the atlas `hcover` consumes, for the
faithful corank-2 leaf — obligations 1+2 assembled, no fight. -/
theorem exists_ball_subset_faithfulTree_leafImages :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : Fin 14 → ℝ) ρ ⊆ faithfulTree.leafImages :=
  FanTree.exists_ball_subset_leafImages faithfulTree covers_faithfulTree

/-! ## §5 — the forced axiom gate

The faithful cover results rest only on `[propext, Classical.choice, Quot.sound]` — a future edit
that makes any depend on `sorryAx` FAILS this red (not masked by a stale-olean `exit 0`). -/
#assert_banked_clean_batch [faithfulShear_covers, covers_faithfulTree,
  closedBall_subset_faithfulTree_leafImages, exists_ball_subset_faithfulTree_leafImages]

end DLNFibre.DLN.Aoyagi.Corank2FaithfulHCover
