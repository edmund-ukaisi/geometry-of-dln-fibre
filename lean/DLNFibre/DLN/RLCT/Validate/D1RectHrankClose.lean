import DLNFibre.DLN.RLCT.Validate.D1JointDiffRankExact
import DLNFibre.DLN.RLCT.Validate.D1RectValueArith

/-!
# `D1RectHrankClose` — the exact-rank arithmetic closing `hrank₂` above b3

Combines the exact joint-differential rank (b3, `jacFlatL2_rank_eq`) with Sylvester's inequality
(`rank_add_rank_le_rank_mul_add_middle`) and the layer-rank bounds at an optimal `v` to prove the
honest-subtraction arithmetic identity

    (jacFlatL2 H v).rank − nRegL2 H r = extraCountRect (H0−r) (H2−r) a b,

with `a = (v 0).rank − r` (FRONT layer-rank rise) and `b = (v 1).rank − r` (BACK layer-rank rise).
This is the count the `hrank₂` gate of `d1ge_L2_rect_two_peel` needs (once `residJacobian_rank_eq`
supplies `rank(jacResid) = jacFlatL2.rank − nReg`). The gate's honest-subtraction hypotheses
`a ≤ H0−r`, `a + b ≤ H1−r` (Sylvester), `b ≤ H2−r` are all derived here from `v` at a valid stratum.

Scope L = 2 (`H : Fin 3 → ℕ`).
-/

open Matrix Module
namespace DLNFibre.DLN.RLCT

/-- The FRONT layer-rank rise of an optimal `v`: `a = rank(v⁰) − r`. -/
noncomputable def frontRise (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H) : ℕ :=
  (layer0 H v).rank - r
/-- The BACK layer-rank rise of an optimal `v`: `b = rank(v¹) − r`. -/
noncomputable def backRise (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H) : ℕ :=
  (layer1 H v).rank - r

/-! ## The layer-rank facts at an optimal `v` -/

/-- **`r ≤ rank(v⁰)` and `r ≤ rank(v¹)`.** From `rank(prod v) = rank(v⁰·v¹) = r ≤ min ranks`. -/
theorem r_le_layer_ranks (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (hr : (prod H v).rank = r) :
    r ≤ (layer0 H v).rank ∧ r ≤ (layer1 H v).rank := by
  have hprod : prod H v = layer0 H v * layer1 H v := prod_eq_layerMul H v
  have h0 : (prod H v).rank ≤ (layer0 H v).rank := by
    rw [hprod]; exact Matrix.rank_mul_le_left _ _
  have h1 : (prod H v).rank ≤ (layer1 H v).rank := by
    rw [hprod]; exact Matrix.rank_mul_le_right _ _
  exact ⟨hr ▸ h0, hr ▸ h1⟩

/-- **Sylvester at the layers:** `rank(v⁰) + rank(v¹) ≤ H1 + r`. From
`rank(v⁰) + rank(v¹) ≤ rank(v⁰·v¹) + H1 = r + H1`. -/
theorem layer_ranks_sylvester (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (hr : (prod H v).rank = r) :
    (layer0 H v).rank + (layer1 H v).rank ≤ H 1 + r := by
  have hprodrank : (layer0 H v * layer1 H v).rank = r := by
    rw [← prod_eq_layerMul H v]; exact hr
  have hsyl := rank_add_rank_le_rank_mul_add_middle (layer0 H v) (layer1 H v)
  rw [hprodrank] at hsyl
  omega

/-! ## The exact-rank arithmetic close -/

/-- **The exact `hrank₂` count above b3.** At an optimal `v` (`prod v = B`, `rank B = r`), with
`a = rank(v⁰) − r`, `b = rank(v¹) − r`:

    (jacFlatL2 H v).rank − nRegL2 H r = extraCountRect (H0−r) (H2−r) a b.

b3 (`jacFlatL2_rank_eq`) gives the exact `jacFlatL2` rank; the layer-rank facts (`r ≤ rank(v⁰)`,
`r ≤ rank(v¹)`, Sylvester, and the width bounds) make the honest ℕ subtraction close by `omega`. -/
theorem jacFlatL2_rank_sub_nReg_eq_extraCountRect (H : Fin (2 + 1) → ℕ) (r : ℕ) (v : Params H)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ) (hopt : prod H v = B) (hB : B.rank = r) :
    (jacFlatL2 H v).rank - nRegL2 H r
      = extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v) := by
  have hrankprod : (prod H v).rank = r := by rw [hopt, hB]
  obtain ⟨hr0, hr1⟩ := r_le_layer_ranks H r v hrankprod
  have hsyl := layer_ranks_sylvester H r v hrankprod
  -- width bounds on the layer ranks
  have hb0H0 : (layer0 H v).rank ≤ H 0 := Matrix.rank_le_height _
  have hb1H2 : (layer1 H v).rank ≤ H 2 := Matrix.rank_le_width _
  -- b3: exact `jacFlatL2` rank; nReg / extraCountRect unfold (codomain `H (Fin.last 2) = H 2`).
  have hjac := jacFlatL2_rank_eq H v
  have hnReg : nRegL2 H r = r * (H 0 + H 2 - r) := rfl
  have hfr : frontRise H r v = (layer0 H v).rank - r := rfl
  have hbr : backRise H r v = (layer1 H v).rank - r := rfl
  have hecr : extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)
      = (frontRise H r v) * (H 2 - r) + (backRise H r v) * (H 0 - r)
        - (frontRise H r v) * (backRise H r v) := rfl
  rw [hjac, hnReg, hecr, hfr, hbr]
  -- `r ≤ H0`, `r ≤ H2`.
  have hrH0 : r ≤ H 0 := le_trans hr0 hb0H0
  have hrH2 : r ≤ H 2 := le_trans hr1 hb1H2
  -- write `rk0 = r + a`, `rk1 = r + b`, and `H0 = r + a + c0`, `H2 = r + b + c2` (all honest);
  -- then EVERY nat subtraction vanishes and the identity is pure `ring` on ℕ.
  obtain ⟨a, ha⟩ : ∃ a, (layer0 H v).rank = r + a := ⟨(layer0 H v).rank - r, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, (layer1 H v).rank = r + b := ⟨(layer1 H v).rank - r, by omega⟩
  obtain ⟨c0, hc0⟩ : ∃ c0, H 0 = r + a + c0 := ⟨H 0 - r - a, by omega⟩
  obtain ⟨c2, hc2⟩ : ∃ c2, H 2 = r + b + c2 := ⟨H 2 - r - b, by omega⟩
  rw [ha, hb, hc0, hc2]
  -- with `H0 = r+a+c0`, `H2 = r+b+c2` every nat subtraction is honest. Simplify the inner
  -- subtractions, then abstract the four products as opaque atoms for `omega` (the equation is
  -- LINEAR in those atoms; the products' defining relations are the `hprod*` hypotheses).
  have h2' : r + b + c2 - r = b + c2 := by omega
  have h0' : r + a + c0 - r = a + c0 := by omega
  have hmid : r + a + c0 + (r + b + c2) - r = a + c0 + (r + b + c2) := by omega
  have hra : r + a - r = a := by omega
  have hrb : r + b - r = b := by omega
  rw [h2', h0', hmid, hra, hrb]
  -- the products and their expansions (so omega sees the cross-terms as equal atoms).
  have p1 : (r + a + c0) * (r + b) = r*r + r*b + a*r + a*b + c0*r + c0*b := by ring
  have p2 : (r + a) * (r + b + c2) = r*r + r*b + r*c2 + a*r + a*b + a*c2 := by ring
  have p3 : (r + a) * (r + b) = r*r + r*b + a*r + a*b := by ring
  have p4 : r * (a + c0 + (r + b + c2)) = r*a + r*c0 + r*r + r*b + r*c2 := by ring
  have p5 : a * (b + c2) = a*b + a*c2 := by ring
  have p6 : b * (a + c0) = a*b + b*c0 := by ring
  rw [p1, p2, p3, p4, p5, p6]
  -- normalise commutative products so equal atoms match, then omega on the linear atom-equation.
  simp only [Nat.mul_comm]
  omega

end DLNFibre.DLN.RLCT
