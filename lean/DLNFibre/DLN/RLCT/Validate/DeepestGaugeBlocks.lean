import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks` — gauge-slice → Schur block algebra (#44c sub-1)

The **route-independent** matrix-algebra core of `deepest_gauge_chart_exists` (sub-lemma 1,
controller 2026-06-22). Banks regardless of the L2 transport wrapper (squeeze vs chart): the
geometric content that `deepest_gauge_chart_exists` produces and any transport consumes.

## The obligation (g150/g153 cert, refined)

At a rank-`r`-exact deepest point, each layer gauge-slices to `C_s = [[I+X_s, Y_s],[Z_s, T_s]]`. The
loss is `‖∏C_s − D‖²` with `D = blockdiag[I, 0]` (the deepest product value). Block-summing the
Frobenius norm: `loss = ∑(E²) + ‖P11‖²`, `E` = the regular residuals on the `(0,0),(0,1),(1,0)`
blocks, `P11` = the `(1,1)` block of `∏C`.

**The raw-`∏T` core is INSUFFICIENT** (g153, Codex CE verified): `C1C2C3 = blockdiag[1, −ε⁴]` has
`∑E²=0`, raw `∏T = 0` (interior `T2=0`), but `P11 = −ε⁴` — so `‖P11‖² = ε⁸ ≠ 0 = ‖∏T‖²`. A zero
INTERIOR reduced block produces a nonzero `P11` via gauge interactions invisible to `E`. So the
reduced core MUST be the **Schur complement** `R = P11 − P10·Ainv·P01` (`A = P00 ≈ I` near `w0`),
the gauge-normalized chain — NOT the raw `∏T`.

## The reusable bedrock (from `GeneralR1Recursion`)

The abstract squeeze is already PROVEN there and reused here:
- `hardPivot_schur_blockId` — `L·(fromBlocks 1 b c D)·R = fromBlocks 1 0 0 (D−c·b)` (transvection).
- `schur_row_decomp` — `b·β + D·Γ = b·(1·β + a·Γ) + (D − b·a)·Γ` (the row decomposition).
- `schur_lossDiff_eq_cofactor` — `∑(bErow+SΓ)² − ∑(SΓ)² = ∑ bErow·(bErow+2SΓ)` (loss-diff ∈ ideal).
- `schur_node_squeeze_unif` — the two-sided squeeze, explicit `c₁ = (2(1+T²))⁻¹`, `c₂ = 2+2T²`.

The genuine #44c work here is the **L2 geometric presentation**: the 2-factor gauge-sliced product
in Schur block form, matched to the `schur_*` shape (`Erow` = regular residual row, `b` = pivot
column `→ 0` at `w0`, `S·Γ` = the reduced chain).

## Status

ROUTE-INDEPENDENT bedrock (sub-1): the 2-factor block product + the Schur `(1,1)` split, GREEN. The
`L`-fold + the gauge-slice presentation are the next layers; the wrapper is controller-wired.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The 2-factor block product** (`g150_gauge_chart` cert). For two gauge-sliced rank-`r` layers
`C₁ = fromBlocks (I+X₁) Y₁ Z₁ T₁`, `C₂ = fromBlocks (I+X₂) Y₂ Z₂ T₂`, the product `C₁·C₂` has blocks
`(0,0) = (I+X₁)(I+X₂)+Y₁Z₂`, `(0,1) = (I+X₁)Y₂+Y₁T₂`, `(1,0) = Z₁(I+X₂)+T₁Z₂`, `(1,1) = Z₁Y₂+T₁T₂`.
Pure `CommRing` block algebra (`fromBlocks_multiply`). -/
theorem twofactor_block_product {r m₁ m₂ m₃ : Type*} [Fintype r] [DecidableEq r]
    [Fintype m₂] {R : Type*} [CommRing R]
    (X₁ : Matrix r r R) (Y₁ : Matrix r m₂ R) (Z₁ : Matrix m₁ r R) (T₁ : Matrix m₁ m₂ R)
    (X₂ : Matrix r r R) (Y₂ : Matrix r m₃ R) (Z₂ : Matrix m₂ r R) (T₂ : Matrix m₂ m₃ R) :
    (Matrix.fromBlocks (1 + X₁) Y₁ Z₁ T₁) * (Matrix.fromBlocks (1 + X₂) Y₂ Z₂ T₂)
      = Matrix.fromBlocks
          ((1 + X₁) * (1 + X₂) + Y₁ * Z₂) ((1 + X₁) * Y₂ + Y₁ * T₂)
          (Z₁ * (1 + X₂) + T₁ * Z₂) (Z₁ * Y₂ + T₁ * T₂) := by
  rw [Matrix.fromBlocks_multiply]

/-- **The Schur split of the 2-factor product's `(1,1)` block** (g150-fix / g153). The lower-right
Schur complement `R := P₁₁ − P₁₀·Ainv·P₀₁` (`Ainv` = the pivot inverse) is the clean reduced core
(the gauge-normalized chain); `P₁₁ = R + P₁₀·Ainv·P₀₁` exhibits the endpoint leak `P₁₁ − R` as a
product of the regular residuals `P₁₀, P₀₁` (`∈ ideal(reg)`). Pure ring algebra. -/
theorem schur_P11_decomp {r mlo nhi : Type*} [Fintype r] {R : Type*} [Ring R]
    (Ainv : Matrix r r R) (P01 : Matrix r nhi R) (P10 : Matrix mlo r R)
    (P11 : Matrix mlo nhi R) :
    P11 = (P11 - P10 * Ainv * P01) + P10 * Ainv * P01 := by
  rw [sub_add_cancel]

/-- **The Frobenius block-sum** (route-independent). The entrywise-summed `f`-weight of a
`fromBlocks` matrix splits into the four block sums (`f = (·²)` gives the squared-Frobenius split).
The block-summing of `dlnLoss = ∑ f((prod − B)ᵢⱼ)` once the gauge-sliced product is in block form:
`loss = ∑E² + ‖P11‖²`, `E` the regular-residual blocks `(0,0),(0,1),(1,0)`, `P11` the `(1,1)` block.
Pure `Fintype.sum_sum_type`; stated for a general entry weight `f` to dodge a typeclass. -/
theorem frobenius_fromBlocks {r mlo nhi₀ nhi₁ : Type*} [Fintype r] [Fintype mlo]
    [Fintype nhi₀] [Fintype nhi₁] {R S : Type*} [AddCommMonoid S] (f : R → S)
    (E00 : Matrix r nhi₀ R) (E01 : Matrix r nhi₁ R)
    (E10 : Matrix mlo nhi₀ R) (E11 : Matrix mlo nhi₁ R) :
    (∑ i, ∑ j, f (Matrix.fromBlocks E00 E01 E10 E11 i j))
      = ((∑ i, ∑ j, f (E00 i j)) + (∑ i, ∑ j, f (E01 i j)))
        + ((∑ i, ∑ j, f (E10 i j)) + (∑ i, ∑ j, f (E11 i j))) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
    rw [Finset.sum_add_distrib]
  · simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    rw [Finset.sum_add_distrib]

/-- **The matrix-core comparability squeeze** (#54, the load-bearing #44c obligation, route- and
encoding-independent). With the loss-block decomposed as `P₁₁ = leak + R` entrywise (`hsplit`: `R` =
the gauge-normalized Schur core, `leak` = the regular×regular endpoint leak) and the leak charged to
the regular block `∑ leak² ≤ t²·∑ E²` (`hleak`; `t = ‖pivot‖ → 0` at `w0`), the loss `∑E² + ‖P₁₁‖²`
is two-sidedly comparable to the clean form `∑E² + ‖R‖²`:
`(2(1+t²))⁻¹·(∑E²+‖R‖²) ≤ ∑E²+‖P₁₁‖² ≤ (2+2t²)·(∑E²+‖R‖²)`.
The thin specialisation of `squeeze_bounds_abstract` (`p = leak`, `s = R`, `p+s = P₁₁`). The g153
raw-`∏T` refutation is dodged: the leak is in the regular ideal (`hleak`), so its excess is charged
to `∑E²`, not the core — exactly where the raw-`∏T` core was insufficient. -/
theorem core_comparability_squeeze {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι → ℝ) (P11 leak Rcore : κ → ℝ) (t : ℝ)
    (hsplit : ∀ j, P11 j = leak j + Rcore j)
    (hleak : (∑ j, (leak j) ^ 2) ≤ t ^ 2 * (∑ i, (E i) ^ 2)) :
    ((∑ i, (E i) ^ 2) + (∑ j, (Rcore j) ^ 2))
        ≤ (2 * (1 + t ^ 2)) * ((∑ i, (E i) ^ 2) + (∑ j, (P11 j) ^ 2))
    ∧ ((∑ i, (E i) ^ 2) + (∑ j, (P11 j) ^ 2))
        ≤ (2 + 2 * t ^ 2) * ((∑ i, (E i) ^ 2) + (∑ j, (Rcore j) ^ 2)) := by
  simp only [hsplit]
  exact squeeze_bounds_abstract E leak Rcore t hleak

/-- **The per-layer Schur block-diagonalisation** (#44c, g156 / #61 — the corrected `coreAbsorb`
core object). A gauge layer `C = fromBlocks (1+X) Y Z T` with invertible `(0,0)` corner
block-diagonalises by the unipotent transvections `L = [[1,0],[−Z⅟(1+X),1]]`,
`R = [[1,−⅟(1+X)Y],[0,1]]` to `blockdiag[(1+X), S]`, where `S = T − Z·⅟(1+X)·Y` is the **per-layer
Schur complement** — the honest reduced block (#61 CORRECTION: NOT the multiplicative unit
`T·(I−VY)⁻¹`, which is `0` whenever `T=0`; the additive Schur `S` is nonzero when `T=0` but `Z,Y≠0`,
the g153 case). The general-pivot analog of `hardPivot_schur_blockId` (pivot `= 1`). -/
theorem layer_schur_blockDiag {r m : Type*} [Fintype r] [DecidableEq r] [Fintype m] [DecidableEq m]
    {R : Type*} [CommRing R]
    (X : Matrix r r R) (Y : Matrix r m R) (Z : Matrix m r R) (T : Matrix m m R)
    [Invertible (1 + X : Matrix r r R)] :
    Matrix.fromBlocks (1 : Matrix r r R) (0 : Matrix r m R) (-(Z * ⅟(1 + X))) 1
        * Matrix.fromBlocks (1 + X) Y Z T
        * Matrix.fromBlocks (1 : Matrix r r R) (-(⅟(1 + X) * Y)) (0 : Matrix m r R) 1
      = Matrix.fromBlocks (1 + X) (0 : Matrix r m R) (0 : Matrix m r R) (T - Z * ⅟(1 + X) * Y) := by
  have hr1 : (1 + X : Matrix r r R) * ⅟(1 + X) = 1 := mul_invOf_self _
  have hl1 : ⅟(1 + X : Matrix r r R) * (1 + X) = 1 := invOf_mul_self _
  -- Step 1: `L · C = fromBlocks (1+X) Y 0 (T − Z⅟(1+X)·Y)` (clear the lower-left).
  have hLC : Matrix.fromBlocks (1 : Matrix r r R) (0 : Matrix r m R) (-(Z * ⅟(1 + X))) 1
        * Matrix.fromBlocks (1 + X) Y Z T
      = Matrix.fromBlocks (1 + X) Y (0 : Matrix m r R) (T - Z * ⅟(1 + X) * Y) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · -- (1,0): −Z⅟(1+X)·(1+X) + 1·Z = 0
      rw [Matrix.one_mul, Matrix.neg_mul, Matrix.mul_assoc, hl1, Matrix.mul_one, neg_add_cancel]
    · -- (1,1): −Z⅟(1+X)·Y + 1·T = T − Z⅟(1+X)·Y
      rw [Matrix.one_mul, Matrix.neg_mul]; abel
  -- Step 2: `(L·C) · R = fromBlocks (1+X) 0 0 (T − Z⅟(1+X)·Y)` (clear the upper-right).
  rw [hLC, Matrix.fromBlocks_multiply]
  congr 1
  · simp
  · -- (0,1): (1+X)·(−⅟(1+X)·Y) + Y·1 = −(1+X)⅟(1+X)·Y + Y = 0
    rw [Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, hr1, Matrix.one_mul, neg_add_cancel]
  · simp
  · -- (1,1): 0·(−⅟(1+X)·Y) + (T−Z⅟(1+X)·Y)·1 = T − Z⅟(1+X)·Y
    rw [Matrix.zero_mul, Matrix.mul_one, zero_add]

/-- **The core-shear homeomorphism** (the `coreAbsorb` packaging, part (a)). Given a continuous
`shift : Reg × Spec → Core` — the gauge-dependent Schur correction `S_s − T_s = −Z_s(I+X_s)⁻¹Y_s`,
a function of the GAUGE coords (which after `split` live in the regular AND spectator slots, never
the core slot `T` itself) — the self-map `(reg, core, spec) ↦ (reg, core + shift (reg, spec), spec)`
on `Reg × (Core × Spec)` is a homeomorphism fixing the regular and spectator slots, inverse
`core ↦ core − shift (reg, spec)`. The genuine `coreAbsorb` shear (`T_s ↦ S_s = T_s − Z(I+X)⁻¹Y`):
additive in the core slot since the correction does not depend on `T`; `shift` is abstract so the
producer (the gauge slice) supplies the concrete `−Z(I+X)⁻¹Y`. -/
def coreShearHomeo {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] (shift : Reg × Spec → Core) (hshift : Continuous shift) :
    (Reg × (Core × Spec)) ≃ₜ (Reg × (Core × Spec)) where
  toFun := fun q => (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2))
  invFun := fun q => (q.1, (q.2.1 - shift (q.1, q.2.2), q.2.2))
  left_inv := fun q => by simp
  right_inv := fun q => by simp
  continuous_toFun := by
    have hrs : Continuous fun q : Reg × (Core × Spec) => (q.1, q.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    refine continuous_fst.prodMk (Continuous.prodMk ?_ (continuous_snd.comp continuous_snd))
    exact (continuous_fst.comp continuous_snd).add (hshift.comp hrs)
  continuous_invFun := by
    have hrs : Continuous fun q : Reg × (Core × Spec) => (q.1, q.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    refine continuous_fst.prodMk (Continuous.prodMk ?_ (continuous_snd.comp continuous_snd))
    exact (continuous_fst.comp continuous_snd).sub (hshift.comp hrs)

/-- `coreShearHomeo` fixes the regular slot. -/
theorem coreShearHomeo_regular {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] (shift : Reg × Spec → Core) (hshift : Continuous shift)
    (q : Reg × (Core × Spec)) : (coreShearHomeo shift hshift q).1 = q.1 := rfl

/-- `coreShearHomeo` fixes the spectator slot. -/
theorem coreShearHomeo_spectator {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] (shift : Reg × Spec → Core) (hshift : Continuous shift)
    (q : Reg × (Core × Spec)) : (coreShearHomeo shift hshift q).2.2 = q.2.2 := rfl

/-- `coreShearHomeo` fixes the origin iff the shift vanishes at the origin gauge coords — the
`coreAbsorb_basepoint` datum (the Schur correction `−Z(I+X)⁻¹Y = 0` at the deepest point, where
`Y = Z = 0`). -/
theorem coreShearHomeo_basepoint {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [AddCommGroup Core] [TopologicalSpace Core] [IsTopologicalAddGroup Core]
    [TopologicalSpace Spec] [Zero Reg] [Zero Spec]
    (shift : Reg × Spec → Core) (hshift : Continuous shift) (h0 : shift (0, 0) = 0) :
    coreShearHomeo shift hshift (0 : Reg × (Core × Spec)) = 0 := by
  show ((0 : Reg), ((0 : Core) + shift ((0 : Reg), (0 : Spec)), (0 : Spec))) = 0
  rw [h0, add_zero]; rfl

/-! ## The `regAbsorb` packaging — lifting a spec-fixing reg-homeomorphism to `DeepestSplit`

Unlike `coreAbsorb` (an additive shear, GLOBAL det = 1), `regAbsorb` is the NONLINEAR residual map
raw→`E` — a genuine LOCAL diffeo (`det → 0` off `w0`). Its structural shape, abstract over the
concrete `E`: a homeomorphism `Ψ` of the `(Reg × Spec)` part that FIXES the spectator component
(reads reg+spec, writes reg, the spec untouched), lifted to `DeepestSplit = Reg × (Core × Spec)`
fixing the core slot. The concrete `Ψ` (the IFT straightening of `E`) is the producer's; this
packaging is abstract over it. -/

/-- **The reg-slice homeomorphism** (the `regAbsorb` packaging). Given a homeomorphism `Ψ` of
`Reg × Spec` that fixes the spectator component (`(Ψ p).2 = p.2`), the lift
`(reg, core, spec) ↦ ((Ψ (reg, spec)).1, core, spec)` is a self-homeomorphism of `Reg × (Core × Spec)`
fixing the core and spectator slots. The producer supplies `Ψ` = the IFT straightening of the
nonlinear residual `E` (a local diffeo near `w0`, restricted to a homeomorphism on its image). -/
def regSliceHomeo {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2) :
    (Reg × (Core × Spec)) ≃ₜ (Reg × (Core × Spec)) where
  toFun := fun q => ((Ψ (q.1, q.2.2)).1, (q.2.1, q.2.2))
  invFun := fun q => ((Ψ.symm (q.1, q.2.2)).1, (q.2.1, q.2.2))
  left_inv := fun q => by
    have hsymm : Ψ.symm (Ψ (q.1, q.2.2)) = (q.1, q.2.2) := Ψ.left_inv _
    have hfst : (Ψ (q.1, q.2.2)).2 = q.2.2 := hΨspec _
    have : (Ψ.symm ((Ψ (q.1, q.2.2)).1, q.2.2)).1 = q.1 := by
      rw [← hfst, Prod.mk.eta, hsymm]
    simp only [this]
  right_inv := fun q => by
    have hsymm : Ψ (Ψ.symm (q.1, q.2.2)) = (q.1, q.2.2) := Ψ.right_inv _
    have hfst : (Ψ.symm (q.1, q.2.2)).2 = q.2.2 := by
      have := hΨspec (Ψ.symm (q.1, q.2.2)); rwa [hsymm] at this
    have : (Ψ ((Ψ.symm (q.1, q.2.2)).1, q.2.2)).1 = q.1 := by
      rw [← hfst, Prod.mk.eta, hsymm]
    simp only [this]
  continuous_toFun := by
    have hrs : Continuous fun q : Reg × (Core × Spec) => (q.1, q.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    exact ((continuous_fst.comp Ψ.continuous).comp hrs).prodMk
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd))
  continuous_invFun := by
    have hrs : Continuous fun q : Reg × (Core × Spec) => (q.1, q.2.2) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    exact ((continuous_fst.comp Ψ.symm.continuous).comp hrs).prodMk
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd))

/-- `regSliceHomeo` fixes the core slot. -/
theorem regSliceHomeo_core {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (q : Reg × (Core × Spec)) : (regSliceHomeo Ψ hΨspec q).2.1 = q.2.1 := rfl

/-- `regSliceHomeo` fixes the spectator slot. -/
theorem regSliceHomeo_spectator {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (q : Reg × (Core × Spec)) : (regSliceHomeo Ψ hΨspec q).2.2 = q.2.2 := rfl

/-- `regSliceHomeo` fixes the origin iff `Ψ` fixes the origin reg-component — the
`regAbsorb_basepoint` datum (the residual `E = 0` at the deepest point, where all gauge coords `0`). -/
theorem regSliceHomeo_basepoint {Reg Core Spec : Type*}
    [TopologicalSpace Reg] [TopologicalSpace Core] [TopologicalSpace Spec]
    [Zero Reg] [Zero Core] [Zero Spec]
    (Ψ : (Reg × Spec) ≃ₜ (Reg × Spec)) (hΨspec : ∀ p : Reg × Spec, (Ψ p).2 = p.2)
    (h0 : (Ψ (0, 0)).1 = 0) :
    regSliceHomeo Ψ hΨspec (0 : Reg × (Core × Spec)) = 0 := by
  show ((Ψ ((0 : Reg), (0 : Spec))).1, ((0 : Core), (0 : Spec))) = 0
  rw [h0]; rfl

end DLNFibre.DLN.RLCT
