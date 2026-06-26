import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import DLNFibre.Core.Matrix.RankNormalForm
import Mathlib.MeasureTheory.Group.Measure

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestBaseL1` — the `L = 1` deepest-point normal form

The `L = 1` specialization of `deepest_regular_core_normal_form` (`Skeleton.lean`), proven
sorry-free. At a single layer there is no product: `prod H A = A 0`, so `dlnLoss H B` is the shifted
square-Frobenius norm `‖A − B‖²` — a **full nondegenerate** sum of `H⁰·H¹` squares (no separate
regular/core blocks to chart). Its local RLCT at the deepest point (whose single layer equals `B`)
is therefore `H⁰·H¹/2`, computed by flattening (`paramsEquivFlat`), translating to the origin, and
applying the full-block RLCT `smoothBlockND_rlct`.

The arithmetic recombination `H⁰·H¹/2 = r(H⁰+H¹−r)/2 + (H⁰−r)(H¹−r)/2` (the regular shift plus the
`L = 1` core `lambdaCore (H−r)`, where at one reduced layer `lambdaCore M = M⁰·M¹/2`) closes the
headline.

**Honest scope (soundness flag, controller-actionable).** The statement is FALSE when `H⁰ = 0` or
`H¹ = 0`: there the loss is an empty sum `≡ 0`, so `rlctAt = ⊤` (`rlctAtOn_zero_eq_top`), while the
right side is the finite `0`. The corner is reachable under the parent's hypotheses (`H⁰ = 0` forces
`r = 0` with `B` the empty `0×H¹` matrix of rank `0`). So this `L = 1` lemma adds `0 < H 0` and
`0 < H (Fin.last 1)`; the parent `deepest_regular_core_normal_form` (Skeleton:1124) carries the same
latent corner and should be re-scoped with all-widths-positive (flagged to the controller).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Real Matrix Finset
open scoped ENNReal Topology

/-! ## The general `n`-coordinate smooth block on the product (Params-flat) measure -/

/-- **The full nondegenerate quadratic on `Fin n → ℝ` has RLCT `n/2`** (for `n = m+1 ≥ 1`).
`rlctAtOn (∑ᵢ xᵢ²) 0 = (m+1)/2` on the product Lebesgue measure, bridged from
`smoothBlockND_rlct` (stated on `EuclideanSpace ℝ (Fin (m+1))`, Haar `volume`) across the
measure-preserving homeomorph `toLp`. Generalises `Case212.rlctAtOn_blockG_eq_one` (`m = 1`). -/
theorem sumSq_rlctAtOn_finN (m : ℕ) :
    rlctAtOn (fun x : Fin (m + 1) → ℝ => ∑ i, x i ^ 2) (0 : Fin (m + 1) → ℝ)
      = ((m + 1 : ℕ) / 2 : ℝ≥0∞) := by
  set e : (Fin (m + 1) → ℝ) ≃ₜ EuclideanSpace ℝ (Fin (m + 1)) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toHomeomorph.symm with he
  have hmp : MeasurePreserving e volume volume := PiLp.volume_preserving_toLp (Fin (m + 1))
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have key := rlctAtOn_comp_homeomorph e hmp hemb
    (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ∑ i, x i ^ 2) 0
  have he0 : e 0 = 0 := by simp [he]
  rw [he0, smoothBlockND_rlct m] at key
  rw [show (fun x : Fin (m + 1) → ℝ => ∑ i, x i ^ 2)
        = (fun w => ∑ i, (e w) i ^ 2) from by funext x; simp [he]]
  rw [key]
  push_cast
  rfl

/-- **The full nondegenerate quadratic on `Fin n → ℝ` has RLCT `n/2`** (`0 < n`), with `n` not
pinned to a successor — the `0 < n` form `rlctAt_dlnLoss_L1` consumes. -/
theorem sumSq_rlctAtOn_finN_pos (n : ℕ) (hn : 0 < n) :
    rlctAtOn (fun x : Fin n → ℝ => ∑ i, x i ^ 2) (0 : Fin n → ℝ) = ((n : ℕ) / 2 : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact sumSq_rlctAtOn_finN m

/-! ## The flattening preserves the (shifted) sum of squares -/

variable {L : ℕ}

/-- **Shifted sum-of-squares is preserved by `paramsEquivFlat`** (the flattening is a reindexing
bijection of the matrix entries). `∑ₖ ((flat A)ₖ − (flat W)ₖ)² = ∑ₛᵢⱼ (Aₛᵢⱼ − Wₛᵢⱼ)²` — no
per-entry cast computation, only the `Sigma`-sum reindex (the two `piCurry` steps + the
`arrowCongr'` re-index). General `L`; consumed at `L = 1` with `W = deepestPoint`. -/
theorem sumSq_shift_paramsEquivFlat (H : Fin (L + 1) → ℕ) (A W : Params H) :
    ∑ k, ((paramsEquivFlat H A) k - (paramsEquivFlat H W) k) ^ 2
      = ∑ s : Fin L, ∑ i, ∑ j, (A s i j - W s i j) ^ 2 := by
  set g : FlatIdx H → ℝ := fun q => (A q.1.1 q.1.2 q.2 - W q.1.1 q.1.2 q.2) ^ 2 with hg
  have hpt : ∀ k : Fin (flatDim H),
      ((paramsEquivFlat H A) k - (paramsEquivFlat H W) k) ^ 2
        = g ((Fintype.equivFin (FlatIdx H)).symm k) := fun k => by
    rw [hg]
    have hA : (paramsEquivFlat H A) k
        = A ((((Fintype.equivFin (FlatIdx H)).symm k).1).1)
            ((((Fintype.equivFin (FlatIdx H)).symm k).1).2)
            (((Fintype.equivFin (FlatIdx H)).symm k).2) := by
      show ((MeasurableEquiv.arrowCongr' (Fintype.equivFin (FlatIdx H)) (MeasurableEquiv.refl ℝ))
            (Sigma.uncurry (Sigma.uncurry A))) k = _
      rfl
    have hW : (paramsEquivFlat H W) k
        = W ((((Fintype.equivFin (FlatIdx H)).symm k).1).1)
            ((((Fintype.equivFin (FlatIdx H)).symm k).1).2)
            (((Fintype.equivFin (FlatIdx H)).symm k).2) := by
      show ((MeasurableEquiv.arrowCongr' (Fintype.equivFin (FlatIdx H)) (MeasurableEquiv.refl ℝ))
            (Sigma.uncurry (Sigma.uncurry W))) k = _
      rfl
    rw [hA, hW]
  have h1 : ∑ k, ((paramsEquivFlat H A) k - (paramsEquivFlat H W) k) ^ 2
      = ∑ q : FlatIdx H, g q := by
    rw [Finset.sum_congr rfl (fun k _ => hpt k)]
    exact Equiv.sum_comp (Fintype.equivFin (FlatIdx H)).symm g
  rw [h1, hg, Fintype.sum_sigma, Fintype.sum_sigma]

/-! ## The `L = 1` product and loss -/

/-- At `L = 1` the layer product is the sole layer: `prod H A = A 0` (the index casts are `rfl`). -/
theorem prod_L1 (H : Fin (1 + 1) → ℕ) (A : Params (L := 1) H) : prod H A = A 0 := by
  unfold prod
  show prodAux H A (0 + 1) (by omega) = A 0
  unfold prodAux
  simp only [prodAux]
  exact Matrix.one_mul _

/-- The `paramsEquivFlat`-flattening of `Params H` as a `Homeomorph` (it is a `MeasurableEquiv`,
continuous both ways). -/
noncomputable def paramsFlatHomeo (H : Fin (L + 1) → ℕ) : Params H ≃ₜ (Fin (flatDim H) → ℝ) where
  toEquiv := (paramsEquivFlat H).toEquiv
  continuous_toFun := continuous_paramsEquivFlat H
  continuous_invFun := continuous_paramsEquivFlat_symm H

/-- **`L = 1` loss as a shifted flat sum of squares.** `dlnLoss H B A = ∑ₖ ((flat A)ₖ − cₖ)²` where
`c = flat (deepestPoint)`. Uses `prod_L1` (single layer = the product), the deepest-point fibre
identity `prod (deepestPoint) = B` (so the single layer of `deepestPoint` is `B`), and the shifted
flattening `sumSq_shift_paramsEquivFlat`. -/
theorem dlnLoss_L1_eq_flat_sumSq (H : Fin (1 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 1))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (1 + 1), r ≤ H s) (A : Params (L := 1) H) :
    dlnLoss H B A
      = ∑ k, ((paramsEquivFlat H A) k
              - (paramsEquivFlat H (deepestPoint H r B hB hr (by norm_num))) k) ^ 2 := by
  set w₀ := deepestPoint H r B hB hr (by norm_num) with hw₀
  -- the single layer of the deepest point equals B (it is in the fibre, prod = B = layer 0).
  have hfib : prod H w₀ = B := (deepestPoint_isDeep H r B hB hr (by norm_num)).1
  have hw₀0 : w₀ 0 = B := by rw [← prod_L1 H w₀]; exact hfib
  rw [sumSq_shift_paramsEquivFlat H A w₀]
  -- the matrix-entry side: ∑ s ∑ i ∑ j (A s i j - w₀ s i j)² collapses (Fin 1) to layer 0,
  -- and dlnLoss = ∑ i ∑ j ((prod A - B) i j)² = ∑ i ∑ j (A 0 i j - B i j)².
  unfold dlnLoss
  rw [prod_L1 H A]
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hw₀0]; rfl

/-! ## The `L = 1` RLCT value -/

/-- **`L = 1` RLCT of the loss at the deepest point is `H⁰·H¹/2`** (`0 < H⁰`, `0 < H¹`). The loss is
a full nondegenerate sum of `H⁰·H¹` squares: flatten (`paramsFlatHomeo`), translate to the origin
(`Homeomorph.addRight`), and apply `sumSq_rlctAtOn_finN`. -/
theorem rlctAt_dlnLoss_L1 (H : Fin (1 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 1))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (1 + 1), r ≤ H s) (hH0 : 0 < H 0) (hH1 : 0 < H (Fin.last 1)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr (by norm_num))
      = ((H 0 * H (Fin.last 1) : ℕ) : ℝ≥0∞) / 2 := by
  set w₀ := deepestPoint H r B hB hr (by norm_num) with hw₀
  set n := flatDim H with hn
  -- n = H 0 * H 1 at L = 1
  have hnval : n = H 0 * H (Fin.last 1) := by
    rw [hn, flatDim_eq, Fin.sum_univ_one]; rfl
  have hnpos : 0 < n := by rw [hnval]; exact Nat.mul_pos hH0 hH1
  -- flat center c = flat w₀
  set p := paramsFlatHomeo H with hp
  set c : Fin n → ℝ := paramsEquivFlat H w₀ with hc
  -- Step 1: rlctAt = rlctAtOn (loss ∘ p.symm) at c (flatten via the homeomorph p.symm)
  rw [← rlctAtOn_eq_rlctAt]
  have hpmp : MeasurePreserving p.symm volume volume :=
    (measurePreserving_paramsEquivFlat H).symm (paramsEquivFlat H)
  have hpemb : MeasurableEmbedding p.symm := (paramsEquivFlat H).symm.measurableEmbedding
  have hstep1 := rlctAtOn_comp_homeomorph p.symm hpmp hpemb (dlnLoss H B) c
  have hpsc : p.symm c = w₀ := by
    show (paramsEquivFlat H).symm (paramsEquivFlat H w₀) = w₀
    exact (paramsEquivFlat H).symm_apply_apply w₀
  rw [hpsc] at hstep1
  rw [← hstep1]
  -- Step 2: translate by c on Fin n → ℝ (Homeomorph.addRight c; sends 0 ↦ c)
  set τ : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) := Homeomorph.addRight c with hτ
  have hτmp : MeasurePreserving τ volume volume := by
    rw [hτ]; exact measurePreserving_add_right volume c
  have hτemb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hstep2 := rlctAtOn_comp_homeomorph τ hτmp hτemb (fun x => dlnLoss H B (p.symm x)) 0
  have hτ0 : τ (0 : Fin n → ℝ) = c := by rw [hτ]; show (0 : Fin n → ℝ) + c = c; rw [zero_add]
  rw [hτ0] at hstep2
  rw [← hstep2]
  -- Step 3: (loss ∘ p.symm ∘ τ)(x) = ∑ k, x k ^ 2.
  have hcomp : (fun x : Fin n → ℝ => dlnLoss H B (p.symm (τ x))) = (fun x => ∑ k, x k ^ 2) := by
    funext x
    -- p.symm (τ x) = p.symm (x + c); flat (that) = x + c; and dlnLoss = ∑ ((flat ·) - c)².
    rw [dlnLoss_L1_eq_flat_sumSq H r B hB hr (p.symm (τ x))]
    have hflat : ∀ k, (paramsEquivFlat H (p.symm (τ x))) k = (x + c) k := by
      intro k
      show (paramsEquivFlat H) ((paramsEquivFlat H).symm (τ x)) k = (x + c) k
      rw [(paramsEquivFlat H).apply_symm_apply]
      rw [hτ]; rfl
    have hcc : (paramsEquivFlat H w₀) = c := by rw [hc]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hflat k, hcc]
    show ((x + c) k - c k) ^ 2 = x k ^ 2
    rw [Pi.add_apply]; ring
  rw [hcomp, sumSq_rlctAtOn_finN_pos n hnpos]
  -- n/2 = (H0*H1)/2
  rw [hnval]

/-! ## The `L = 1` core arithmetic -/

/-- **`lambdaCore` at `L = 1`.** A single reduced layer has the all-zero exponent vector as its only
admissible `T` (the last-exponent constraint forces `T 0 = 0`), so `lambdaCore M = M⁰·M¹/2`. -/
theorem lambdaCore_L1 (M : Fin (1 + 1) → ℕ) :
    lambdaCore (L := 1) M = (1 / 2 : ℚ) * ((M 0 * M (Fin.last 1) : ℕ) : ℚ) := by
  unfold lambdaCore
  have hAdm : Adm (L := 1) M = {fun _ => 0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨zero_mem_Adm M, ?_⟩
    intro T hT
    rw [Adm, mem_filter] at hT
    obtain ⟨_, _, _, hlast⟩ := hT
    funext s
    have hs0 : s = (0 : Fin 1) := Subsingleton.elim _ _
    subst hs0
    exact hlast 0 (by rfl)
  have hinf : (Adm (L := 1) M).inf' (Adm_nonempty M) (Mval M) = Mval (L := 1) M (fun _ => 0) := by
    apply le_antisymm
    · exact Finset.inf'_le _ (by rw [hAdm]; exact Finset.mem_singleton_self _)
    · apply Finset.le_inf'
      intro b hb
      rw [hAdm, Finset.mem_singleton] at hb
      rw [hb]
  rw [hinf]
  have hMval : Mval (L := 1) M (fun _ => 0) = (M 0 * M (Fin.last 1) : ℕ) := by
    unfold Mval tPrev
    rw [Fin.sum_univ_one]
    have hsucc : ((0 : Fin 1).succ) = Fin.last 1 := by decide
    simp only [Fin.isValue, Fin.val_zero, CharP.cast_eq_zero, sub_zero, hsucc]
    push_cast
    ring
  rw [hMval]
  push_cast
  ring

/-! ## The headline -/

/-- **`L = 1` deepest-point regular/core normal form** (`0 < H⁰`, `0 < H¹`). The `L = 1` instance of
`deepest_regular_core_normal_form`: the local RLCT of the deep-linear loss at the deepest point of
the rank-`r` fibre equals the regular shift `r(H⁰+H¹−r)/2` plus the singular core
`lambdaCore (H−r)`. At `L = 1` both reduce to the single full block `H⁰·H¹/2`
(`= r(H⁰+H¹−r)/2 + (H⁰−r)(H¹−r)/2`, the latter being `lambdaCore (H−r)`). Proven sorry-free:
`rlctAt_dlnLoss_L1` (the full-block RLCT) + `lambdaCore_L1` (the core arithmetic) + the
natural-number identity `H⁰·H¹ = r(H⁰+H¹−r) + (H⁰−r)(H¹−r)` (given `r ≤ H⁰`, `r ≤ H¹`). -/
theorem deepest_regular_core_normal_form_L1 (H : Fin (1 + 1) → ℕ) (r : ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 1))) ℝ) (hB : B.rank = r)
    (hr : ∀ s : Fin (1 + 1), r ≤ H s) (hH0 : 0 < H 0) (hH1 : 0 < H (Fin.last 1)) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr (by norm_num))
      = ((r * (H 0 + H (Fin.last 1) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) := by
  rw [rlctAt_dlnLoss_L1 H r B hB hr hH0 hH1]
  -- right side: nReg/2 + ofReal(lambdaCore (H-r)).  Show both = (H0*H1)/2.
  have h0 : r ≤ H 0 := hr 0
  have h1 : r ≤ H (Fin.last 1) := hr (Fin.last 1)
  -- lambdaCore (H-r) = (H0-r)(H1-r)/2 ≥ 0
  set M : Fin (1 + 1) → ℕ := fun s => H s - r with hM
  have hMcore : lambdaCore (L := 1) M = (1 / 2 : ℚ) * ((M 0 * M (Fin.last 1) : ℕ) : ℚ) :=
    lambdaCore_L1 M
  have hM0 : M 0 = H 0 - r := rfl
  have hM1 : M (Fin.last 1) = H (Fin.last 1) - r := rfl
  -- the ℝ≥0∞ cast assembly: nReg/2 + ofReal(core) = (H0*H1)/2
  -- core (as ℝ) = ((H0-r)*(H1-r))/2 ≥ 0
  have hcoreReal : (lambdaCore (L := 1) M : ℝ) = ((M 0 * M (Fin.last 1) : ℕ) : ℝ) / 2 := by
    rw [hMcore]; push_cast; ring
  -- ofReal(core) = ((H0-r)*(H1-r) : ℕ)/2 in ℝ≥0∞
  have hcoreENN : ENNReal.ofReal (lambdaCore (L := 1) M : ℝ)
      = ((M 0 * M (Fin.last 1) : ℕ) : ℝ≥0∞) / 2 := by
    rw [hcoreReal, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast,
      show ENNReal.ofReal (2 : ℝ) = 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; rfl]
  rw [hcoreENN]
  -- now: (H0*H1)/2 = (r*(H0+H1-r))/2 + ((H0-r)*(H1-r))/2.  Combine over /2, then ℕ identity.
  rw [ENNReal.div_add_div_same]
  congr 1
  -- ((H0*H1 : ℕ) : ℝ≥0∞) = ((r*(H0+H1-r) : ℕ) : ℝ≥0∞) + (((H0-r)*(H1-r) : ℕ) : ℝ≥0∞)
  rw [← Nat.cast_add]
  congr 1
  -- ℕ identity: H0*H1 = r*(H0+H1-r) + (H0-r)*(H1-r), given r ≤ H0, r ≤ H1
  rw [hM0, hM1]
  -- write H0 = r + a, H1 = r + b; both sides expand to r² + rb + ar + ab.
  obtain ⟨a, ha⟩ : ∃ a, H 0 = r + a := ⟨H 0 - r, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, H (Fin.last 1) = r + b := ⟨H (Fin.last 1) - r, by omega⟩
  rw [ha, hb]
  -- (r+a)*(r+b) = r*((r+a)+(r+b)-r) + (r+a-r)*(r+b-r) = r*(r+a+b) + a*b
  have h1 : (r + a) + (r + b) - r = r + a + b := by omega
  have h2 : r + a - r = a := by omega
  have h3 : r + b - r = b := by omega
  rw [h1, h2, h3]
  ring

end DLNFibre.DLN.RLCT
