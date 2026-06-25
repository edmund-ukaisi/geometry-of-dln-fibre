import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.Topology.Instances.Matrix

/-!
# `DLNFibre.DLN.RLCT.Foundations.LossContinuity` — `dlnLoss` is continuous / measurable (fm3)

The square-Frobenius loss `dlnLoss H B : Params H → ℝ` is a polynomial in the layer-matrix entries, hence
continuous and measurable. The recursion-driver-INDEPENDENT analytic bedrock for the `IsRouteMCover.Fmeas`
field on the GENERAL multiplication-map loss (the flat core then composes `paramsEquivFlat.symm`, itself a
homeomorphism). Built bottom-up:

- `continuous_prodAux` : `A ↦ A⁽¹⁾·…·A⁽ᵏ⁾` is continuous (induction on `k`, `Continuous.matrix_mul`).
- `continuous_prod` : the multiplication map `A ↦ prod H A` is continuous.
- `continuous_dlnLoss` : `A ↦ dlnLoss H B A` is continuous (a finite sum of squares of `prod` entries).
- `measurable_dlnLoss` : `dlnLoss H B` is measurable (continuous ⟹ measurable).

These hold for ANY `H`, `B` — no recursion/dispatcher dependency; they are the general `Fmeas` building block.
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **`prodAux` is continuous.** The partial layer product `A ↦ prodAux H A k hk` (`= A⁽¹⁾·…·A⁽ᵏ⁾`) is
continuous in `A`, for every `k ≤ L`. Induction on `k`: base `k = 0` is the constant `1`; step is
`Continuous.matrix_mul` of the inductive product and the (continuous) evaluation of the `k`-th layer
matrix (the dependent-`Fin` index cast in `prodAux`'s definition is defeq-transparent to
`continuous_apply`). -/
theorem continuous_prodAux (H : Fin (L + 1) → ℕ) :
    ∀ (k : ℕ) (hk : k < L + 1), Continuous (fun A : Params H => prodAux H A k hk) := by
  intro k
  induction k with
  | zero =>
      intro hk
      have h1 : (fun A : Params H => prodAux H A 0 hk)
          = fun _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ) := by funext A; rfl
      rw [h1]; exact continuous_const
  | succ n ih =>
      intro hk
      exact (ih (Nat.lt_of_succ_lt hk)).matrix_mul (continuous_apply _)

/-- **The multiplication map is continuous.** `A ↦ prod H A` (`= A⁽¹⁾·…·A⁽ᴸ⁾`) is continuous. -/
theorem continuous_prod (H : Fin (L + 1) → ℕ) :
    Continuous (fun A : Params H => prod H A) :=
  continuous_prodAux H L (Nat.lt_succ_self L)

/-- **The square-Frobenius loss is continuous.** `A ↦ dlnLoss H B A = ∑ᵢⱼ ((prod H A − B)ᵢⱼ)²` is
continuous: a finite sum of squares of entries of the (continuous) product map (entry access +
subtraction + squaring are continuous). -/
theorem continuous_dlnLoss (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) :
    Continuous (fun A : Params H => dlnLoss H B A) := by
  unfold dlnLoss
  refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
  exact ((((continuous_prod H).matrix_elem i j).sub continuous_const).pow 2)

/-- **The square-Frobenius loss is measurable.** `dlnLoss H B` is measurable (continuous ⟹ measurable).
The general `IsRouteMCover.Fmeas` building block for the multiplication-map loss. -/
theorem measurable_dlnLoss (H : Fin (L + 1) → ℕ)
    (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) :
    Measurable (fun A : Params H => dlnLoss H B A) := by
  haveI : OpensMeasurableSpace (Params H) :=
    inferInstanceAs (OpensMeasurableSpace
      (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))
  exact (continuous_dlnLoss H B).measurable

/-! ## The general bounded base neighbourhood (the `IsRouteMCover.U` over the flat ambient)

The bounded open box `(−1,1)^N ∋ 0` in `Fin N → ℝ` — the general analog of the `(2,2,2)` `openBox`.
`IsRouteMCover.U` must be a BOUNDED open nbhd of the deepest point (the `≥`-leg
`rlctAtOn_ge_of_integral_lt` needs a bounded witness; `univ` breaks it). Anchoring-independent: the box
is fixed by the flat dimension `N`, not by the resolution recursion. -/

/-- The bounded open box `(−1,1)^N ∋ 0` in the flat ambient `Fin N → ℝ` (the general base neighbourhood
for the Route-M cover; the `N`-generic analog of the `(2,2,2)` `openBox`). -/
def flatOpenBox (N : ℕ) : Set (Fin N → ℝ) := Set.univ.pi (fun _ => Set.Ioo (-1 : ℝ) 1)

/-- `flatOpenBox N` is open (a product of open intervals over the finite index). -/
theorem isOpen_flatOpenBox (N : ℕ) : IsOpen (flatOpenBox N) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

/-- `0 ∈ flatOpenBox N` (the deepest point is in the box: `−1 < 0 < 1`). -/
theorem mem_flatOpenBox_zero (N : ℕ) : (0 : Fin N → ℝ) ∈ flatOpenBox N := by
  simp only [flatOpenBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.zero_apply]
  exact fun _ => ⟨by norm_num, by norm_num⟩

/-- `flatOpenBox N` is bounded (it sits in the ball/cube `[−1,1]^N`) — the boundedness the
`≥`-direction needs (`univ` would break `rlctAtOn_ge_of_integral_lt`). -/
theorem isBounded_flatOpenBox (N : ℕ) : Bornology.IsBounded (flatOpenBox N) := by
  apply Bornology.IsBounded.subset (Metric.isBounded_Icc (-(1 : Fin N → ℝ)) 1)
  intro x hx
  simp only [flatOpenBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hx
  simp only [Set.mem_Icc]
  exact ⟨fun i => by have := (hx i).1; simp only [Pi.neg_apply, Pi.one_apply]; linarith,
    fun i => by have := (hx i).2; simp only [Pi.one_apply]; linarith⟩

end DLNFibre.DLN.RLCT
