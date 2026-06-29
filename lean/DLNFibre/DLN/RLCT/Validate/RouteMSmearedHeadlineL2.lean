import DLNFibre.DLN.RLCT.Validate.RouteMSmearedChartL2
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedHeadlineIface
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedMinAdm

/-!
# `RouteMSmearedHeadlineL2` — the L=2 boundary-smeared box-divergence on a CONDITIONED source box

The validate-small anchor for the boundary-SMEARED branch. The headline is the achiever box-divergence

    ∫⁻_{cubeBox N ε} |routeMCore M x|^{−c'} = ⊤   (c' ≥ ½·minAdm M, every ε > 0),

assembled from the banked smeared engine through a CONDITIONED source box (`condBox`) — NOT the banked
`smearedSubBox`. The reason is a soundness finding (this tide): the genm-smeared2 `smearedSubBox` (pivot
in `Ioo 0 δ`, ALL other coords in the FULL `Icc −δ δ`) is TOO WEAK for the rational-shear chart — the
unit `U = ‖P₁·H̄‖²` is `0` where the rank block `P₁ = 0` (the all-small corner of the full box), so the
`hUpos` the axis-peel needs is unsatisfiable there, and the off-pole rate degenerates. The `(2,3,1)` /
`(1,3,2)` precedents avoid this by feeding a CONDITIONED box (`subBox231`: the rank-block diagonal pinned
in `[δ/2,δ]`, keeping `det P₁ ≥ δ²/8 > 0`) directly through `routeMCore_box_diverges_of_RadialMPChart`.

This file banks the conditioned-box L=2 assembly:

* `condBox p box δ` — a per-axis product box (the pivot coord `p` in `Ioo 0 δ`, every other coord `k` in
  a supplied interval `box k ⊆ Icc −δ δ`), the opaque-width analog of `subBox231`.
* `hSdiv_of_peeled_rate_onBox` — the weighted divergence on `condBox`, from a peeled rate holding ON the
  conditioned box (so `U > 0` is a genuine box hypothesis, not the false full-box one). The conditioned
  generalization of `hSdiv_of_peeled_rate` (which is its `box k = Icc −δ δ` special case), via the same
  axis-peel engine (`axisPeel_diverges_of_quadratic_rate`, banked, takes any positive-measure rest box).
* `routeMCore_box_diverges_smearedL2` — the headline: from the chart's MP/embedding/radial facts, the
  containment on `condBox` (field A), and the peeled rate + `U`-positivity on `condBox`, the box integral
  diverges for `c' ≥ ½·minAdm M`. The genm-smeared2 contract (`routeMCore_box_diverges_smearedContract`)
  wired with the conditioned-box divergence.

The genuinely-analytic field-A Λ₀-bound and the opaque-width chart decode (producing the peeled rate over
the conditioned box) are the per-family inputs; their generic constructions are independent follow-ups.
Non-vacuity: the `(2,3,1)` chart satisfies the inputs (`condBox` = `subBox231` shape).
-/

open MeasureTheory
open scoped ENNReal BigOperators Matrix

namespace DLNFibre.DLN.RLCT

/-! ## The conditioned source box `condBox` (the opaque-width `subBox231` shape) -/

/-- **The conditioned source box.** `condBox p box δ = {u | u p ∈ Ioo 0 δ ∧ ∀ k ≠ p, u k ∈ box k}` —
the pivot coord positive-small, every other coord in its supplied interval `box k` (e.g. the rank-block
diagonal pinned in `[δ/2,δ]` to keep `det P₁` away from `0`). The `box k = Icc −δ δ` choice recovers
`smearedSubBox`. -/
def condBox {N : ℕ} (p : Fin N) (box : Fin N → Set ℝ) (δ : ℝ) : Set (Fin N → ℝ) :=
  {u | u p ∈ Set.Ioo (0 : ℝ) δ ∧ ∀ k, k ≠ p → u k ∈ box k}

/-- `condBox p box δ` is measurable (a finite intersection of coordinate-preimages), given each `box k`
measurable. -/
theorem measurableSet_condBox {N : ℕ} (p : Fin N) (box : Fin N → Set ℝ) (δ : ℝ)
    (hbox : ∀ k, MeasurableSet (box k)) : MeasurableSet (condBox p box δ) := by
  have hpiv : MeasurableSet {u : Fin N → ℝ | u p ∈ Set.Ioo (0 : ℝ) δ} :=
    measurableSet_preimage (measurable_pi_apply p) measurableSet_Ioo
  have hrest : MeasurableSet {u : Fin N → ℝ | ∀ k, k ≠ p → u k ∈ box k} := by
    have heq : {u : Fin N → ℝ | ∀ k, k ≠ p → u k ∈ box k}
        = ⋂ k ∈ (Finset.univ.erase p), {u : Fin N → ℝ | u k ∈ box k} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
    rw [heq]
    exact Finset.measurableSet_biInter _ (fun k _ =>
      measurableSet_preimage (measurable_pi_apply k) (hbox k))
  exact hpiv.inter hrest

/-- **`condBox p box δ` as a product under the pivot peel.** Pushed through `piFinSuccAbove p`, it is
`Ioo 0 δ ×ˢ (univ.pi fun k => box (p.succAbove k))`. The conditioned analog of `smearedSubBox_peel`. -/
theorem condBox_peel {n : ℕ} (p : Fin (n + 1)) (box : Fin (n + 1) → Set ℝ) (δ : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).symm ⁻¹' (condBox p box δ)
      = (Set.Ioo (0:ℝ) δ) ×ˢ (Set.univ.pi (fun k : Fin n => box (p.succAbove k))) := by
  ext ⟨x, y⟩
  have hsym : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).symm (x, y)
      = Fin.insertNth p x y := by
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  simp only [Set.mem_preimage, hsym, condBox, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo,
    Set.mem_univ, true_implies, Set.mem_pi]
  constructor
  · rintro ⟨hpiv, hrest⟩
    rw [Fin.insertNth_apply_same] at hpiv
    refine ⟨hpiv, fun k => ?_⟩
    have := hrest (p.succAbove k) (Fin.succAbove_ne p k)
    rwa [Fin.insertNth_apply_succAbove] at this
  · rintro ⟨hpiv, hrest⟩
    refine ⟨by rwa [Fin.insertNth_apply_same], fun j hj => ?_⟩
    rcases Fin.eq_self_or_eq_succAbove p j with rfl | ⟨k, rfl⟩
    · exact absurd rfl hj
    · rw [Fin.insertNth_apply_succAbove]; exact hrest k

/-! ## The weighted divergence on the conditioned box (field B, conditioned) -/

/-- **The weighted divergence on `condBox` (the contract's `hSdiv`, conditioned).** Given the
loss-along-chart `W` with the quadratic rate `W (insertNth p z y) = z²·Uy y` ON the conditioned rest box
(`Uy` reads only the non-pivot coords, measurable + positive THERE), each conditioned interval positive
and `box k ≠ ∅`-witnessed by positivity, and `h − 2c' ≤ −1`, the pivot-weighted integral over `condBox`
diverges. The pivot peel (`condBox_peel`) + `axisPeel_diverges_of_quadratic_rate`. The conditioned
generalization of `smearedSubBox_weighted_diverges`. -/
theorem condBox_weighted_diverges {n : ℕ} (p : Fin (n + 1)) (box : Fin (n + 1) → Set ℝ) (δ h c' : ℝ)
    (W : (Fin (n + 1) → ℝ) → ℝ) (Uy : (Fin n → ℝ) → ℝ)
    (hδ : 0 < δ)
    (hboxmeas : ∀ k, MeasurableSet (box (p.succAbove k)))
    (hboxpos : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box (p.succAbove k))))
    (hUmeas : Measurable Uy)
    (hexp : h - 2 * c' ≤ -1)
    (hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ,
      ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
        W (Fin.insertNth p z y) = z ^ 2 * Uy y)
    (hUpos : ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)), 0 < Uy y) :
    ∫⁻ u in condBox p box δ,
        ENNReal.ofReal (|u p| ^ h * |W u| ^ (-c')) = ⊤ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p with he
  have hsym : ∀ x (y : Fin n → ℝ), e.symm (x, y) = Fin.insertNth p x y :=
    fun x y => by rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  have hmp : MeasurePreserving e.symm
      (volume.prod (volume : Measure (Fin n → ℝ))) (volume : Measure (Fin (n + 1) → ℝ)) := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).symm
    rwa [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _] at h
  have htrans := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun u : Fin (n + 1) → ℝ => ENNReal.ofReal (|u p| ^ h * |W u| ^ (-c')))
    (condBox p box δ)
  rw [condBox_peel p box δ] at htrans
  rw [← htrans]
  rw [show (fun (a : ℝ × (Fin n → ℝ)) =>
      ENNReal.ofReal (|(e.symm a) p| ^ h * |W (e.symm a)| ^ (-c')))
      = (fun a : ℝ × (Fin n → ℝ) =>
        ENNReal.ofReal (|a.1| ^ h * |(fun q : ℝ × (Fin n → ℝ) => W (Fin.insertNth p q.1 q.2)) a| ^ (-c')))
      from by
    funext a; obtain ⟨x, y⟩ := a
    rw [hsym]; congr 2
    rw [Fin.insertNth_apply_same]]
  exact axisPeel_diverges_of_quadratic_rate δ h c'
    (Set.univ.pi (fun k : Fin n => box (p.succAbove k)))
    (fun q => W (Fin.insertNth p q.1 q.2)) Uy hδ
    (MeasurableSet.univ_pi (fun k => hboxmeas k)) hboxpos
    hUmeas hexp
    (fun z hz y hy => by simp only; rw [hRate z hz y hy]) hUpos

/-- **The contract's `hSdiv` from the peeled rate over the conditioned box** (the bridge into
`routeMCore_box_diverges_smearedContract`). The conditioned generalization of `hSdiv_of_peeled_rate`:
the weighted divergence on `condBox p box δ` from the peeled rate
`routeMCore M (ψ (R (insertNth p z y))) = z²·Uy y` ON the conditioned box. -/
theorem hSdiv_of_peeled_rate_onBox {L n : ℕ} (M : Fin (L + 1) → ℕ) (hN : routeMAmbient M = n + 1)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (p : Fin (n + 1)) (box : Fin (n + 1) → Set ℝ) (h : ℕ) (c' δ : ℝ) (Uy : (Fin n → ℝ) → ℝ)
    (hδ : 0 < δ)
    (hboxmeas : ∀ k, MeasurableSet (box (p.succAbove k)))
    (hboxpos : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box (p.succAbove k))))
    (hUmeas : Measurable Uy) (hexp : (h : ℝ) - 2 * c' ≤ -1)
    (W : (Fin (n + 1) → ℝ) → ℝ)
    (hW : ∀ u : Fin (n + 1) → ℝ, W u = routeMCore M (ψ (R (hN ▸ u))))
    (hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ,
      ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
        W (Fin.insertNth p z y) = z ^ 2 * Uy y)
    (hUpos : ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)), 0 < Uy y) :
    (∫⁻ u in condBox p box δ, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|W u| ^ (-c'))) = ⊤ := by
  have hcomb : (∫⁻ u in condBox p box δ, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|W u| ^ (-c')))
      = ∫⁻ u in condBox p box δ,
          ENNReal.ofReal (|u p| ^ (h : ℝ) * |W u| ^ (-c')) := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only
    rw [← Real.rpow_natCast |u p| h, ← ENNReal.ofReal_mul (by positivity)]
  rw [hcomb]
  exact condBox_weighted_diverges p box δ (h : ℝ) c' W Uy hδ hboxmeas hboxpos hUmeas hexp hRate hUpos

/-! ## The L=2 conditioned-box headline assembly -/

/-- **The contract's `hSdiv`, transported from the `Fin (n+1)` peel to `Fin N` via `N = n + 1`.** A
`subst`-clean helper isolating the single `Fin N` vs `Fin (n+1)` dimension cast the assembly needs (the
`hSdiv_of_peeled_rate_onBox` output is in `Fin (n+1)`, the contract input in `Fin N`). Takes the
`Fin (n+1)` divergence for the loss `fun u => G (hN ▸ u)` (`G` precomposed with the cast — exactly the
peeled-rate `W`) over `condBox p₀ box₀ δ`, yields the `Fin N` divergence for `G` over the `hN ▸`-images.
`subst hN` makes `N` and `n+1` defeq, collapsing every `hN ▸`. -/
theorem hSdiv_box_transport {N n : ℕ} (hN : N = n + 1)
    (G : (Fin N → ℝ) → ℝ) (p₀ : Fin (n + 1)) (box₀ : Fin (n + 1) → Set ℝ) (h : ℕ) (c' δ : ℝ)
    (htop : (∫⁻ u in condBox p₀ box₀ δ, ENNReal.ofReal (|u p₀| ^ h)
      * ENNReal.ofReal (|G (hN ▸ u)| ^ (-c'))) = ⊤) :
    (∫⁻ u in condBox (hN ▸ p₀ : Fin N) (fun k => box₀ (hN ▸ k)) δ,
        ENNReal.ofReal (|u (hN ▸ p₀ : Fin N)| ^ h)
          * ENNReal.ofReal (|G u| ^ (-c'))) = ⊤ := by
  subst hN; simpa using htop

/-- **The L=2 conditioned-box boundary-smeared box-divergence (the assembly).** For `M : Fin (L+1) → ℕ`
with `routeMAmbient M = n + 1`, the achiever box integral `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`
from the per-family chart facts on the CONDITIONED box `condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ`:

* `ψ` measure-preserving + a measurable embedding (the rational shear ∘ linear reshape);
* `R` a radial blow-up with fderiv `D`, injective on the box, `|det D u| = |u p|^h` (the sole Jacobian);
* the containment `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)` (FIELD A);
* the decode-derived PEELED RATE `routeMCore M (ψ (R (insertNth p z y))) = z²·Uy y` ON the conditioned
  box, with `Uy` measurable and positive THERE (a genuine conditioned hypothesis — not the false full-box
  one), and the conditioned rest box positive-measure;
* `(h:ℝ) − 2c' ≤ −1` (the binding-axis exponent, from `c' ≥ ½·minAdm`, `h = minAdm − 1`).

The genm-smeared2 contract (`routeMCore_box_diverges_smearedContract`) wired with the conditioned-box
divergence (`hSdiv_of_peeled_rate_onBox`). Non-vacuous: the `(2,3,1)`/`(1,3,2)` charts satisfy it. -/
theorem routeMCore_box_diverges_smearedL2 {L n : ℕ} (M : Fin (L + 1) → ℕ)
    (hN : routeMAmbient M = n + 1)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (p : Fin (n + 1)) (box : Fin (n + 1) → Set ℝ) (h : ℕ) (c' ε δ : ℝ) (Uy : (Fin n → ℝ) → ℝ)
    (hδ : 0 < δ)
    (hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding ψ)
    (hSpre : condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ
      ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRderiv : ∀ u ∈ condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ,
      HasFDerivWithinAt R (D u) (condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ) u)
    (hRinj : Set.InjOn R (condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ))
    (hRdet : ∀ u ∈ condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ,
      |(D u).det| = |u (hN ▸ p)| ^ h)
    (hboxmeas : ∀ k, MeasurableSet (box (p.succAbove k)))
    (hboxmeasAll : ∀ k : Fin (routeMAmbient M), MeasurableSet ((fun k => box (hN ▸ k)) k))
    (hboxpos : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box (p.succAbove k))))
    (hUmeas : Measurable Uy)
    (hexp : (h : ℝ) - 2 * c' ≤ -1)
    (hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ,
      ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
        routeMCore M (ψ (R (hN ▸ (Fin.insertNth p z y)))) = z ^ 2 * Uy y)
    (hUpos : ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)), 0 < Uy y) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ := by
  -- the `Fin (n+1)` peeled divergence (banked engine, over the conditioned box)
  have hbridge := hSdiv_of_peeled_rate_onBox M hN ψ R p box h c' δ Uy hδ hboxmeas hboxpos
    hUmeas hexp (fun u => routeMCore M (ψ (R (hN ▸ u)))) (fun u => rfl) hRate hUpos
  -- transport to `Fin (routeMAmbient M)` (one dimension cast)
  have hSdiv := hSdiv_box_transport (N := routeMAmbient M) (n := n) hN
    (fun u => routeMCore M (ψ (R u))) p box h c' δ hbridge
  -- the contract over the conditioned box
  exact routeMCore_box_diverges_smearedContract M ψ R D (hN ▸ p) h hmp hemb c' ε
    (condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ)
    (measurableSet_condBox _ _ _ hboxmeasAll)
    hSpre hRderiv hRinj hRdet hSdiv

end DLNFibre.DLN.RLCT
