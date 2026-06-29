import DLNFibre.DLN.RLCT.Validate.RouteMSmearedAxisPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedPerFamily

/-!
# `RouteMSmearedBoxDiv` — the weighted divergence on `smearedSubBox` (field B, on the real source box)

Connects the M-agnostic axis-peel engine (`axisPeel_diverges_of_quadratic_rate`) to the BANKED source box
`smearedSubBox p δ` (the contract's `S`). The pivot axis `p` is peeled by `MeasurableEquiv.piFinSuccAbove
p`, mapping `smearedSubBox p δ` to the product `Ioo 0 δ ×ˢ (rest box)`; the integrand transports, and the
axis-peel concludes `⊤`.

The rate must be supplied in the peeled form: `W (z, y) = z² · Uy y` where `W` is the loss along the chart
on the inserted point and `Uy` reads only the non-pivot coords (the `z`-free polynomial unit — the `Λ₀`
having cancelled). This is the contract's `hSdiv` on the genuine `smearedSubBox`, reusable for all opaque
widths and any pivot `p`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- **`smearedSubBox p δ` as a product under the pivot peel.** `smearedSubBox p δ`, pushed through
`piFinSuccAbove p`, is `Ioo 0 δ ×ˢ (univ.pi fun _ => Icc −δ δ)` (the pivot in `(0,δ)`, the rest in
`[−δ,δ]`). The set identity behind the peel. -/
theorem smearedSubBox_peel {n : ℕ} (p : Fin (n + 1)) (δ : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).symm ⁻¹' (smearedSubBox p δ)
      = (Set.Ioo (0:ℝ) δ) ×ˢ (Set.univ.pi (fun _ : Fin n => Set.Icc (-δ) δ)) := by
  ext ⟨x, y⟩
  have hsym : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).symm (x, y)
      = Fin.insertNth p x y := by
    rw [MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  simp only [Set.mem_preimage, hsym, smearedSubBox, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioo,
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

/-- **The weighted divergence on `smearedSubBox` (the contract's `hSdiv`).** Given the loss-along-chart
`W : (Fin (n+1) → ℝ) → ℝ` with the quadratic rate `W u = (u p)²·Uy(peel u)` on the box (`Uy` reads only
the non-pivot coords, measurable + positive), and `h − 2c' ≤ −1`, the pivot-weighted integral over
`smearedSubBox p δ` diverges. The pivot peel (`smearedSubBox_peel`) + `axisPeel_diverges_of_quadratic_rate`.
-/
theorem smearedSubBox_weighted_diverges {n : ℕ} (p : Fin (n + 1)) (δ h c' : ℝ)
    (W : (Fin (n + 1) → ℝ) → ℝ) (Uy : (Fin n → ℝ) → ℝ)
    (hδ : 0 < δ)
    (hUmeas : Measurable Uy)
    (hexp : h - 2 * c' ≤ -1)
    (hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ, ∀ y ∈ Set.univ.pi (fun _ : Fin n => Set.Icc (-δ) δ),
      W (Fin.insertNth p z y) = z ^ 2 * Uy y)
    (hUpos : ∀ y ∈ Set.univ.pi (fun _ : Fin n => Set.Icc (-δ) δ), 0 < Uy y) :
    ∫⁻ u in smearedSubBox p δ,
        ENNReal.ofReal (|u p| ^ h * |W u| ^ (-c')) = ⊤ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p with he
  have hsym : ∀ x (y : Fin n → ℝ), e.symm (x, y) = Fin.insertNth p x y :=
    fun x y => by rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  -- MP of the peel inverse (`volume` on `ℝ × (Fin n → ℝ)` is the product)
  have hmp : MeasurePreserving e.symm
      (volume.prod (volume : Measure (Fin n → ℝ))) (volume : Measure (Fin (n + 1) → ℝ)) := by
    have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).symm
    rwa [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _] at h
  -- transport the integral to the product box
  have htrans := hmp.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun u : Fin (n + 1) → ℝ => ENNReal.ofReal (|u p| ^ h * |W u| ^ (-c')))
    (smearedSubBox p δ)
  rw [smearedSubBox_peel p δ] at htrans
  rw [← htrans]
  -- on the product box, the integrand is `ofReal(|z|^h * |W(insertNth p z y)|^{−c'})`; apply the engine
  rw [show (fun (a : ℝ × (Fin n → ℝ)) =>
      ENNReal.ofReal (|(e.symm a) p| ^ h * |W (e.symm a)| ^ (-c')))
      = (fun a : ℝ × (Fin n → ℝ) =>
        ENNReal.ofReal (|a.1| ^ h * |(fun q : ℝ × (Fin n → ℝ) => W (Fin.insertNth p q.1 q.2)) a| ^ (-c')))
      from by
    funext a; obtain ⟨x, y⟩ := a
    rw [hsym]; congr 2
    rw [Fin.insertNth_apply_same]]
  exact axisPeel_diverges_of_quadratic_rate δ h c'
    (Set.univ.pi (fun _ : Fin n => Set.Icc (-δ) δ))
    (fun q => W (Fin.insertNth p q.1 q.2)) Uy hδ
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    (by
      rw [volume_pi_pi]
      refine CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => ?_)
      rw [Real.volume_Icc, ENNReal.ofReal_pos]; linarith)
    hUmeas hexp
    (fun z hz y hy => by simp only; rw [hRate z hz y hy]) hUpos

end DLNFibre.DLN.RLCT
