import DLNFibre.DLN.RLCT.Validate.RouteMSmearedDecodeGen
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedAchieverGeneral
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedMinAdm

/-!
# `RouteMSmearedAssembleGen` — the general-`L` smeared achiever assembly `routeMCore_smearedGen`

Assembles the general-`L` smeared box-divergence from the DECODE-derived rate (`RouteMSmearedDecodeGen`)
and the M-agnostic assembly engine `routeMCore_box_diverges_smearedL2` (which is fully general-`L`,
despite its historical "L2" name — it takes `M : Fin (L+1) → ℕ`). The generic chart facts (`ψ`
measure-preserving + a measurable embedding, `R` fderiv/injectivity/det) are DISCHARGED from the
general-`L` radial machinery (`psiMapG`/`RmapG`/`DmapG`, `RouteMSmearedDecodeGen`); the peeled rate is
`routeMCore_psiMapG_RmapG` (off the shear cancellation). What remains per family are the genuinely
conditioned analytic inputs — the cancellation `P₁·Λ₀ = P₂` on the box, FIELD-A containment, and
`U`-positivity — supplied as named hypotheses (exactly the `SmearedAchieverChart` fields).

* `routeMCore_smearedGen` — the general-`L` conditioned-box smeared box-divergence, with the mechanical
  `z`/`U` peel (`zuG = z`, `Uy y := UunitG (hN ▸ insertNth p 0 y)` z-free) FOLDED in, so only the
  genuinely-analytic per-family inputs remain.

The radial Jacobian exponent is `r · M (deepLayer).succ − 1 = deepRank · M_L − 1 = minAdm M − 1`
(via the banked `minAdm_eq_deepRank_mul_last`), with `r = deepRank M` — the FIDELITY constraint that
exactly the `r·c` deepest-top coords are radial-active (K's coords are FREE spectators, sheared not
radial). This module states `routeMCore_smearedGen` with `r` free (`h := r · M (deepLayer).succ − 1`);
the `r = deepRank` specialization (matching `minAdm`) is the caller's choice at the chart bundle.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-! ## The mechanical `z`/`U` peel under the `hN` ambient-dimension cast -/

/-- The cast-cancellation `(hN ▸ f) (hN ▸ x) = f x` for a `Fin`-vector under `routeMAmbient M = n+1`. -/
theorem hNG_cast_apply {n : ℕ} (M : Fin (L + 1) → ℕ) (hN : routeMAmbient M = n + 1)
    (f : Fin (n + 1) → ℝ) (x : Fin (n + 1)) :
    (hN ▸ f : Fin (routeMAmbient M) → ℝ) (hN ▸ x : Fin (routeMAmbient M)) = f x := by
  have key : ∀ (N : ℕ) (h : N = n + 1) (g : Fin (n + 1) → ℝ) (z : Fin (n + 1)),
      (h ▸ g : Fin N → ℝ) (h ▸ z : Fin N) = g z := fun N h g z => by subst h; rfl
  exact key _ hN f x

/-- **The `z`-readoff under the peel.** `zuG (hN ▸ insertNth p z y) = z` when `hN ▸ p = pivotCoordG`. -/
theorem zuG_hN_insertNth {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc) (z : ℝ) (y : Fin n → ℝ) :
    zuG M hL hrs hr hc (hN ▸ (Fin.insertNth p z y)) = z := by
  rw [zuG, ← hp, hNG_cast_apply M hN (Fin.insertNth p z y) p, Fin.insertNth_apply_same]

/-- The two peeled points `hN ▸ insertNth p z y` and `hN ▸ insertNth p 0 y` agree off `pivotCoordG`. -/
theorem hNG_insertNth_agree_off_pivot {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc) (z : ℝ) (y : Fin n → ℝ) :
    ∀ m, m ≠ pivotCoordG M hL hrs hr hc →
      (hN ▸ (Fin.insertNth p z y) : Fin (routeMAmbient M) → ℝ) m
        = (hN ▸ (Fin.insertNth p (0:ℝ) y) : Fin (routeMAmbient M) → ℝ) m := by
  have key : ∀ (N : ℕ) (h : N = n + 1) (m : Fin N),
      (h ▸ p : Fin N) ≠ m →
        (h ▸ (Fin.insertNth p z y) : Fin N → ℝ) m
          = (h ▸ (Fin.insertNth p (0:ℝ) y) : Fin N → ℝ) m := by
    intro N h m hm; subst h
    rcases Fin.eq_self_or_eq_succAbove p m with rfl | ⟨k, rfl⟩
    · exact absurd rfl hm
    · simp only [Fin.insertNth_apply_succAbove]
  intro m hm
  exact key _ hN m (fun he => hm ((hp ▸ he).symm))

/-- **The `z`-free peeled unit** `UunitG (hN ▸ insertNth p z y) = UunitG (hN ▸ insertNth p 0 y)`. -/
theorem UunitG_hN_insertNth {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc) (z : ℝ) (y : Fin n → ℝ) :
    UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p z y))
      = UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y)) :=
  UunitG_congr_off_pivot M hL hrs hr hc
    (hNG_insertNth_agree_off_pivot M hL hrs hr hc hN p hp z y)

/-! ## The general-`L` smeared box-divergence assembly

`routeMCore_smearedGen`: the general-`L` conditioned-box smeared box-divergence, assembled from the
DECODE-derived rate (`routeMCore_psiMapG_RmapG`) + the M-agnostic engine
`routeMCore_box_diverges_smearedL2`. The mechanical `z`/`U` peel is folded in; only the
genuinely-conditioned analytic inputs remain (the cancellation on each peeled point, FIELD-A
containment, `U`-positivity), plus the `ψ` measure-theoretic facts (MP + a measurable embedding) and
the `Uy` measurability — the mechanical `psiMapG`/`UunitG` plumbing, isolated as named hypotheses
(discharged per-family or by the `frontProd`-polynomial-measurability residue). -/

/-- **The general-`L` conditioned-box boundary-smeared box-divergence.** For `M : Fin (L+1) → ℕ`,
`0 < L`, the front-bottleneck split `r + s = M (deepLayer hL).castSucc`, `0 < r`, `0 < M
(deepLayer).succ`, `routeMAmbient M = n + 1`, and the binding pivot `p` (`hN ▸ p = pivotCoordG`): the
achiever box integral `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`, given

* `ψ := psiMapG` measure-preserving + a measurable embedding (the mechanical shear-∘-reshape facts);
* the exponent `(r·M(deepLayer).succ − 1 : ℝ) − 2c' ≤ −1` (`= minAdm − 1 − 2c'`, from `c' ≥ ½·minAdm`);
* the shear cancellation `P₁·Λ₀ = P₂` on each peeled point (off the pole — K-free-spectator);
* `U`-positivity `0 < UunitG (hN ▸ insertNth p 0 y)` on the conditioned rest box;
* FIELD-A containment + box measurability/positivity + `Uy` measurability.

The chart facts (radial fderiv/injOn/det, the peeled rate's `z²·UunitG` form) are DISCHARGED from the
general-`L` radial machinery + `routeMCore_psiMapG_RmapG`. -/
theorem routeMCore_smearedGen {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1)) (box : Fin (n + 1) → Set ℝ)
    (c' ε δ : ℝ) (hδ : 0 < δ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc)
    (hmp : MeasurePreserving (psiMapG M hL hrs)
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding (psiMapG M hL hrs))
    (hSpre : condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ
      ⊆ (fun u => psiMapG M hL hrs (RmapG M hL hrs hr hc u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hboxmeas : ∀ k, MeasurableSet (box (p.succAbove k)))
    (hboxmeasAll : ∀ k : Fin (routeMAmbient M), MeasurableSet ((fun k => box (hN ▸ k)) k))
    (hboxpos : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box (p.succAbove k))))
    (hexp : ((r * M ((deepLayer hL).succ) - 1 : ℕ) : ℝ) - 2 * c' ≤ -1)
    (hUmeas : Measurable
      (fun y : Fin n → ℝ => UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y))))
    (hcancel : ∀ z ∈ Set.Ioo (0:ℝ) δ, ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
      P1uG M hL hrs (hN ▸ (Fin.insertNth p z y)) * Lam0uG M hL hrs (hN ▸ (Fin.insertNth p z y))
        = P2uG M hL hrs (hN ▸ (Fin.insertNth p z y)))
    (hUpos : ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
      0 < UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y))) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ := by
  refine routeMCore_box_diverges_smearedL2 (M := M) (n := n) hN (psiMapG M hL hrs)
    (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc) p box (r * M ((deepLayer hL).succ) - 1) c' ε δ
    (fun y => UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y))) hδ hmp hemb hSpre ?_ ?_ ?_
    hboxmeas hboxmeasAll hboxpos hUmeas hexp ?_ hUpos
  · -- `RmapG` fderiv on the box
    exact fun u _ => RmapG_hasFDerivWithinAt M hL hrs hr hc _ u
  · -- `RmapG` injective on the box (`u pivot ∈ Ioo 0 δ` so `≠ 0`)
    have hsub : condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ
        ⊆ Set.univ \ {x | x (pivotCoordG M hL hrs hr hc) = 0} := by
      intro u hu
      refine ⟨Set.mem_univ u, ?_⟩
      obtain ⟨hpiv, _⟩ := hu
      simp only [Set.mem_setOf_eq, ← hp]
      exact ne_of_gt (Set.mem_Ioo.mp hpiv).1
    exact (RmapG_injOn M hL hrs hr hc Set.univ).mono (by rw [hp] at hsub ⊢; exact hsub)
  · -- `|det (DmapG u)| = |u (hN ▸ p)|^(r·M(deepLayer).succ − 1)`
    intro u _
    rw [DmapG_abs_det M hL hrs hr hc, hp]
  · -- the PEELED RATE: `routeMCore M (psiMapG (RmapG (hN ▸ insertNth p z y))) = z²·UunitG`
    intro z hz y hy
    rw [routeMCore_psiMapG_RmapG M hL hrs hr hc _ e1 e2
      (hcancel z hz y hy), frobeniusSq_P1_Hbar_cast M hL hrs hr hc,
      zuG_hN_insertNth M hL hrs hr hc hN p hp z y,
      UunitG_hN_insertNth M hL hrs hr hc hN p hp z y]

end DLNFibre.DLN.RLCT
