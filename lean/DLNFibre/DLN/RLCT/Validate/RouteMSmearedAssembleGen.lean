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

The radial Jacobian exponent is `r · M (deepLayerS).succ − 1 = deepRank · M_L − 1 = minAdm M − 1`
(via the banked `minAdm_eq_deepRank_mul_last`), with `r = deepRank M` — the FIDELITY constraint that
exactly the `r·c` deepest-top coords are radial-active (K's coords are FREE spectators, sheared not
radial). This module states `routeMCore_smearedGen` with `r` free (`h := r · M (deepLayerS).succ − 1`);
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
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc) (z : ℝ) (y : Fin n → ℝ) :
    zuG M hL hrs hr hc (hN ▸ (Fin.insertNth p z y)) = z := by
  rw [zuG, ← hp, hNG_cast_apply M hN (Fin.insertNth p z y) p, Fin.insertNth_apply_same]

/-- The two peeled points `hN ▸ insertNth p z y` and `hN ▸ insertNth p 0 y` agree off `pivotCoordG`. -/
theorem hNG_insertNth_agree_off_pivot {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
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
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc) (z : ℝ) (y : Fin n → ℝ) :
    UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p z y))
      = UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y)) :=
  UunitG_congr_off_pivot M hL hrs hr hc
    (hNG_insertNth_agree_off_pivot M hL hrs hr hc hN p hp z y)

/-! ## Measurability of the general-`L` chart components (the mechanical polynomial residue) -/

/-- **`prodAux` entry measurability.** For a `u`-parametrized `Params M` whose entries are measurable in
`u`, each `prodAux` entry is measurable (matrix products of measurable-entry matrices). By induction on
the layer count `k`. -/
theorem measurable_prodAux_entry (M : Fin (L + 1) → ℕ)
    (A : (Fin (routeMAmbient M) → ℝ) → Params M)
    (hA : ∀ t i j, Measurable (fun u => A u t i j)) :
    ∀ (k : ℕ) (hk : k < L + 1) (i : Fin (M 0)) (j : Fin (M ⟨k, hk⟩)),
      Measurable (fun u => prodAux M (A u) k hk i j) := by
  intro k
  induction k with
  | zero =>
      intro hk i j
      simp only [prodAux, Matrix.one_apply]
      by_cases h : i = j <;> simp only [h, if_true, if_false] <;> exact measurable_const
  | succ k ih =>
      intro hk i j
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
        apply congrArg; apply Fin.ext; simp [Fin.castSucc]
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
        apply congrArg; apply Fin.ext; simp [Fin.succ]
      have hrw : ∀ u, prodAux M (A u) (k + 1) hk i j
          = ((prodAux M (A u) k hk') * (Matrix.reindex (finCongr e1.symm) (finCongr e2.symm)
              (A u ⟨k, hkL⟩))) i j := fun u => by rw [prodAux_succ M (A u) k hk e1 e2]
      simp only [hrw, Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
      exact Finset.measurable_sum _ (fun c _ => (ih hk' i c).mul (hA ⟨k, hkL⟩ _ _))

/-- Each `frontTupleG` entry is a coordinate projection of `u` (measurable). -/
theorem measurable_frontTupleG_entry (M : Fin (L + 1) → ℕ) (t : Fin L)
    (i : Fin (M t.castSucc)) (j : Fin (M t.succ)) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => (frontTupleG M u) t i j) :=
  measurable_pi_apply _

/-- Each `frontProd` entry is measurable (`prodAux (L−1)` of the measurable `frontTupleG`). -/
theorem measurable_frontProd_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (i : Fin (M 0)) (j : Fin (M (⟨L - 1, by omega⟩ : Fin (L + 1)))) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => frontProd M (frontTupleG M u) hL i j) := by
  rw [show (fun u : Fin (routeMAmbient M) → ℝ => frontProd M (frontTupleG M u) hL i j)
      = (fun u => prodAux M (frontTupleG M u) (L - 1) (by omega) i j) from rfl]
  exact measurable_prodAux_entry M (fun u => frontTupleG M u)
    (fun t i j => measurable_frontTupleG_entry M t i j) (L - 1) (by omega) i j

/-- Each `P1uG` entry is measurable (a `frontProd` entry). -/
theorem measurable_P1uG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (i : Fin (M 0)) (a : Fin r) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => P1uG M hL hrs u i a) :=
  measurable_frontProd_entry M hL i _

/-- Each `P2uG` entry is measurable. -/
theorem measurable_P2uG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (i : Fin (M 0)) (b : Fin s) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => P2uG M hL hrs u i b) :=
  measurable_frontProd_entry M hL i _

/-- Each `Lam0uG` entry is measurable (the `(P₁ᵀP₁)⁻¹P₁ᵀP₂` chain via `measurable_lamEntry`). -/
theorem measurable_Lam0uG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (a : Fin r) (b : Fin s) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => Lam0uG M hL hrs u a b) :=
  measurable_lamEntry (fun u => P1uG M hL hrs u) (fun u => P2uG M hL hrs u)
    (fun i a => measurable_P1uG_entry M hL hrs i a)
    (fun i b => measurable_P2uG_entry M hL hrs i b) a b

/-- Each `SbotuG` entry is a coordinate projection (measurable). -/
theorem measurable_SbotuG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (b : Fin s) (j : Fin (M ((deepLayerS hL).succ))) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => SbotuG M hL hrs u b j) :=
  measurable_pi_apply _

/-- Each `HbarUnitG` entry is measurable (a coordinate projection or the constant `1`). -/
theorem measurable_HbarUnitG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (a : Fin r) (j : Fin (M ((deepLayerS hL).succ))) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => HbarUnitG M hL hrs hr hc u a j) := by
  unfold HbarUnitG
  by_cases hpiv : coordOfG M (topSlotG M hL hrs a j) = pivotCoordG M hL hrs hr hc
  · simp only [if_pos hpiv]; exact measurable_const
  · simp only [if_neg hpiv]; exact measurable_pi_apply _

/-- `u ↦ UunitG M hL hrs hr hc u` is measurable (a finite sum of squares of `P₁·H̄_unit` entries). -/
theorem measurable_UunitG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ)) :
    Measurable (fun u : Fin (routeMAmbient M) → ℝ => UunitG M hL hrs hr hc u) := by
  unfold UunitG
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  refine Measurable.pow_const ?_ 2
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ (fun a _ =>
    (measurable_P1uG_entry M hL hrs i a).mul (measurable_HbarUnitG_entry M hL hrs hr hc a j))

/-- `u' ↦ shiftFullG M hL hrs u' m` is measurable (a finite signed sum of `Λ₀`/`S_bot` products). -/
theorem measurable_shiftFullG_coord (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (m : Fin (routeMAmbient M)) :
    Measurable (fun u' : Fin (routeMAmbient M) → ℝ => shiftFullG M hL hrs u' m) := by
  unfold shiftFullG
  refine (Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun j _ => ?_))).neg
  by_cases h : coordOfG M (topSlotG M hL hrs a j) = m
  · simp only [if_pos h, Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun b _ =>
      (measurable_Lam0uG_entry M hL hrs a b).mul (measurable_SbotuG_entry M hL hrs b j))
  · simp only [if_neg h]; exact measurable_const

/-- `shiftCoreG` is measurable (reconstruct via the `splitOfCoreSet.symm` ME, then `shiftFullG`). -/
theorem measurable_shiftCoreG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) : Measurable (shiftCoreG M hL hrs) := by
  apply measurable_pi_iff.2
  intro jc
  unfold shiftCoreG
  have hrecon : Measurable (fun q : (Fin 0 → ℝ) × (Fin (topCoordsG M hL hrs)ᶜ.card → ℝ) =>
      (splitOfCoreSet (topCoordsG M hL hrs)).symm
        (q.1, ((0 : Fin (topCoordsG M hL hrs).card → ℝ), q.2))) :=
    (splitOfCoreSet (topCoordsG M hL hrs)).symm.measurable.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact (measurable_shiftFullG_coord M hL hrs _).comp hrecon

/-! ## `psiMapG` measure-preserving + a measurable embedding

`psiMapG = paramsEquivFlat ∘ (flatEquivOf slotEquivG).symm ∘ shearMBody`: the two outer factors are
banked measure-preserving `MeasurableEquiv`s; `shearMBody` is MP for the measurable `shiftCoreG`. -/

/-- `psiMapG` is measure-preserving (the three-factor composition, `shearMBody` MP via
`measurable_shiftCoreG`, the two flat `MeasurableEquiv`s MP). -/
theorem measurePreserving_psiMapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) :
    MeasurePreserving (psiMapG M hL hrs)
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume := by
  have hshear : MeasurePreserving (shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs))
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume :=
    measurePreserving_shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs)
      (measurable_shiftCoreG M hL hrs)
  have hpack : MeasurePreserving (⇑(flatEquivOf M (slotEquivG M)).symm)
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) (volume : Measure (Params M)) :=
    (measurePreserving_flatEquivOf M (slotEquivG M)).symm _
  exact (measurePreserving_paramsEquivFlat M).comp (hpack.comp hshear)

/-- `psiMapG` is a measurable embedding (the composition of the shear `MeasurableEmbedding` and the two
flat `MeasurableEquiv`s' embeddings). -/
theorem measurableEmbedding_psiMapG (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) :
    MeasurableEmbedding (psiMapG M hL hrs) := by
  have h1 : MeasurableEmbedding (shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs)) :=
    measurableEmbedding_shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs)
      (measurable_shiftCoreG M hL hrs)
  have h2 : MeasurableEmbedding (⇑(flatEquivOf M (slotEquivG M)).symm) :=
    (flatEquivOf M (slotEquivG M)).symm.measurableEmbedding
  have h3 : MeasurableEmbedding (⇑(paramsEquivFlat M)) := (paramsEquivFlat M).measurableEmbedding
  have hpsi : psiMapG M hL hrs = (⇑(paramsEquivFlat M) ∘ ⇑(flatEquivOf M (slotEquivG M)).symm)
      ∘ shearMBody (topCoordsG M hL hrs) (shiftCoreG M hL hrs) := rfl
  rw [hpsi]
  exact (h3.comp h2).comp h1

/-! ## The general-`L` smeared box-divergence assembly

`routeMCore_smearedGen`: the general-`L` conditioned-box smeared box-divergence, assembled from the
DECODE-derived rate (`routeMCore_psiMapG_RmapG`) + the M-agnostic engine
`routeMCore_box_diverges_smearedL2`. The mechanical `z`/`U` peel is folded in; only the
genuinely-conditioned analytic inputs remain (the cancellation on each peeled point, FIELD-A
containment, `U`-positivity), plus the `ψ` measure-theoretic facts (MP + a measurable embedding) and
the `Uy` measurability — the mechanical `psiMapG`/`UunitG` plumbing, isolated as named hypotheses
(discharged per-family or by the `frontProd`-polynomial-measurability residue). -/

/-- **The general-`L` conditioned-box boundary-smeared box-divergence.** For `M : Fin (L+1) → ℕ`,
`0 < L`, the front-bottleneck split `r + s = M (deepLayerS hL).castSucc`, `0 < r`, `0 < M
(deepLayerS).succ`, `routeMAmbient M = n + 1`, and the binding pivot `p` (`hN ▸ p = pivotCoordG`): the
achiever box integral `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`, given

* `ψ := psiMapG` measure-preserving + a measurable embedding (the mechanical shear-∘-reshape facts);
* the exponent `(r·M(deepLayerS).succ − 1 : ℝ) − 2c' ≤ −1` (`= minAdm − 1 − 2c'`, from `c' ≥ ½·minAdm`);
* the shear cancellation `P₁·Λ₀ = P₂` on each peeled point (off the pole — K-free-spectator);
* `U`-positivity `0 < UunitG (hN ▸ insertNth p 0 y)` on the conditioned rest box;
* FIELD-A containment + box measurability/positivity + `Uy` measurability.

The chart facts (radial fderiv/injOn/det, the peeled rate's `z²·UunitG` form) are DISCHARGED from the
general-`L` radial machinery + `routeMCore_psiMapG_RmapG`. -/
theorem routeMCore_smearedGen {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
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
    (hexp : ((r * M ((deepLayerS hL).succ) - 1 : ℕ) : ℝ) - 2 * c' ≤ -1)
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
    (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc) p box (r * M ((deepLayerS hL).succ) - 1) c' ε δ
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
  · -- `|det (DmapG u)| = |u (hN ▸ p)|^(r·M(deepLayerS).succ − 1)`
    intro u _
    rw [DmapG_abs_det M hL hrs hr hc, hp]
  · -- the PEELED RATE: `routeMCore M (psiMapG (RmapG (hN ▸ insertNth p z y))) = z²·UunitG`
    intro z hz y hy
    rw [routeMCore_psiMapG_RmapG M hL hrs hr hc _ e1 e2
      (hcancel z hz y hy), frobeniusSq_P1_Hbar_cast M hL hrs hr hc,
      zuG_hN_insertNth M hL hrs hr hc hN p hp z y,
      UunitG_hN_insertNth M hL hrs hr hc hN p hp z y]

/-! ## The general-`L` `SmearedAchieverChart` builder + `hSmeared`

`smearedChartGen`: build a `SmearedAchieverChart M` for arbitrary `L` from the structural data
(`hrs`/`hr`/`hc`/`hp`, the exponent-matching split `r = deepRank`, `h = minAdm − 1`) + a per-ε
conditioned-box-data supplier (the genuinely-conditioned analytic inputs — box radius, Field-A,
cancellation, `U`-positivity — exactly what `smearedChartData231` supplies at L=2). The chart's
generic maps and the peeled rate are DISCHARGED from the general-`L` machinery. Feeding this into the
already-∀L `hSmeared_of_smearedChart` gives the spine's `hSmeared` for `M`. -/

/-- **The per-ε conditioned chart data at general `L`** (the `SmearedChartData` for `psiMapG`/`RmapG`/
`DmapG`, radial exponent `r·M(deepLayerS).succ − 1`), built from the supplied conditioned box + its
analytic inputs. The `hRate` field is discharged from the rate bridge + the `z`/`U` peel; `Uy :=
UunitG (hN ▸ insertNth p 0 ·)` is the z-free unit, measurable via `measurable_UunitG`. -/
noncomputable def smearedChartDataGen {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc)
    (ε : ℝ)
    (δ₀ : ℝ) (box₀ : Fin (n + 1) → Set ℝ) (hδ₀ : 0 < δ₀)
    (hSpre : condBox (hN ▸ p) (fun k => box₀ (hN ▸ k)) δ₀
      ⊆ (fun u => psiMapG M hL hrs (RmapG M hL hrs hr hc u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRinj : Set.InjOn (RmapG M hL hrs hr hc) (condBox (hN ▸ p) (fun k => box₀ (hN ▸ k)) δ₀))
    (hboxmeas : ∀ k, MeasurableSet (box₀ (p.succAbove k)))
    (hboxmeasAll : ∀ k : Fin (routeMAmbient M), MeasurableSet ((fun k => box₀ (hN ▸ k)) k))
    (hboxpos : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k))))
    (hcancel : ∀ z ∈ Set.Ioo (0:ℝ) δ₀, ∀ y ∈ Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k)),
      P1uG M hL hrs (hN ▸ (Fin.insertNth p z y)) * Lam0uG M hL hrs (hN ▸ (Fin.insertNth p z y))
        = P2uG M hL hrs (hN ▸ (Fin.insertNth p z y)))
    (hUpos : ∀ y ∈ Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k)),
      0 < UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y))) :
    SmearedChartData M n hN (psiMapG M hL hrs) (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc) p
      (r * M ((deepLayerS hL).succ) - 1) ε where
  δ := δ₀
  box := box₀
  Uy := fun y => UunitG M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y))
  hδ := hδ₀
  hSpre := hSpre
  hRderiv := fun u _ => RmapG_hasFDerivWithinAt M hL hrs hr hc _ u
  hRinj := hRinj
  hRdet := fun u _ => by rw [DmapG_abs_det M hL hrs hr hc, hp]
  hboxmeas := hboxmeas
  hboxmeasAll := hboxmeasAll
  hboxpos := hboxpos
  hUmeas := (measurable_UunitG M hL hrs hr hc).comp (by
    have key : ∀ (N : ℕ) (h : N = n + 1),
        Measurable (fun y : Fin n → ℝ => (h ▸ (Fin.insertNth p (0:ℝ) y) : Fin N → ℝ)) := by
      intro N h; subst h
      exact measurable_pi_iff.2 (fun i => by
        rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨k, rfl⟩
        · simp only [Fin.insertNth_apply_same]; exact measurable_const
        · simp only [Fin.insertNth_apply_succAbove]; exact measurable_pi_apply k)
    exact key _ hN)
  hRate := fun z hz y hy => by
    rw [routeMCore_psiMapG_RmapG M hL hrs hr hc _ e1 e2 (hcancel z hz y hy),
      frobeniusSq_P1_Hbar_cast M hL hrs hr hc,
      zuG_hN_insertNth M hL hrs hr hc hN p hp z y,
      UunitG_hN_insertNth M hL hrs hr hc hN p hp z y]
  hUpos := hUpos

/-- **The general-`L` `SmearedAchieverChart` for `M`.** Bundles the general-`L` chart maps
(`psiMapG`/`RmapG`/`DmapG`, MP + a measurable embedding), the pivot `p`, radial exponent
`r·M(deepLayerS).succ − 1`, and the per-ε conditioned data supplier (`smearedChartDataGen`). The
exponent field `hexp` uses the caller-supplied `minAdm` match `hminadm : r · M(deepLayerS).succ =
minAdm M` (from `minAdm_eq_deepRank_mul_last` at `r = deepRank`) with `1 ≤ minAdm M`, giving
`(minAdm − 1) − minAdm = −1 ≤ −1`. -/
noncomputable def smearedChartGen {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hminadm : r * M ((deepLayerS hL).succ) = minAdm M) (hminpos : 1 ≤ minAdm M)
    (dataGen : ∀ ε : ℝ, 0 < ε →
      SmearedChartData M n hN (psiMapG M hL hrs) (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc) p
        (r * M ((deepLayerS hL).succ) - 1) ε) :
    SmearedAchieverChart M where
  n := n
  hN := hN
  ψ := psiMapG M hL hrs
  R := RmapG M hL hrs hr hc
  D := DmapG M hL hrs hr hc
  p := p
  h := r * M ((deepLayerS hL).succ) - 1
  hmp := measurePreserving_psiMapG M hL hrs
  hemb := measurableEmbedding_psiMapG M hL hrs
  hexp := by
    -- `(minAdm − 1) − 2·(minAdm/2) = −1 ≤ −1`
    rw [hminadm]
    have h1 : (1 : ℕ) ≤ minAdm M := hminpos
    have : ((minAdm M - 1 : ℕ) : ℝ) = (minAdm M : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; norm_num
    rw [this]; ring_nf; linarith
  data := dataGen

/-- **The spine's `hSmeared`, for `M`, from the general-`L` chart.** Given the structural data + the
per-ε conditioned-data supplier, the boundary-smeared branch's `hSmeared` holds for `M`: for `2 ≤ L`
and `BoundarySmeared M`, the achiever box integral diverges (`c' ≥ ½·minAdm M`, `ε > 0`). Feeds
`smearedChartGen` into the already-∀L `hSmeared_of_smearedChart`. -/
theorem hSmeared_smearedGen {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (hminadm : r * M ((deepLayerS hL).succ) = minAdm M) (hminpos : 1 ≤ minAdm M)
    (dataGen : ∀ ε : ℝ, 0 < ε →
      SmearedChartData M n hN (psiMapG M hL hrs) (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc) p
        (r * M ((deepLayerS hL).succ) - 1) ε)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    (2 ≤ L) → BoundarySmeared M →
      ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  hSmeared_of_smearedChart M
    (fun _ => smearedChartGen M hL hrs hr hc hN p hminadm hminpos dataGen) c' hc' ε hε

end DLNFibre.DLN.RLCT
