import DLNFibre.DLN.RLCT.Validate.RouteMSmearedAssembleGen
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedCancelGen

/-!
# `RouteMSmearedDetData` — the general-`L` chart data from the TWO box determinants

Wraps `smearedChartDataGen` (`RouteMSmearedAssembleGen`) by discharging its two genuinely-analytic
per-point inputs — the shear cancellation `hcancel` and the unit positivity `hUpos` — from the SAME
two determinant conditions, via the general-`L` reduction of `RouteMSmearedCancelGen`:

* the Gram `det ((P1uG u)ᵀ (P1uG u)) ≠ 0` (`P₁` full column rank `r`);
* the waist-block `det (V[:, deepWidthEquiv ∘ inl]) ≠ 0` for the width-`r` waist factorization
  `frontProd u = U · V`.

The KEY structural input (`pen-and-paper` waist verdict, unconditional in the smeared regime): a front
waist layer `q ≤ L−1` with `M ⟨q,_⟩ = r`. Given the waist and the two per-point dets on the source box,
this produces a `SmearedChartData` — so the per-family work collapses to: the box + Field-A containment
+ `RmapG`-injectivity + measurability + the two box determinants (both diagonal-dominance, downstream).

* `smearedChartDataGen_of_dets` — the `SmearedChartData` from a waist + the two per-point dets, the box,
  Field-A, `RmapG`-injectivity, and measurability.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-- **The general-`L` chart data from the two box determinants.** Feeds `smearedChartDataGen` by
discharging its `hcancel`/`hUpos` fields from the two per-point determinant conditions (Gram +
waist-block) via `hcancelG_of_waist` / `UunitG_pos_of_gram_det_ne`.

The waist `q ≤ L−1` (`M ⟨q,_⟩ = r`) supplies the width-`r` factorization; `hGram` (the Gram det at each
peeled cancellation point AND at each `z=0` positivity point) and `hWaist` (the waist-block det at each
cancellation point) are the two box conditions. All the mechanical chart fields (fderiv, det, `Uy`
measurability, the rate) come from `smearedChartDataGen`. -/
noncomputable def smearedChartDataGen_of_dets {n : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayerS hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayerS hL).succ))
    (hN : routeMAmbient M = n + 1) (p : Fin (n + 1))
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (hp : (hN ▸ p : Fin (routeMAmbient M)) = pivotCoordG M hL hrs hr hc)
    (q : ℕ) (hq : q < L + 1) (hqL : q ≤ L - 1) (hMq : M ⟨q, hq⟩ = r)
    (ε : ℝ) (δ₀ : ℝ) (box₀ : Fin (n + 1) → Set ℝ) (hδ₀ : 0 < δ₀)
    (hSpre : condBox (hN ▸ p) (fun k => box₀ (hN ▸ k)) δ₀
      ⊆ (fun u => psiMapG M hL hrs (RmapG M hL hrs hr hc u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRinj : Set.InjOn (RmapG M hL hrs hr hc) (condBox (hN ▸ p) (fun k => box₀ (hN ▸ k)) δ₀))
    (hboxmeas : ∀ k, MeasurableSet (box₀ (p.succAbove k)))
    (hboxmeasAll : ∀ k : Fin (routeMAmbient M), MeasurableSet ((fun k => box₀ (hN ▸ k)) k))
    (hboxpos : 0 < (volume : Measure (Fin n → ℝ))
      (Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k))))
    (hGram : ∀ z ∈ Set.Ioo (0:ℝ) δ₀, ∀ y ∈ Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k)),
      ((P1uG M hL hrs (hN ▸ (Fin.insertNth p z y))).transpose
        * P1uG M hL hrs (hN ▸ (Fin.insertNth p z y))).det ≠ 0)
    (hGram0 : ∀ y ∈ Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k)),
      ((P1uG M hL hrs (hN ▸ (Fin.insertNth p (0:ℝ) y))).transpose
        * P1uG M hL hrs (hN ▸ (Fin.insertNth p (0:ℝ) y))).det ≠ 0)
    (hWaist : ∀ z ∈ Set.Ioo (0:ℝ) δ₀, ∀ y ∈ Set.univ.pi (fun k : Fin n => box₀ (p.succAbove k)),
      ∀ (U : Matrix (Fin (M 0)) (Fin r) ℝ) (V : Matrix (Fin r) (Fin (M ⟨L - 1, by omega⟩)) ℝ),
        frontProd M (frontTupleG M (hN ▸ (Fin.insertNth p z y))) hL = U * V →
          (V.submatrix (id : _ → _)
            (fun k : Fin r => deepWidthEquiv (hrsAtom_of_hrs hL hrs) (Sum.inl k))).det ≠ 0) :
    SmearedChartData M n hN (psiMapG M hL hrs) (RmapG M hL hrs hr hc) (DmapG M hL hrs hr hc) p
      (r * M ((deepLayerS hL).succ) - 1) ε :=
  smearedChartDataGen M hL hrs hr hc hN p e1 e2 hp ε δ₀ box₀ hδ₀ hSpre hRinj
    hboxmeas hboxmeasAll hboxpos
    (fun z hz y hy => hcancelG_of_waist M hL hrs (hN ▸ (Fin.insertNth p z y)) q hq hqL hMq
      (hWaist z hz y hy) (hGram z hz y hy))
    (fun y hy => UunitG_pos_of_gram_det_ne M hL hrs hr hc (hN ▸ (Fin.insertNth p (0:ℝ) y))
      (hGram0 y hy))

end DLNFibre.DLN.RLCT
