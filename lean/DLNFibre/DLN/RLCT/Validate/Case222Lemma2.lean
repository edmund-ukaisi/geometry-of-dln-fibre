import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Constructions

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Lemma2` — the `(2,2,2)` Lemma-2 regular change of coordinates

The Lemma-2 node of the `(2,2,2)` resolution tree (`r1-222-cover-handoff-split.md`): after the
step-1 `a`-pivot blow-up, the residual `Q = ‖Â·B‖²` (`Â = [[1,t1],[t2,t3]]`) is brought to the
resolved form `E² + F0² + (qE + δG)² + (qF0 + δH)²` by an explicit **polynomial diffeomorphism**
(det `±1`, NOT a blow-up — so it transports `rlctAtOn` by `rlctAtOn_comp_homeomorph`, the genuine
homeomorph case). On the seven chart coordinates `(t1, t2, t3, b00, b01, b10, b11)` (slot order
`0..6`, `t1` carried as a spectator):

  `E = b00 + t1·b10,  F0 = b01 + t1·b11,  δ = t3 − t1·t2,  q = t2,  G = b10,  H = b11`

with inverse `t2 = q, t3 = δ + t1·q, b00 = E − t1·G, b01 = F0 − t1·H, b10 = G, b11 = H`. Both maps
are polynomial ⟹ continuous; the bilinear shears `b00 ↦ b00 + t1·b10` etc. preserve Lebesgue
measure (elementary transvections, Jacobian `1`), so `lemma2` is a measure-preserving homeomorphism
on `Fin 7 → ℝ`.

## INTERFACE (the controller's interface-first hand-off point)

This file states the Lemma-2 node as the measure-preserving homeomorphism the cover assembly uses:
- `lemma2Equiv : (Fin 7 → ℝ) ≃ (Fin 7 → ℝ)` — the explicit polynomial bijection (proven here).
- `continuous_lemma2Fwd` / `continuous_lemma2Inv` — both directions continuous (proven here).
- `lemma2Hom : (Fin 7 → ℝ) ≃ₜ (Fin 7 → ℝ)` — packaged homeomorphism (proven here).
- `measurePreserving_lemma2` — the volume-preservation. **The next build chunk** (not yet in this
  file). Jacobian determinant is the constant `−1` (sympy-verified), so it preserves volume. ROUTE
  (Codex 2026-06-21, de-risked): a coordinate permutation (`volume_measurePreserving_piCongrLeft`)
  followed by three elementary shears `xᵢ ↦ xᵢ ± (product of other coords)`, each measure-preserving
  via `MeasurePreserving.skew_product` (`f = id`, the fibre map `x ↦ x + g(rest)` measure-preserving
  by `measurePreserving_add_right` + `ae_of_all`). The shear primitive is verified to close;
  remaining friction is the `piEquivPiSubtypeProd` coordinate-isolation (subtype `Fintype`) and the
  broader Haar imports — pure plumbing, the natural parallel hand-off boundary.

The cover assembly (`Case222Cover`) composes `lemma2Hom` between the step-1 and step-2 pivot nodes
via `rlctAtOn_comp_homeomorph`.
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

/-- The Lemma-2 forward map on the seven chart coordinates `(t1,t2,t3,b00,b01,b10,b11)` (slots
`0..6`) to `(t1,E,F0,δ,q,G,H)`: `E = b00 + t1·b10`, `F0 = b01 + t1·b11`, `δ = t3 − t1·t2`, `q = t2`,
`G = b10`, `H = b11` (`t1` carried in slot `0`). -/
noncomputable def lemma2Fwd (v : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![v 0, v 3 + v 0 * v 5, v 4 + v 0 * v 6, v 2 - v 0 * v 1, v 1, v 5, v 6]

/-- The Lemma-2 inverse map: `t2 = q`, `t3 = δ + t1·q`, `b00 = E − t1·G`, `b01 = F0 − t1·H`,
`b10 = G`, `b11 = H` (`t1` carried). -/
noncomputable def lemma2Inv (w : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![w 0, w 4, w 3 + w 0 * w 4, w 1 - w 0 * w 5, w 2 - w 0 * w 6, w 5, w 6]

theorem lemma2Inv_lemma2Fwd (v : Fin 7 → ℝ) : lemma2Inv (lemma2Fwd v) = v := by
  funext i; fin_cases i <;> simp [lemma2Fwd, lemma2Inv]

theorem lemma2Fwd_lemma2Inv (w : Fin 7 → ℝ) : lemma2Fwd (lemma2Inv w) = w := by
  funext i; fin_cases i <;> simp [lemma2Fwd, lemma2Inv]

/-- The Lemma-2 polynomial bijection on `Fin 7 → ℝ` (det `±1`; both maps polynomial). -/
noncomputable def lemma2Equiv : (Fin 7 → ℝ) ≃ (Fin 7 → ℝ) where
  toFun := lemma2Fwd
  invFun := lemma2Inv
  left_inv := lemma2Inv_lemma2Fwd
  right_inv := lemma2Fwd_lemma2Inv

theorem continuous_lemma2Fwd : Continuous lemma2Fwd := by
  unfold lemma2Fwd
  refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
    (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ continuous_const))))))
  all_goals fun_prop

theorem continuous_lemma2Inv : Continuous lemma2Inv := by
  unfold lemma2Inv
  refine Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
    (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_ (Continuous.matrixVecCons ?_
      (Continuous.matrixVecCons ?_ continuous_const))))))
  all_goals fun_prop

/-- The Lemma-2 node as a homeomorphism on `Fin 7 → ℝ` (the explicit bijection + both continuities),
for transporting `rlctAtOn` via `rlctAtOn_comp_homeomorph`. -/
noncomputable def lemma2Hom : (Fin 7 → ℝ) ≃ₜ (Fin 7 → ℝ) :=
  { lemma2Equiv with
    continuous_toFun := continuous_lemma2Fwd, continuous_invFun := continuous_lemma2Inv }

/-! ## Measure-preservation (the volume the cover assembly transports)

`lemma2Fwd` is a composition of a coordinate permutation and three elementary transvections
(shears), each volume-preserving; so it preserves `volume` (consistent with its constant Jacobian
determinant `−1`). Route: `measurePreserving_shearAt` (single-coordinate shear, reusable) ×3 + the
coordinate permutation, composed (Codex 2026-06-21). -/

/-- **Single-coordinate shear is measure-preserving.** Adding to coordinate `i` a measurable
function `g` of the *other* coordinates preserves Lebesgue volume on `Fin (n+1) → ℝ` (an elementary
transvection, Jacobian `1`). Proof: isolate coordinate `i` via `piFinSuccAbove`
(measure-preserving), shear the isolated factor (`skew_product` + translation-invariance
`measurePreserving_add_right`), reassemble. Reusable for any polynomial-shear volume argument. -/
theorem measurePreserving_shearAt {n : ℕ} (i : Fin (n + 1)) (g : (Fin n → ℝ) → ℝ)
    (hg : Measurable g) :
    MeasurePreserving
      (fun x : Fin (n + 1) → ℝ => Function.update x i (x i + g (fun k => x (i.succAbove k))))
      (volume : Measure (Fin (n + 1) → ℝ)) volume := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have hmpe : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ)) volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hshear : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (p.1 + g p.2, p.2))
      (volume : Measure (ℝ × (Fin n → ℝ))) volume := by
    rw [show (volume : Measure (ℝ × (Fin n → ℝ))) = (volume : Measure ℝ).prod volume from
      Measure.volume_eq_prod _ _]
    have hskew : MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => (p.1, p.2 + g p.1))
        ((volume : Measure (Fin n → ℝ)).prod volume)
        ((volume : Measure (Fin n → ℝ)).prod volume) :=
      MeasurePreserving.skew_product (μa := (volume : Measure (Fin n → ℝ))) (μb := volume)
        (μc := (volume : Measure ℝ)) (μd := volume) (f := id) (g := fun r x => x + g r)
        (MeasurePreserving.id volume) (by fun_prop)
        (ae_of_all _ (fun r => (measurePreserving_add_right (volume : Measure ℝ) (g r)).map_eq))
    have := (Measure.measurePreserving_swap.comp hskew).comp Measure.measurePreserving_swap
    convert this using 1
  have hcomp := hmpe.symm.comp (hshear.comp hmpe)
  convert hcomp using 1
  funext x
  change Function.update x i (x i + g (fun k => x (i.succAbove k)))
      = e.symm (((e x).1 + g (e x).2, (e x).2))
  have hsym : e.symm ((x i + g (fun k => x (i.succAbove k)), fun k => x (i.succAbove k)))
      = Fin.insertNth i (x i + g (fun k => x (i.succAbove k))) (fun k => x (i.succAbove k)) := by
    rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]; exact List.ofFn_inj.mp rfl
  rw [show (e x).1 = x i from rfl, show (e x).2 = (fun k => x (i.succAbove k)) from rfl, hsym]
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · rw [Function.update_self, Fin.insertNth_apply_same]
  · rw [Function.update_of_ne (Fin.succAbove_ne i k), Fin.insertNth_apply_succAbove]

/-- **Coordinate permutation is measure-preserving.** Reindexing `x ↦ x ∘ σ` by a permutation `σ`
preserves `volume` on `Fin 7 → ℝ` (`volume_measurePreserving_piCongrLeft`, the constant-family cast
cleared by `piCongrLeft_apply_eq_cast`). -/
theorem measurePreserving_perm (σ : Fin 7 ≃ Fin 7) :
    MeasurePreserving (fun x : Fin 7 → ℝ => x ∘ σ) (volume : Measure (Fin 7 → ℝ)) volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin 7 => ℝ) σ.symm
  convert h using 1
  funext x; funext a
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp [Function.comp]

/-- The coordinate permutation taking the post-shear layout `(t1, t2, δ, E, F0, G, H)` to the
Lemma-2 output `(t1, E, F0, δ, t2, G, H)` (slots `[0,3,4,2,1,5,6]`). -/
noncomputable def lemma2Perm : Fin 7 ≃ Fin 7 :=
  Equiv.ofBijective ![0, 3, 4, 2, 1, 5, 6] (by decide)

/-- **Lemma-2 preserves volume.** `lemma2Fwd = (· ∘ lemma2Perm) ∘ shear₂ ∘ shear₄ ∘ shear₃`: three
elementary shears (modifying slots `3,4,2` by `t1·b10`, `t1·b11`, `−t1·t2` — functions of the fixed
slots `0,1,5,6`) put the vector in the layout `(t1,t2,δ,E,F0,G,H)`, then the permutation reorders to
`(t1,E,F0,δ,t2,G,H)`. Each factor is measure-preserving (`measurePreserving_shearAt`,
`measurePreserving_perm`); the composite equals `lemma2Fwd` (`fin_cases` + `ring`). -/
theorem measurePreserving_lemma2 :
    MeasurePreserving lemma2Fwd (volume : Measure (Fin 7 → ℝ)) volume := by
  have hs3 := measurePreserving_shearAt (3 : Fin 7) (fun r => r 0 * r 4) (by fun_prop)
  have hs4 := measurePreserving_shearAt (4 : Fin 7) (fun r => r 0 * r 5) (by fun_prop)
  have hs2 := measurePreserving_shearAt (2 : Fin 7) (fun r => -(r 0 * r 1)) (by fun_prop)
  have hperm := measurePreserving_perm lemma2Perm
  have hcomp := (hperm.comp (hs2.comp (hs4.comp hs3)))
  convert hcomp using 1
  funext v
  funext j
  fin_cases j <;>
    simp [lemma2Fwd, lemma2Perm, Equiv.ofBijective, Function.update, Fin.succAbove,
      Function.comp] <;>
    ring

/-- The Lemma-2 homeomorphism is measure-preserving (`measurePreserving_lemma2`); the package the
cover assembly feeds to `rlctAtOn_comp_homeomorph`. -/
theorem measurePreserving_lemma2Hom :
    MeasurePreserving lemma2Hom (volume : Measure (Fin 7 → ℝ)) volume :=
  measurePreserving_lemma2

end DLNFibre.DLN.RLCT
