import DLNFibre.DLN.RLCT.Foundations.S1Fubini

/-!
# `DLNFibre.DLN.RLCT.Foundations.CoreShearMP` — the core-shear is measure-preserving (the 2 MP helpers)

The two measure-preserving helpers cobuild-sub34's `coreAbsorb_rlct` wiring consumes (Route A, Codex
g165): the product-`volume` REASSOCIATION `Reg × (Core × Spec) ≃ (Reg × Spec) × Core` and the
fiber-SHEAR `(reg, core, spec) ↦ (reg, core + shift(reg,spec), spec)`. Both are pure S1-Fubini idiom
(`measurePreserving_shearAt`'s `skew_product` + `measurePreserving_add_right` template), filled
STANDALONE here so cobuild-sub34 wires them into `coreAbsorb_rlct` (`rlctAtOn_comp_homeomorph` on the
det-1 `coreShearHomeo`).

These are MECHANICAL + TYPE-PINNED — their truth is carried by the build (one cannot prove a false
`MeasurePreserving`) and their fit by cobuild-sub34's consuming wiring (a 2-party prover/consumer
check). The geometric content (the Schur shift, `loss_squeeze`, the absorptions) stays cobuild-sub34's.

`shift` is arbitrary continuous — the concrete gauge-dependent Schur shift `−Z_s(I+X_s)⁻¹Y_s` is
plugged in by `deepest_coreAbsorb_exists` (PIN 0, cobuild-sub34's).
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

/-- **The core reassociation is measure-preserving.** The product-`volume` regrouping
`(Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) ≃ ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ)`
(reg, (core, spec)) ↦ ((reg, spec), core) preserves volume — the carrier for the core-shear MP.
Inner swap `(core, spec) ↦ (spec, core)` then `prodAssoc.symm`, each via the product-`volume` form. -/
theorem measurePreserving_coreReassoc (a b c : ℕ) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) => ((q.1, q.2.2), q.2.1))
      volume volume := by
  set A := Fin a → ℝ; set Bb := Fin b → ℝ; set C := Fin c → ℝ
  -- Step 1: swap the inner `(core, spec) ↦ (spec, core)` under `id` on the reg factor.
  have hswap : MeasurePreserving (Prod.swap : Bb × C → C × Bb) volume volume := by
    rw [show (volume : Measure (Bb × C)) = (volume : Measure Bb).prod volume from
          Measure.volume_eq_prod _ _,
      show (volume : Measure (C × Bb)) = (volume : Measure C).prod volume from
          Measure.volume_eq_prod _ _]
    exact Measure.measurePreserving_swap
  have h1 : MeasurePreserving
      (Prod.map (id : A → A) (Prod.swap : Bb × C → C × Bb)) volume volume := by
    rw [show (volume : Measure (A × (Bb × C))) = (volume : Measure A).prod volume from
          Measure.volume_eq_prod _ _,
      show (volume : Measure (A × (C × Bb))) = (volume : Measure A).prod volume from
          Measure.volume_eq_prod _ _]
    exact (MeasurePreserving.id (volume : Measure A)).prod hswap
  -- Step 2: `prodAssoc.symm`: `reg × (spec × core) ↦ (reg × spec) × core`.
  have h2 : MeasurePreserving
      (fun q : A × (C × Bb) => ((q.1, q.2.1), q.2.2)) volume volume := by
    rw [show (volume : Measure (A × (C × Bb)))
          = (volume : Measure A).prod ((volume : Measure C).prod volume) from by
          rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
      show (volume : Measure ((A × C) × Bb))
          = ((volume : Measure A).prod volume).prod volume from by
          rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
    exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc (volume : Measure A) volume volume)
  exact h2.comp h1

/-- **The core-shear is measure-preserving.** For any continuous
`shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)`, the fiber-shear
`(reg, core, spec) ↦ (reg, core + shift (reg, spec), spec)` preserves the product `volume`. The shear
is a det-1 fiber translation: regroup to `(reg × spec) × core` (`coreReassoc`), `skew_product` over the
`reg × spec` base with per-fiber translation invariance (`measurePreserving_add_right`), regroup back.
Consumed by `coreAbsorb_rlct` via `rlctAtOn_comp_homeomorph` on the `coreShearHomeo`. -/
theorem measurePreserving_coreShear (a b c : ℕ)
    (shift : (Fin a → ℝ) × (Fin c → ℝ) → (Fin b → ℝ)) (hshift : Continuous shift) :
    MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
        (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
      volume volume := by
  have hmshift : Measurable shift := hshift.measurable
  -- regroup `reg × (core × spec) ↦ (reg × spec) × core` (MP, `coreReassoc`).
  have hreassoc : MeasurePreserving
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) => ((q.1, q.2.2), q.2.1))
      volume volume :=
    measurePreserving_coreReassoc a b c
  -- the skew on `(reg × spec) × core`: `((rs), core) ↦ ((rs), core + shift rs)`, det-1 translation.
  -- the measurability of `uncurry g` is proven explicitly (not via `fun_prop`, which overflows the
  -- elaborator stack on the `skew_product`-inferred goal at this Pi-valued shape).
  have hskew : MeasurePreserving
      (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1, p.2 + shift p.1))
      ((volume : Measure ((Fin a → ℝ) × (Fin c → ℝ))).prod volume)
      ((volume : Measure ((Fin a → ℝ) × (Fin c → ℝ))).prod volume) :=
    MeasurePreserving.skew_product
      (μa := (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ)))) (μb := volume)
      (μc := (volume : Measure (Fin b → ℝ))) (μd := volume)
      (f := id) (g := fun rs core => core + shift rs)
      (MeasurePreserving.id volume)
      (measurable_snd.add (hmshift.comp measurable_fst))
      (ae_of_all _ (fun rs =>
        (measurePreserving_add_right (volume : Measure (Fin b → ℝ)) (shift rs)).map_eq))
  have hskew' : MeasurePreserving
      (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1, p.2 + shift p.1))
      volume volume := by
    rw [show (volume : Measure (((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ)))
          = (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ))).prod volume from
      Measure.volume_eq_prod _ _]
    exact hskew
  -- regroup back `(reg × spec) × core ↦ reg × (core × spec)` (= `coreReassoc.symm`, MP).
  have hreassoc' : MeasurePreserving
      (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1.1, (p.2, p.1.2)))
      volume volume := by
    -- `((rs), core) ↦ (reg, (core, spec))`: `prodAssoc` then inner swap `(spec,core)↦(core,spec)`.
    have hassoc : MeasurePreserving
        (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1.1, (p.1.2, p.2)))
        volume volume := by
      rw [show (volume : Measure (((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ)))
            = ((volume : Measure (Fin a → ℝ)).prod volume).prod volume from by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _],
        show (volume : Measure ((Fin a → ℝ) × ((Fin c → ℝ) × (Fin b → ℝ))))
            = (volume : Measure (Fin a → ℝ)).prod
                ((volume : Measure (Fin c → ℝ)).prod volume) from by
            rw [Measure.volume_eq_prod _ _, Measure.volume_eq_prod _ _]]
      exact measurePreserving_prodAssoc (volume : Measure (Fin a → ℝ)) volume volume
    have hswapinner : MeasurePreserving
        (Prod.map (id : (Fin a → ℝ) → (Fin a → ℝ))
          (Prod.swap : (Fin c → ℝ) × (Fin b → ℝ) → (Fin b → ℝ) × (Fin c → ℝ)))
        volume volume := by
      rw [show (volume : Measure ((Fin a → ℝ) × ((Fin c → ℝ) × (Fin b → ℝ))))
            = (volume : Measure (Fin a → ℝ)).prod volume from Measure.volume_eq_prod _ _,
        show (volume : Measure ((Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ))))
            = (volume : Measure (Fin a → ℝ)).prod volume from Measure.volume_eq_prod _ _]
      refine (MeasurePreserving.id (volume : Measure (Fin a → ℝ))).prod ?_
      rw [show (volume : Measure ((Fin c → ℝ) × (Fin b → ℝ)))
            = (volume : Measure (Fin c → ℝ)).prod volume from Measure.volume_eq_prod _ _,
        show (volume : Measure ((Fin b → ℝ) × (Fin c → ℝ)))
            = (volume : Measure (Fin b → ℝ)).prod volume from Measure.volume_eq_prod _ _]
      exact Measure.measurePreserving_swap
    exact hswapinner.comp hassoc
  -- the composite `coreReassoc.symm ∘ skew ∘ coreReassoc` IS the core-shear (pointwise `rfl`).
  have hcomp := (hreassoc'.comp hskew').comp hreassoc
  have hfun :
      (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) =>
          (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2)))
        = (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1.1, (p.2, p.1.2)))
            ∘ (fun p : ((Fin a → ℝ) × (Fin c → ℝ)) × (Fin b → ℝ) => (p.1, p.2 + shift p.1))
            ∘ (fun q : (Fin a → ℝ) × ((Fin b → ℝ) × (Fin c → ℝ)) => ((q.1, q.2.2), q.2.1)) := by
    funext q; rfl
  rw [hfun]; exact hcomp

end DLNFibre.DLN.RLCT
