/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.ChartEvalLemma

/-!
# `DLNFibre.Core.ChartEvalGaugeCommute` — the gauge-evaluation commute (Ψ descent, seam A.4)

The gauge-evaluation commute underlying the chart-evaluation lemma (thread 31, Codex route-(b)): for a
gauge `P : BaseChangeGroup (k := SchurLoc) d` and a chart-point evaluation `g : SchurLoc →ₐ[k] k`, the
substitution `aevalTower g (canonicalCoord B)` applied to the gauged generic coordinate
`gaugeSub d P x` is the corresponding entry of the **evaluated gauge** acting on `B`:

> `(aevalTower g (canonicalCoord B)) (gaugeSub d P x) = (baseChange (evalGauge g P) B) x.1 x.2.1 x.2.2`,

where `evalGauge g P : BaseChangeGroup (k := k) d := fun v ↦ Units.map g.mapMatrix.toMonoidHom (P v)`
pushes each SchurLoc gauge unit through `g` at the **unit** level (so `⁻¹` commutes for free,
`Units.coe_map_inv` — no `Matrix.nonsing_inv` transport).

The proof: `gaugeSub d P x = baseChange (liftGauge d P) (genericTuple d) x.1 x.2.1 x.2.2`, a matrix
entry over `MvPolynomial (RepCoord d) SchurLoc`. The ring hom `aevalTower g (canonicalCoord B)`
commutes with the matrix products in `baseChange`; on the `C`-lifted gauge units it is `g` entrywise
(`aevalTower_C`), and on the generic factor it is `canonicalCoord B` (`aevalTower_X`).

## Main results
- `evalGauge` — the `k`-valued evaluated gauge `Units.map g.mapMatrix` of a `SchurLoc` gauge.
- `aevalTower_gaugeSub` — the gauge-evaluation commute (per coordinate).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **The evaluated gauge.** From a chart-point evaluation `g : SchurLoc →ₐ[k] k` and a `SchurLoc`
gauge `P : BaseChangeGroup (k := SchurLoc) d`, the `k`-valued gauge `evalGauge g P` pushing each unit
matrix through `g` at the **unit** level (`Units.map` of `g.mapMatrix`). Inverses commute for free
(`Units.coe_map_inv`), avoiding any `Matrix.nonsing_inv` transport. -/
noncomputable def evalGauge (q p r : ℕ) (g : SchurLoc (k := k) q p r →ₐ[k] k)
    {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := SchurLoc (k := k) q p r) d) :
    BaseChangeGroup (k := k) d :=
  fun v ↦ Units.map (RingHom.mapMatrix (g : SchurLoc (k := k) q p r →+* k)).toMonoidHom (P v)

/-- The value of an evaluated gauge unit is the `g`-image (entrywise) of the original unit matrix. -/
theorem evalGauge_val (q p r : ℕ) (g : SchurLoc (k := k) q p r →ₐ[k] k)
    {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := SchurLoc (k := k) q p r) d) (v : Fin (N + 1)) :
    Units.val (evalGauge q p r g P v)
      = (Units.val (P v)).map (g : SchurLoc (k := k) q p r →+* k) := by
  rw [evalGauge, Units.coe_map]
  rfl

/-- The inverse value of an evaluated gauge unit is the `g`-image of the original inverse (unit-level
`Units.coe_map_inv` — no `Matrix.nonsing_inv` transport). -/
theorem evalGauge_inv_val (q p r : ℕ) (g : SchurLoc (k := k) q p r →ₐ[k] k)
    {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := SchurLoc (k := k) q p r) d) (v : Fin (N + 1)) :
    Units.val ((evalGauge q p r g P v)⁻¹)
      = (Units.val ((P v)⁻¹)).map (g : SchurLoc (k := k) q p r →+* k) := by
  rw [evalGauge, Units.coe_map_inv]
  rfl

/-- The ring hom `aevalTower g (canonicalCoord B)` carries the `C`-lifted gauge matrix `liftGauge d P v`
to the `g`-image `(P v).val.map g` (constants fixed by `aevalTower_C`, entrywise). -/
theorem map_aevalTower_liftGauge (q p r : ℕ) (g : SchurLoc (k := k) q p r →ₐ[k] k)
    {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := SchurLoc (k := k) q p r) d)
    (B : Tuple (k := k) d) (v : Fin (N + 1)) :
    (Units.val (liftGauge d P v)).map (aevalTower g (canonicalCoord d B) : _ →+* k)
      = Units.val (evalGauge q p r g P v) := by
  rw [liftGauge_val_eq, evalGauge_val]
  funext a b
  rw [Matrix.map_apply, Matrix.map_apply]
  exact aevalTower_C _ _ _

/-- Same, for the inverse gauge unit. -/
theorem map_aevalTower_liftGauge_inv (q p r : ℕ) (g : SchurLoc (k := k) q p r →ₐ[k] k)
    {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := SchurLoc (k := k) q p r) d)
    (B : Tuple (k := k) d) (v : Fin (N + 1)) :
    (Units.val ((liftGauge d P v)⁻¹)).map (aevalTower g (canonicalCoord d B) : _ →+* k)
      = Units.val ((evalGauge q p r g P v)⁻¹) := by
  rw [liftGauge_inv_val_eq, evalGauge_inv_val]
  funext a b
  rw [Matrix.map_apply, Matrix.map_apply]
  exact aevalTower_C _ _ _

/-- **The gauge-evaluation commute (per coordinate).** Applying the chart-point substitution
`aevalTower g (canonicalCoord B)` to the gauged generic coordinate `gaugeSub d P x` gives the
corresponding entry of the evaluated gauge acting on `B`. The ring hom commutes with the `baseChange`
matrix products; constants go through `g`, the generic factor goes to `canonicalCoord B`. -/
theorem aevalTower_gaugeSub (q p r : ℕ) (g : SchurLoc (k := k) q p r →ₐ[k] k)
    {d : Fin (N + 1) → ℕ} (P : BaseChangeGroup (k := SchurLoc (k := k) q p r) d)
    (B : Tuple (k := k) d) (x : RepCoord d) :
    aevalTower g (canonicalCoord d B) (gaugeSub d P x)
      = (baseChange (evalGauge q p r g P) B) x.1 x.2.1 x.2.2 := by
  obtain ⟨i, a, b⟩ := x
  -- LHS: `gaugeSub d P ⟨i,a,b⟩ = (L · X_i · H⁻¹) a b`, a matrix entry over `MvPolynomial _ SchurLoc`.
  -- RHS: `baseChange (evalGauge g P) B i a b = (Lₖ · B_i · Hₖ⁻¹) a b`.
  show aevalTower g (canonicalCoord d B)
      (baseChange (liftGauge d P) (genericTuple d) i a b)
    = baseChange (evalGauge q p r g P) B i a b
  rw [baseChange_apply, baseChange_apply]
  -- push the ring hom `φ = aevalTower g cc` through the rectangular triple product `L · X_i · H⁻¹`
  -- via `Matrix.map_mul` (the leg lemmas give the gauge factors; `hmid` gives the middle).
  set φ := (aevalTower g (canonicalCoord d B) : MvPolynomial (RepCoord d)
    (SchurLoc (k := k) q p r) →+* k) with hφ
  have hmid : (genericTuple d i).map φ = B i := by
    funext rr cc
    rw [Matrix.map_apply, hφ, genericTuple_apply]
    show aevalTower g (canonicalCoord d B) (X _) = _
    rw [aevalTower_X]
    rfl
  have hmat : ((Units.val (liftGauge d P i.succ) * genericTuple d i
        * Units.val ((liftGauge d P i.castSucc)⁻¹) :
        Matrix (Fin (d i.succ)) (Fin (d i.castSucc))
          (MvPolynomial (RepCoord d) (SchurLoc (k := k) q p r))).map φ)
      = (Units.val (evalGauge q p r g P i.succ) * B i
        * Units.val ((evalGauge q p r g P i.castSucc)⁻¹) :
        Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k) := by
    rw [Matrix.map_mul, Matrix.map_mul, hmid,
      map_aevalTower_liftGauge q p r g P B i.succ,
      map_aevalTower_liftGauge_inv q p r g P B i.castSucc]
  have := congrFun (congrFun hmat a) b
  rw [Matrix.map_apply] at this
  exact this

end DLNFibre.Core
