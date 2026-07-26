import DLNFibre.DLN.Aoyagi.Corank2NativeShear334

/-!
# `DLN.Aoyagi.Corank2NativePerm334` — the 9 born-native node-1 permutation atoms (whole-conjugate)

The value-correct born-native chart per A0-dominant `p1` is the WHOLE loss-symmetry conjugate
`g_c = σ⁻¹ ∘ gWrap ∘ σ` (`whole_conjugate_all288.py`, pnp double-certified `rlct ≥ 4` on all 288).
It DECOMPOSES into DIRECT atoms:

* `σ⁻¹ ∘ shearH ∘ σ` = the native §2 shear (`nativeSel`, `Corank2NativeShear334`);
* `σ⁻¹ ∘ permP  ∘ σ` = a DIRECT coordinate permutation — **this file**;
* `σ⁻¹ ∘ bb(C,q) ∘ σ` = `blockBlowupMap (σ C) (σ q)` (permuted-centre blow-up — baked into the fan).

The node-1 shear of the whole-conjugate fan is `nativeChart1 p = nativeSel p ∘ nativePerm p`
(native shear AFTER native perm — the decomposition order). Each `nativePerm p` is the direct
coordinate map `w ↦ w ∘ cperm_p` for the emitted conj-permP index map `cperm_p : Fin 21 → Fin 21`
(all 9 are genuine `Fin 21` bijections, `by decide`; `p1 = 20` recovers the canonical `permP`). This
is grep-clean of any orbit-conjugation / transport machinery in the DEF: `σ` acts only in the
emitted index DATA, never wrapping the chart.

## Scope
- IN: the generic coordinate-permutation box-containment atom (`permCoord_covers`); the 9 conj-permP
  index maps + their `Equiv.Perm`; `nativePerm` dispatch with box-containment / differentiability /
  `|jacDet| = 1`; the composite node-1 shear `nativeChart1` with box-containment / differentiability.
- OUT: the fan assembly + `hcover` (`Corank2NativeFan334`); the value entry-equalities `hentry` (the
  (B) seat); the per-leaf `jac`/`divisorMin` (the (C) seat).
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2ChartJac
open DLNFibre.DLN.Aoyagi.NativeShear334

namespace DLNFibre.DLN.Aoyagi.NativePerm334

/-! ## §0 — the generic coordinate-permutation box-containment atom -/

/-- **A coordinate permutation box-contains at EVERY radius.** For `σ : Equiv.Perm (Fin D)`, the
reindex map `w ↦ w ∘ σ` maps `closedBall 0 s` ONTO itself, so `closedBall 0 s ⊆ (w ↦ w∘σ) ''
closedBall 0 s` (preimage `x ↦ x ∘ σ⁻¹`, a sup-norm isometry). Reusable engine material. -/
theorem permCoord_covers {D : ℕ} (σ : Equiv.Perm (Fin D)) {s : ℝ} :
    closedBall (0 : Fin D → ℝ) s ⊆ (fun (w : Fin D → ℝ) i ↦ w (σ i)) '' closedBall 0 s := by
  intro x hx
  have hxs : ‖x‖ ≤ s := mem_closedBall_zero_iff.mp hx
  refine ⟨fun k ↦ x (σ.symm k), ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg x) hxs)]
    intro k
    exact (norm_le_pi_norm x (σ.symm k)).trans hxs
  · funext i; simp only [Equiv.symm_apply_apply]

/-- **A coordinate permutation is differentiable** (a bounded linear reindex). -/
theorem differentiable_permCoord {D : ℕ} (σ : Equiv.Perm (Fin D)) :
    Differentiable ℝ (fun (w : Fin D → ℝ) i ↦ w (σ i)) :=
  differentiable_pi.2 (fun i ↦ differentiable_apply (σ i))

/-! ## §1 — the 9 conj-permP index maps (`cperm·`), their injectivity + `Equiv.Perm`.
Machine-generated from `whole_conjugate_all288.py` [1] (`conj(permP, make_sigma(i,j))`; `p1 = 20` is
the canonical `permP`). Injectivity is `by decide`; finite ⟹ bijective ⟹ `Equiv.Perm`. -/

-- BEGIN generated (conj-permP index maps; whole_conjugate_all288.py §[1])
def cperm0 (k : Fin 21) : Fin 21 := if k = 1 then 13 else if k = 2 then 1 else if k = 4 then 14 else if k = 6 then 15 else if k = 12 then 20 else if k = 13 then 4 else if k = 14 then 6 else if k = 15 then 2 else if k = 20 then 12 else k
def cperm1 (k : Fin 21) : Fin 21 := if k = 0 then 16 else if k = 4 then 20 else if k = 5 then 18 else if k = 7 then 19 else if k = 16 then 0 else if k = 17 then 5 else if k = 18 then 7 else if k = 19 then 4 else if k = 20 then 17 else k
def cperm2 (k : Fin 21) : Fin 21 := if k = 0 then 5 else if k = 3 then 11 else if k = 4 then 8 else if k = 5 then 9 else if k = 8 then 4 else if k = 9 then 20 else if k = 10 then 3 else if k = 11 then 0 else if k = 20 then 10 else k
def cperm3 (k : Fin 21) : Fin 21 := if k = 2 then 10 else if k = 4 then 7 else if k = 6 then 8 else if k = 7 then 9 else if k = 8 then 6 else if k = 9 then 2 else if k = 10 then 20 else if k = 11 then 4 else if k = 20 then 11 else k
def cperm4 (k : Fin 21) : Fin 21 := if k = 0 then 14 else if k = 2 then 12 else if k = 5 then 13 else if k = 6 then 15 else if k = 12 then 2 else if k = 13 then 0 else if k = 14 then 6 else if k = 15 then 20 else if k = 20 then 5 else k
def cperm5 (k : Fin 21) : Fin 21 := if k = 0 then 2 else if k = 1 then 18 else if k = 2 then 17 else if k = 4 then 16 else if k = 7 then 19 else if k = 16 then 4 else if k = 17 then 1 else if k = 18 then 7 else if k = 19 then 0 else k
def cperm6 (k : Fin 21) : Fin 21 := if k = 0 then 15 else if k = 2 then 7 else if k = 3 then 12 else if k = 4 then 14 else if k = 7 then 13 else if k = 12 then 3 else if k = 13 then 4 else if k = 14 then 0 else if k = 15 then 2 else k
def cperm7 (k : Fin 21) : Fin 21 := if k = 1 then 19 else if k = 3 then 17 else if k = 4 then 3 else if k = 5 then 18 else if k = 6 then 16 else if k = 16 then 6 else if k = 17 then 5 else if k = 18 then 1 else if k = 19 then 4 else k
def cperm20 (k : Fin 21) : Fin 21 := if k = 0 then 8 else if k = 1 then 9 else if k = 2 then 10 else if k = 3 then 11 else if k = 4 then 1 else if k = 8 then 0 else if k = 9 then 2 else if k = 10 then 3 else if k = 11 then 4 else k
-- END generated

theorem cperm0_inj : Function.Injective cperm0 := by decide
theorem cperm1_inj : Function.Injective cperm1 := by decide
theorem cperm2_inj : Function.Injective cperm2 := by decide
theorem cperm3_inj : Function.Injective cperm3 := by decide
theorem cperm4_inj : Function.Injective cperm4 := by decide
theorem cperm5_inj : Function.Injective cperm5 := by decide
theorem cperm6_inj : Function.Injective cperm6 := by decide
theorem cperm7_inj : Function.Injective cperm7 := by decide
theorem cperm20_inj : Function.Injective cperm20 := by decide

noncomputable def cpermS0 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm0 ((Finite.injective_iff_bijective).mp cperm0_inj)
noncomputable def cpermS1 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm1 ((Finite.injective_iff_bijective).mp cperm1_inj)
noncomputable def cpermS2 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm2 ((Finite.injective_iff_bijective).mp cperm2_inj)
noncomputable def cpermS3 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm3 ((Finite.injective_iff_bijective).mp cperm3_inj)
noncomputable def cpermS4 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm4 ((Finite.injective_iff_bijective).mp cperm4_inj)
noncomputable def cpermS5 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm5 ((Finite.injective_iff_bijective).mp cperm5_inj)
noncomputable def cpermS6 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm6 ((Finite.injective_iff_bijective).mp cperm6_inj)
noncomputable def cpermS7 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm7 ((Finite.injective_iff_bijective).mp cperm7_inj)
noncomputable def cpermS20 : Equiv.Perm (Fin 21) := Equiv.ofBijective cperm20 ((Finite.injective_iff_bijective).mp cperm20_inj)

/-! ## §2 — the per-pivot node-1 native permutation `nativePerm` (id off the 9 A0-dominant pivots) -/

/-- **The per-pivot node-1 native permutation** `nativePerm p = σ⁻¹∘permP∘σ` as the DIRECT coordinate
map `w ↦ w ∘ cperm_p` for each A0-dominant pivot slot `p ∈ {0,…,7,20}`, `id` elsewhere. Presented
through the `Equiv.Perm` `cpermS·` (`cpermS· i = cperm· i` by `Equiv.ofBijective_apply`, so the
concrete `cperm·` if-chain is available to the (B) entry-equality seat). -/
noncomputable def nativePerm : Fin 21 → (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun p =>
  if p = 0 then (fun w i ↦ w (cpermS0 i))
  else if p = 1 then (fun w i ↦ w (cpermS1 i))
  else if p = 2 then (fun w i ↦ w (cpermS2 i))
  else if p = 3 then (fun w i ↦ w (cpermS3 i))
  else if p = 4 then (fun w i ↦ w (cpermS4 i))
  else if p = 5 then (fun w i ↦ w (cpermS5 i))
  else if p = 6 then (fun w i ↦ w (cpermS6 i))
  else if p = 7 then (fun w i ↦ w (cpermS7 i))
  else if p = 20 then (fun w i ↦ w (cpermS20 i))
  else id

/-- The concrete conj-permP index maps recovered from the `Equiv.Perm` (`Equiv.ofBijective_apply`) —
the (B) entry-equality seat unfolds `nativePerm` through these. -/
theorem cpermS_apply :
    (∀ i, cpermS0 i = cperm0 i) ∧ (∀ i, cpermS1 i = cperm1 i) ∧ (∀ i, cpermS2 i = cperm2 i) ∧
    (∀ i, cpermS3 i = cperm3 i) ∧ (∀ i, cpermS4 i = cperm4 i) ∧ (∀ i, cpermS5 i = cperm5 i) ∧
    (∀ i, cpermS6 i = cperm6 i) ∧ (∀ i, cpermS7 i = cperm7 i) ∧ (∀ i, cpermS20 i = cperm20 i) :=
  ⟨fun i ↦ rfl, fun i ↦ rfl, fun i ↦ rfl, fun i ↦ rfl, fun i ↦ rfl, fun i ↦ rfl, fun i ↦ rfl,
    fun i ↦ rfl, fun i ↦ rfl⟩

/-- **Each node-1 native permutation box-contains at every radius** (a coordinate permutation is a
sup-norm isometry), at every dominant pivot. Dispatch to `permCoord_covers` per `cpermS·`. -/
theorem nativePerm_covers (p : Fin 21)
    (hp : p ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))) {s : ℝ} :
    closedBall (0 : Fin 21 → ℝ) s ⊆ nativePerm p '' closedBall 0 s := by
  fin_cases hp <;> simp only [nativePerm, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact permCoord_covers cpermS0 | exact permCoord_covers cpermS1
      | exact permCoord_covers cpermS2 | exact permCoord_covers cpermS3
      | exact permCoord_covers cpermS4 | exact permCoord_covers cpermS5
      | exact permCoord_covers cpermS6 | exact permCoord_covers cpermS7
      | exact permCoord_covers cpermS20

/-- **Each node-1 native permutation is differentiable** (a linear reindex; `id` off the pivots). -/
theorem nativePerm_differentiable (p : Fin 21) : Differentiable ℝ (nativePerm p) := by
  simp only [nativePerm]
  split_ifs <;>
    first
      | exact differentiable_id
      | exact differentiable_permCoord cpermS0 | exact differentiable_permCoord cpermS1
      | exact differentiable_permCoord cpermS2 | exact differentiable_permCoord cpermS3
      | exact differentiable_permCoord cpermS4 | exact differentiable_permCoord cpermS5
      | exact differentiable_permCoord cpermS6 | exact differentiable_permCoord cpermS7
      | exact differentiable_permCoord cpermS20

/-- **Each node-1 native permutation has `|jacDet| = 1`** (`abs_jacDet_permCoord`), at every
dominant pivot. -/
theorem nativePerm_jacDet (p : Fin 21)
    (hp : p ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))) (u : Fin 21 → ℝ) :
    |jacDet (nativePerm p) u| = 1 := by
  fin_cases hp <;> simp only [nativePerm, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact abs_jacDet_permCoord cpermS0 u | exact abs_jacDet_permCoord cpermS1 u
      | exact abs_jacDet_permCoord cpermS2 u | exact abs_jacDet_permCoord cpermS3 u
      | exact abs_jacDet_permCoord cpermS4 u | exact abs_jacDet_permCoord cpermS5 u
      | exact abs_jacDet_permCoord cpermS6 u | exact abs_jacDet_permCoord cpermS7 u
      | exact abs_jacDet_permCoord cpermS20 u

/-! ## §3 — the composite node-1 shear `nativeChart1 = nativeSel ∘ nativePerm` -/

/-- **The whole-conjugate node-1 shear** `nativeChart1 p = nativeSel p ∘ nativePerm p` — the native
§2 shear AFTER the native permutation (the decomposition order `σ⁻¹∘shearH∘σ ∘ σ⁻¹∘permP∘σ`). Both
factors are DIRECT atoms; no chart-level conjugation. -/
noncomputable def nativeChart1 (p : Fin 21) : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  nativeSel p ∘ nativePerm p

/-- **The composite node-1 shear box-contains** with the `C = 2` inflation `r ↦ r + 2r²`: the perm
maps the `f`-box onto itself, then the native shear box-contains (`nativeSel_covers`). -/
theorem nativeChart1_covers (p : Fin 21)
    (hp : p ∈ ({0, 1, 2, 3, 4, 5, 6, 7, 20} : Finset (Fin 21))) {t : ℝ} :
    closedBall (0 : Fin 21 → ℝ) t ⊆ nativeChart1 p '' closedBall 0 (t + 2 * t ^ 2) := by
  calc closedBall (0 : Fin 21 → ℝ) t
      ⊆ nativeSel p '' closedBall 0 (t + 2 * t ^ 2) := nativeSel_covers p hp
    _ ⊆ nativeSel p '' (nativePerm p '' closedBall 0 (t + 2 * t ^ 2)) :=
        Set.image_mono (nativePerm_covers p hp)
    _ = nativeChart1 p '' closedBall 0 (t + 2 * t ^ 2) := (Set.image_comp _ _ _).symm

/-- **The composite node-1 shear is differentiable.** -/
theorem nativeChart1_differentiable (p : Fin 21) : Differentiable ℝ (nativeChart1 p) :=
  (nativeSel_differentiable p).comp (nativePerm_differentiable p)

end DLNFibre.DLN.Aoyagi.NativePerm334
