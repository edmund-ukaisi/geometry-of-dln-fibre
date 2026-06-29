import DLNFibre.DLN.RLCT.Validate.RouteMBData
import DLNFibre.DLN.RLCT.Validate.RouteMLayerGrade
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `RouteMSlotId` — the slot-identification `hslot`: a FIDELITY OBSTRUCTION (banked machine-checked)

This module was tasked to discharge the open hypothesis `hslot` of the BANKED reduction
`phiFlatLiveR1_eq_B_comp_pivotBlowupOn` (`RouteMBData`), closing the `φ = B ∘ pivotBlowupOn` half of
the route-(i) map identity at `L = 2`. The target (∀ `x`):

  `smulRmatRfin (x p₀) M t (genBlkFlatLiveR1 … (rfin x) x)
      = genBlkFlatLiveR1 … (rfin (pivotBlowupOn active p₀ x)) (pivotBlowupOn active p₀ x)`.

**The target `hslot` is FALSE against `genBlkFlatLiveR1`** — for ANY `M`, `t`, `p`, `rfin`, `active`
with a NONEMPTY pivot residual block (the genuinely-intended case, from `InteriorDrop`'s strict
drops), unless `x p₀ = 1`. The decisive reason (record extensionality at the pivot `Rmat p`):

* `smulRmatRfin u` scales **every** `Rmat k` by `u`, **including** the pivot boundary `p`, where the
  R1 decoder pins `Rmat p = rmatPad (pivotEIndicator p)` — a FIXED constant (literal `1` at the
  residual `(0,0)`), NOT read from `x`. So the LHS pivot block is `u • rmatPad (pivotEIndicator p)`.
* The RHS reads `genBlkFlatLiveR1 … (pbo x)`, whose `Rmat p` is STILL the same fixed
  `rmatPad (pivotEIndicator p)` (the `Function.update` value is independent of `x`).
* At the residual `(0,0)` entry the two blocks read `u • 1 = u` (LHS) vs `1` (RHS) — equal only if
  `u = 1`. The pin (`pnp-radial-adjudication/codex/L2-explicit-finset-answer.md`) places the fixed
  `1` in the LEAF anchor (`Rfin`), so `u • Rfin` puts the radial on the anchor while the pivot
  E-block is a FREE coordinate `pivotBlowupOn` scales: the banked decoder fixed the WRONG block.

This is a genuine fidelity gap: the banking commit's "numerically CONFIRMED exact at L=2 (sympy)"
validated the LIVE-pivot model ("the R free coords ARE the active set scaled by `x_p`"), but
`genBlkFlatLiveR1` fixes the pivot R and frees the leaf — the reverse. Independently confirmed by
Codex (verdict FALSE) and sympy (fixed model fails at `u = 2`; live model holds).

We BANK the obstruction machine-checked:

* `genBlkFlatLiveR1_Rmat_pivot_entry` — the RHS pivot `Rmat p` residual `(0,0)` entry is `1`.
* `genBlkFlatLiveR1_Rmat_pivot_smul_entry` — the LHS pivot `Rmat p` residual `(0,0)` is `u • 1 = u`.
* `hslot_genBlkFlatLiveR1_forces_pivot_one` — the `GenBlk` equality, at one point, forces `u = 1`.
* `not_hslot_genBlkFlatLiveR1` — the universally-quantified `hslot` (∀ `x`) is FALSE when the pivot
  residual block is nonempty: a point with `x p₀ = 2` separates the two sides.

The FAITHFUL fix (the live-pivot decoder, where the pivot `Rmat` reads `x`) is the controller-level
restatement of the route's consumer; flagged in the report, not built here (it changes which decoder
`phiFlatLiveR1_eq_B_comp_pivotBlowupOn` consumes).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-! ## The pivot residual `(0,0)` index (nonempty pivot block) -/

/-- The residual `(0,0)` ROW index of `Rmat p` (`Text p × Wext p`), as the `natAdd`-image of the
residual block's `⟨0,_⟩`: lives in the bottom-right `E`-block where `rmatPad` plants
`pivotEIndicator`. -/
def pivotResRow (M t : Fin (L + 1) → ℕ) (p : ℕ)
    (hr : 0 < Text M t p - Text M t (p + 1)) : Fin (Text M t p) :=
  Fin.cast (show Text M t (p + 1) + (Text M t p - Text M t (p + 1)) = Text M t p by omega)
    (Fin.natAdd (Text M t (p + 1)) ⟨0, hr⟩)

/-- The residual `(0,0)` COLUMN index of `Rmat p` (`Text p × Wext p`). -/
def pivotResCol (M t : Fin (L + 1) → ℕ) (p : ℕ)
    (hc : 0 < Wext M p - Text M t (p + 1)) (hp2 : Text M t (p + 1) ≤ Wext M p) : Fin (Wext M p) :=
  Fin.cast (show Text M t (p + 1) + (Wext M p - Text M t (p + 1)) = Wext M p by omega)
    (Fin.natAdd (Text M t (p + 1)) ⟨0, hc⟩)

/-- **The fixed pivot block reads `1` at its residual `(0,0)`.** `(genBlkFlatLiveR1 …).Rmat p =
rmatPad (pivotEIndicator p)` (banked `genBlkFlatLiveR1_Rmat_pivot`); the `natAdd`/`natAdd` residual
entry is `pivotEIndicator p ⟨0,_⟩ ⟨0,_⟩ = 1` (`rmatPad_natAdd_natAdd` then
`pivotEIndicator_apply_zero`). -/
theorem genBlkFlatLiveR1_Rmat_pivot_entry (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (hr : 0 < Text M t p - Text M t (p + 1)) (hc : 0 < Wext M p - Text M t (p + 1))
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) :
    (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Rmat p
        (pivotResRow M t p hr) (pivotResCol M t p hc hp2) = 1 := by
  rw [genBlkFlatLiveR1_Rmat_pivot M t ha p hp1 hp2 rfin x]
  rw [pivotResRow, pivotResCol, rmatPad_natAdd_natAdd hp1 hp2]
  exact pivotEIndicator_apply_zero M t p hr hc

/-- **The scaled pivot block reads `u` at its residual `(0,0)`.** `smulRmatRfin u` scales `Rmat p`
by `u`, so the residual entry is `u • 1 = u`. -/
theorem genBlkFlatLiveR1_Rmat_pivot_smul_entry (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (hr : 0 < Text M t p - Text M t (p + 1)) (hc : 0 < Wext M p - Text M t (p + 1))
    (rfin : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ) (x : Fin (routeMAmbient M) → ℝ) (u : ℝ) :
    (smulRmatRfin u M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x)).Rmat p
        (pivotResRow M t p hr) (pivotResCol M t p hc hp2) = u := by
  change (u • (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x).Rmat p)
      (pivotResRow M t p hr) (pivotResCol M t p hc hp2) = u
  rw [Matrix.smul_apply, genBlkFlatLiveR1_Rmat_pivot_entry M t ha p hp1 hp2 hr hc rfin x,
    smul_eq_mul, mul_one]

/-! ## The obstruction: the banked `hslot` forces `x p₀ = 1` (so the ∀-form is false) -/

/-- **The banked `hslot` equation, at one point, forces `u = 1`.** If the `GenBlk` equality
`smulRmatRfin u (genBlkFlatLiveR1 … rfin x) = genBlkFlatLiveR1 … rfin' x'` holds (any RHS arguments
`rfin'`, `x'`), then reading the pivot `Rmat p` residual `(0,0)` entry on both sides gives `u = 1`.
(The RHS pivot entry is `1` regardless of `rfin'`/`x'` — the fixed `Function.update` value.) The
genuinely-intended pivot has a NONEMPTY residual block (`hr`, `hc` from `InteriorDrop`'s strict
drops), so the entry is genuinely `1`, not a vacuous `0 = 0`. -/
theorem hslot_genBlkFlatLiveR1_forces_pivot_one (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (hr : 0 < Text M t p - Text M t (p + 1)) (hc : 0 < Wext M p - Text M t (p + 1))
    (rfin rfin' : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x x' : Fin (routeMAmbient M) → ℝ) (u : ℝ)
    (heq : smulRmatRfin u M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfin x)
        = genBlkFlatLiveR1 M t ha p hp1 hp2 rfin' x') :
    u = 1 := by
  have hentry := congrArg
    (fun B : GenBlk M t => B.Rmat p (pivotResRow M t p hr) (pivotResCol M t p hc hp2)) heq
  simp only at hentry
  rw [genBlkFlatLiveR1_Rmat_pivot_smul_entry M t ha p hp1 hp2 hr hc rfin x u,
    genBlkFlatLiveR1_Rmat_pivot_entry M t ha p hp1 hp2 hr hc rfin' x'] at hentry
  exact hentry

/-- **The banked `hslot` (∀ `x`) is FALSE for `genBlkFlatLiveR1`** when the pivot residual block is
nonempty (`hr`, `hc`). Any candidate `active : Finset` and leaf reader `rfin` is refuted: the point
`x = fun _ => 2` has `x (structPivot M hN) = 2`, and `hslot` at that point forces `2 = 1`. This is
the exact shape of the open hypothesis of `phiFlatLiveR1_eq_B_comp_pivotBlowupOn`; it cannot be
discharged against this decoder. -/
theorem not_hslot_genBlkFlatLiveR1 (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (hr : 0 < Text M t p - Text M t (p + 1)) (hc : 0 < Wext M p - Text M t (p + 1))
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (active : Finset (Fin (routeMAmbient M))) :
    ¬ (∀ x : Fin (routeMAmbient M) → ℝ,
        smulRmatRfin (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
          = genBlkFlatLiveR1 M t ha p hp1 hp2
              (rfin (pivotBlowupOn active (structPivot M hN) x))
              (pivotBlowupOn active (structPivot M hN) x)) := by
  intro hslot
  have hforce := hslot_genBlkFlatLiveR1_forces_pivot_one M t ha p hp1 hp2 hr hc
    (rfin (fun _ => 2))
    (rfin (pivotBlowupOn active (structPivot M hN) (fun _ => 2)))
    (fun _ => 2) (pivotBlowupOn active (structPivot M hN) (fun _ => 2))
    ((fun _ => 2 : Fin (routeMAmbient M) → ℝ) (structPivot M hN))
    (hslot (fun _ => 2))
  -- `(fun _ => 2) (structPivot M hN) = 2`, so `hforce : (2 : ℝ) = 1`.
  norm_num at hforce

end DLNFibre.DLN.RLCT
