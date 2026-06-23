import DLNFibre.DLN.RLCT.Validate.DeepestSplitReindex
import DLNFibre.DLN.RLCT.Validate.DeepestGaugeConstruction

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestRegPivotEquiv` — the explicit boundary-pivot packing (#120 / #82)

The standalone EARLY-CHECK (controller, 2026-06-23): build the explicit `regPivotFinEquiv` +
`BoundaryPivotIdx` + the boundary routing `regBoundaryToRegGauge` (injective by construction), and
prove the cheap alignment/injectivity facts that GATE the expensive #91 sandwich. If these close, the
Fin-indexing enumeration is right → invest in the sandwich; if not, the wrong enumeration is caught in
~60 lines, not 200.

These are NEW declarations (non-colliding). At cobuild's #80 handoff of `DeepestGaugeConstruction.lean`,
`regResidualPack` is REDEFINED `:= regPivotFinEquiv` and `regGaugeIdxSplit`'s reg-half (in
`DeepestSplitReindex.lean`) routes via `regBoundaryToRegGauge ∘ regPivotFinEquiv`, so the two cancel and
`deepestEPivot_regSlice_fderiv_id` becomes `= id` by construction (see `deriv-120-wiring-spec.md`).

## ⚠ DESIGN-INPUT DRAFT — UNVERIFIED (never compiled: the worktree build was CPU-starved)

This file is the DESIGN INPUT for cobuild's in-place #82-deriv close (controller reallocation
2026-06-23: cobuild owns the def-change files + #80 + a live build env, so it does the refactor
in-place — no copy/merge). The **definitions, types, and the boundary routing** are the load-bearing
content (lift them directly). The **proofs are UNVERIFIED** — this never reached a green build:
- `card_boundaryPivotIdx` / `regPivotFinEquiv` arithmetic: near-certain (copied verbatim from the
  PROVEN `regResidualPack` card proof, `DeepestGaugeConstruction.lean:362-371`).
- `regBoundaryToRegGauge` (the `Y_last` `Fin.last` cast) and `regBoundaryToRegGauge_injective`
  (the `Sigma.mk`/`Sum` injectivity chase): SPECULATIVE — likely need iteration in a live env
  (the cast normal form, the `simp_all`/`aesop` closers). cobuild should treat these as skeletons.

## The boundary correspondence (g213/#91, the collapse-math — CERTIFIED)

At `reg = 0` every framed layer is the idempotent corner `blockdiag[I_r,0]`; Leibniz with idempotent
prefix/suffix products keeps `dP|_0 = (Σ_s δX_s, δY_L, δZ_1)` — the (0,0)-corner sums ALL layers' X, the
last layer's Y, the first layer's Z survive. So the reg slot must carry exactly the boundary generators
`(X_first, Y_last, Z_first)`, one private coordinate each, routed to DISTINCT `RegGaugeIdx` entries so
the `Σ_s δX_s` does not collapse two reg coords (injective-by-construction — the controller's sharpening).
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The boundary-pivot index type** — the three residual blocks `(P11−I, P12, P21)` that survive the
idempotent sandwich: `(r×r) ⊕ ((r×M_L) ⊕ (M_0×r))`, the same sum type `regResidualPack` already targets,
of cardinality `deepestNReg H r`. -/
abbrev BoundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ) : Type :=
  (Fin r × Fin r) ⊕ ((Fin r × Fin (H (Fin.last L) - r)) ⊕ (Fin (H 0 - r) × Fin r))

/-- **The card match** — `card (BoundaryPivotIdx H r) = deepestNReg H r` (the SAME arithmetic
`regResidualPack` already proves: `r² + r(H_L−r) + (H_0−r)r = r(H_0+H_L−r)`). The explicit Fin-equiv
exists by this; the refactor swaps the opaque `Fintype.equivFin` tail for an honest enumeration. -/
theorem card_boundaryPivotIdx (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fintype.card (BoundaryPivotIdx H r) = deepestNReg H r := by
  simp only [BoundaryPivotIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
  obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
  unfold deepestNReg
  rw [← ha', ← hb']
  simp only [Nat.add_sub_cancel_left]
  rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
  ring

/-- **The explicit pivot packing** `Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r` — the TRANSPARENT
enumeration replacing `regResidualPack`'s opaque `Fintype.equivFin`: `finProdFinEquiv` on each block
(`r×r`, `r×M_L`, `M_0×r`) + `finSumFinEquiv` to assemble, with the `deepestNReg = r² + (r·M_L + M_0·r)`
reassociation by `finCongr`. Computable (has `_apply` equation lemmas), so the per-coordinate value
reduces — the property `Fintype.equivFin` lacks. This is what makes the cancellation `rfl`-able. -/
noncomputable def regPivotFinEquiv (H : Fin (L + 1) → ℕ) (r : ℕ)
    (hr : ∀ s : Fin (L + 1), r ≤ H s) :
    Fin (deepestNReg H r) ≃ BoundaryPivotIdx H r :=
  -- `Fin nReg ≃ Fin (r*r + (r*M_L + M_0*r))` then split into the three `finProdFinEquiv` blocks.
  (finCongr (show deepestNReg H r
      = r * r + (r * (H (Fin.last L) - r) + (H 0 - r) * r) by
        obtain ⟨a', ha'⟩ := Nat.le.dest (hr 0)
        obtain ⟨b', hb'⟩ := Nat.le.dest (hr (Fin.last L))
        unfold deepestNReg
        rw [← ha', ← hb']
        simp only [Nat.add_sub_cancel_left]
        rw [show r + a' + (r + b') - r = r + (a' + b') by omega]
        ring)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr finProdFinEquiv.symm
        (finSumFinEquiv.symm.trans
          (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm))))

/-- **The boundary-generator routing** `BoundaryPivotIdx H r ↪ RegGaugeIdx H r` (the reg-half target):
`X_first` ↦ layer-0 (0,0) entry, `Y_last` ↦ last-layer (0,1) entry, `Z_first` ↦ layer-0 (1,0) entry.
INJECTIVE by construction (distinct layer-tag × sum-arm), killing the `Σ_s δX_s` collapse. The
`H (Fin.last L) - r` vs `H (⟨L-1,_⟩.succ) - r` index forced equal by `Fin.last L = ⟨L-1,_⟩.succ`. -/
def regBoundaryToRegGauge (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    BoundaryPivotIdx H r → RegGaugeIdx H r := by
  obtain ⟨Lm, rfl⟩ : ∃ Lm, L = Lm + 1 := ⟨L - 1, by omega⟩
  -- first layer `0 : Fin (Lm+1)`, last layer `Fin.last Lm : Fin (Lm+1)` (= ⟨Lm, _⟩).
  refine fun b => ?_
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ | ⟨i, j⟩
  · -- X_first: layer 0, outer-inl inner-inl
    exact ⟨0, Sum.inl (Sum.inl (i, j))⟩
  · -- Y_last: layer (Fin.last Lm), outer-inl inner-inr; cast j : Fin (H (Fin.last (Lm+1)) - r)
    --         to Fin (H (Fin.last Lm).succ - r) since (Fin.last Lm).succ = Fin.last (Lm+1).
    refine ⟨Fin.last Lm, Sum.inl (Sum.inr (i, ?_))⟩
    have he : H (Fin.last (Lm + 1)) = H ((Fin.last Lm).succ) := by
      congr 1; exact (Fin.succ_last Lm).symm
    exact (finCongr (by rw [he])) j
  · -- Z_first: layer 0, outer-inr
    exact ⟨0, Sum.inr (i, j)⟩

/-- **`regBoundaryToRegGauge` is INJECTIVE** (the controller's sharpening — the load-bearing early-check).
Distinct `BoundaryPivotIdx` coords land in distinct `RegGaugeIdx` entries: X_first/Z_first share layer 0
but differ in the OUTER sum-arm (`Sum.inl` vs `Sum.inr`); Y_last has layer-tag `Fin.last Lm ≠ 0`
(needs `1 ≤ L`, so `Lm ≥ 0` and `Fin.last Lm = ⟨Lm,_⟩`; `0 = Fin.last Lm` would force `Lm = 0`, handled).
This is what makes the reg-half read INJECTIVE, so the `Σ_s δX_s` sandwich does NOT collapse two reg
coords (X_first is the only X in the reg image). -/
theorem regBoundaryToRegGauge_injective (H : Fin (L + 1) → ℕ) (r : ℕ) (hL : 1 ≤ L) :
    Function.Injective (regBoundaryToRegGauge H r hL) := by
  obtain ⟨Lm, rfl⟩ : ∃ Lm, L = Lm + 1 := ⟨L - 1, by omega⟩
  intro a b hab
  -- Unfold both via the `rcases` shape; the Sigma + Sum structure forces the arms equal.
  rcases a with ⟨ia, ja⟩ | ⟨ia, ja⟩ | ⟨ia, ja⟩ <;>
    rcases b with ⟨ib, jb⟩ | ⟨ib, jb⟩ | ⟨ib, jb⟩ <;>
    simp only [regBoundaryToRegGauge] at hab
  all_goals first
    | (-- same-arm cases: the Sigma.mk injectivity gives the index equality
       (obtain ⟨_, h2⟩ := Sigma.mk.inj_iff.1 hab
        simp_all [Sum.inl.injEq, Sum.inr.injEq, Prod.ext_iff, finCongr]) <;> aesop)
    | (-- cross-arm cases: distinct layer-tag OR distinct outer sum-arm → contradiction
       exfalso
       have := Sigma.mk.inj_iff.1 hab
       simp_all [Fin.ext_iff])

end DLNFibre.DLN.RLCT
