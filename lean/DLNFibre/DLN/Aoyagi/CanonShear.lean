import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.DLN.Aoyagi.PivotPreservation

/-!
# `DLN.Aoyagi.CanonShear` — the faithful `N_p` within-carve emission (SEAT-L4, M7; N_p re-bake)

The per-step faithful normalization `canonNormalizationOf` (`N_p`, defined in `MonumentAtlas`) a
case12/case2 edge emits, and the proof that it satisfies the RE-AUTHORED `ShearWithinCarveRaw` clauses
(I write-zero STRICTLY above `sl = S+1` / II reads ignore layers `> sl` / III vanishes on ledger
birth-corners). N_p has TWO supports (elder verbatim §1/§2): the layer-`s.layer` pivot-shifted Schur
cross-term `−w_{row,b}·w_{a,col}`, AND the layer-`(s.layer+1)` recoord image `A_{S+1}·Q₁⁻¹` (the piece
`canonShearOf` omitted). So it writes/reads layers `S` and `S+1` and vanishes strictly above `S+1`; the
recoord VALUE on layer `S+1` is pinned by `IsRealBranch`'s L1 value-pin, not re-pinned here.

`canonNormalizationOf … pivot` is the RAW displacement `shearφ` (the edge stores
`blockShear (canonNormalizationOf …)`; `ShearWithinCarveRaw`/`IsRealBranch` read the raw displacement).
At a case11/rollover edge the shear is `id` (displacement `0`), trivially within-carve — this file is
the case12/case2 emitter. `canonNormalizationOf_shearWithinCarve` is FRONTIER-sorried (the re-authored
clauses need re-derivation for the pivot-shifted+recoord shear; elder §2).
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- A flat coordinate in `layerCoords d ℓ` decodes (via `tupIdxEquiv`) to layer exactly `ℓ`. -/
theorem decode_layer_of_mem_layerCoords (d : Fin (N + 1) → ℕ) (ℓ : ℕ) (i : Fin (flatDim d))
    (hi : i ∈ layerCoords d ℓ) : (((tupIdxEquiv d).symm i).1.1 : ℕ) = ℓ := by
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨q, hq, hqi⟩ := hi
  rw [← hqi, Equiv.symm_apply_apply]
  exact hq

/-- **case-1(2)/case-2 oracle step child: layer preserved, cleared advanced by one.** For a step child
`c` of `conOracle M s` whose edge case is `case12` or `case2`, the child state is `stepAppendAdvance`,
so `c.child.layer = s.layer` and `c.child.cleared = s.cleared + 1`. Dispatch mirrors
`divBirthCoord_persists_conOracle` (per-branch `conOracle`-reduction, terminal/rollover/case-1(1)
branches excluded by the case hypothesis). Supplies the layer-descent `sl = layer + 1` M7 needs. -/
theorem conOracle_child_layer_cleared_of_case12_case2 {L : ℕ} {M : Fin (L + 1) → ℕ} (s : ConState L)
    (c : StepChild M s) (hc : c ∈ (conOracle M s).stepChildren)
    (hcase : c.ecase = StepCase.case12 ∨ c.ecase = StepCase.case2) :
    c.child.layer = s.layer ∧ c.child.cleared = s.cleared + 1 := by
  by_cases h1 : L ≤ s.layer
  · have horacle : conOracle M s = oracleTerminal M s := by unfold conOracle; rw [dif_pos h1]
    rw [horacle] at hc
    simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hc
  · have hlive : s.layer < L := not_le.mp h1
    by_cases h2 : widthMinUpto M (s.layer + 1) ≤ s.cleared
    · have horacle : conOracle M s = rolloverDecision M s (le_of_lt (not_le.mp h1)) h2 := by
        unfold conOracle; rw [dif_neg h1, dif_pos h2]
      rw [horacle] at hc
      simp only [rolloverDecision, ConDecision.stepChildren, List.mem_singleton] at hc
      subst hc
      rcases hcase with h | h <;> nomatch h
    · have hlt : s.cleared < widthMinUpto M (s.layer + 1) := not_le.mp h2
      have hcap : s.cleared < layerCap M := lt_of_lt_of_le hlt (widthMinUpto_le_layerCap M _)
      rcases hmin : ((List.finRange s.numDiv).filterMap (fun k =>
          if s.cleared + 1 ≤ s.divTilde k ∧ s.divTilde k + 1 ≤ widthMinUpto M s.layer
          then some (s.divTilde k) else none)).min? with _ | target
      · -- case-2
        have horacle : conOracle M s = case2Decision M s
            (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
          unfold conOracle; rw [dif_neg h1, dif_neg h2]
          split <;> simp_all only [reduceCtorEq]
        rw [horacle] at hc
        simp only [case2Decision, ConDecision.stepChildren, List.mem_singleton] at hc
        subst hc
        exact ⟨rfl, rfl⟩
      · rcases hf : chooseMin s target with _ | f
        · have horacle : conOracle M s = oracleTerminal M s := by
            unfold conOracle; rw [dif_neg h1, dif_neg h2]
            split <;> simp_all only [reduceCtorEq, Option.some.injEq]
            all_goals (try subst_vars)
            all_goals (try (split <;> simp_all only [reduceCtorEq]))
          rw [horacle] at hc
          simp only [oracleTerminal, ConDecision.stepChildren, List.not_mem_nil] at hc
        · -- case-1 (two children: stepCase11, then stepAppendAdvance)
          have hgt : s.cleared < target := by
            obtain ⟨hmemtar, -⟩ := List.min?_eq_some_iff'.mp hmin
            rw [List.mem_filterMap] at hmemtar
            obtain ⟨k0, -, hk0⟩ := hmemtar
            by_cases hc0 : s.cleared + 1 ≤ s.divTilde k0 ∧
                s.divTilde k0 + 1 ≤ widthMinUpto M s.layer
            · rw [if_pos hc0] at hk0
              have hdt : s.divTilde k0 = target := Option.some.inj hk0
              omega
            · rw [if_neg hc0] at hk0; exact absurd hk0 (by simp)
          have horacle : conOracle M s = case1Decision M s f (target - s.cleared)
              (widthMinUpto M s.layer - s.cleared) (M ⟨s.layer + 1, by omega⟩ - s.cleared)
              (not_le.mp h1) (by omega) (by rw [(chooseMin_spec s target hf).1]; omega) hcap := by
            unfold conOracle
            rw [dif_neg h1, dif_neg h2]
            split
            · rename_i target' heq
              obtain rfl : target' = target := Option.some.inj (heq ▸ hmin)
              split
              · rename_i f' hf'
                obtain rfl : f' = f := Option.some.inj (hf' ▸ hf)
                rfl
              · rename_i hf'
                exact absurd (hf' ▸ hf) (by simp)
            · rename_i heq
              exact absurd (heq ▸ hmin) (by simp)
          rw [horacle] at hc
          simp only [case1Decision, ConDecision.stepChildren, List.mem_cons,
            List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · rcases hcase with h | h <;> nomatch h
          · exact ⟨rfl, rfl⟩

/-- **M7 emission — `canonNormalizationOf` is within-carve ⟨FRONTIER; statement-locked, elder §2⟩.** At a
case12/case2 real-branch edge (node = the step, so `node.conState = ed.nextState`, `cleared ≥ 1`,
`sl = layer+1`), the faithful `N_p` shear `canonNormalizationOf d p.conState ed.pivot` satisfies the
RE-AUTHORED `ShearWithinCarveRaw` clauses: (I) writes 0 STRICTLY above `sl = S+1` (the Schur is on layer
`S`, the recoord on `S+1`, so nothing above `S+1`); (II) reads only layers `S`, `S+1`, so ignores layers
`> S+1`; (III) vanishes on the ledger birth-corners (the pivot-preservation clause). Re-stated + FRONTIER
sorried per precision §0-iv: the OLD `canonShearOf_shearWithinCarve` proved the OLD clause-(I)
("= 0 on ℓ ≥ sl"), which is FALSE for the faithful `N_p` (it WRITES layer `sl = S+1`) — so the old proof
proved the wrong object and is retired, not regressed. The re-derivation (recoord confinement + the
freshness-driven corner vanishing at the pivot-shifted Schur) is the substantial new proof. -/
@[blueprint]
theorem canonNormalizationOf_shearWithinCarve (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (p : TreePath d) (ed : TreeEdge d p)
    (hcase : ed.case = StepCase.case12 ∨ ed.case = StepCase.case2)
    (hpar : p.IsRealBranch e) (hdesc : DescendView d p ed)
    (hshear : ed.shearφ = canonNormalizationOf d p.conState ed.pivot) :
    ShearWithinCarveRaw d e (p.extend ed) ed.shearφ := by
  -- map: M7-emission ⟨FRONTIER — N_p satisfies re-authored ShearWithinCarveRaw (I/II vanish >sl; III corner)⟩
  sorry

/-- **Positive-branch value of `canonNormalizationOf`** (proof-aid twin of `canonNormalizationOf_support`;
pivot-parametric per elder §6). On the layer-`s.layer` Schur branch (decode-layer `= s.layer`, off the
pivot cross `row ≠ a`, `col ≠ b`, on the carve residual `row,col ≥ cleared`) the displacement is the
explicit pivot-shifted Schur cross-term `−w_{row,b}·w_{a,col}` (`b = ` pivot col, `a = ` pivot row, read
by NAT indices via `readEntry`). A clean `if_pos` projection off the def's first guard — PROVEN. -/
@[blueprint]
theorem canonNormalizationOf_apply_interior (d : Fin (N + 1) → ℕ) (s : ConState N) (p : Fin (flatDim d))
    (u : Fin (flatDim d) → ℝ) (k : Fin (flatDim d))
    (hlay : (((tupIdxEquiv d).symm k).1.1 : ℕ) = s.layer)
    (hrow_ne : (((tupIdxEquiv d).symm k).1.2 : ℕ) ≠ (((tupIdxEquiv d).symm p).1.2 : ℕ))
    (hcol_ne : (((tupIdxEquiv d).symm k).2 : ℕ) ≠ (((tupIdxEquiv d).symm p).2 : ℕ))
    (hrow_ge : s.cleared ≤ (((tupIdxEquiv d).symm k).1.2 : ℕ))
    (hcol_ge : s.cleared ≤ (((tupIdxEquiv d).symm k).2 : ℕ)) :
    canonNormalizationOf d s p u k =
      (-(readEntry d u s.layer (((tupIdxEquiv d).symm k).1.2 : ℕ) (((tupIdxEquiv d).symm p).2 : ℕ)))
        * readEntry d u s.layer (((tupIdxEquiv d).symm p).1.2 : ℕ) (((tupIdxEquiv d).symm k).2 : ℕ) := by
  -- map: B-canonNormalizationOf-apply-interior (Schur cross-term value; if_pos on the first guard)
  simp only [canonNormalizationOf]
  rw [if_pos ⟨hlay, hrow_ne, hcol_ne, hrow_ge, hcol_ge⟩]

end DLNFibre.DLN.Aoyagi
