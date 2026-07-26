import DLNFibre.DLN.Aoyagi.Corank2CleanEntry334

/-!
# `DLN.Aoyagi.Corank2CleanHentry334` — the CLEAN-144 `hentry` (the (B) seat deliverable)

Assembles the 9 per-pivot entry-equalities (`Corank2CleanEntry334`) into the `hentry` field of
`rlctAt_coreGen334_ge_four_of_survivor_entries`, on the CLEAN-144:

`clean_hentry : ∀ c, IsClean c → ∀ w, coreGen dvec eWrap (k0 c) (gFin c w) = ∏_d (w d)^(ek₀ c d)`.

`IsClean c` = the leaf's pivot-cross `(pivot1 c, pivot2 c)` is a clean single-entry survivor pair
(the CLEAN-144, `cleanPairs`, pnp 288-leaf census). The value monomial is the pivot-cross
`ek₀ c = 1@(pivot1 c) + 1@(pivot2 c)`; the survivor `coreGen` entry index is `k0 c`.

## Scope (honest)
- IN: the exact per-chart entry-equality on the CLEAN-144, `k0`/`ek₀`/`IsClean` explicit + verified
  (the born-native shear cancels the block-elim cross-term ⟹ the survivor `coreGen` entry = the
  pivot-cross monomial EXACTLY; the pnp 288-leaf direct-atom cert).
- OUT: the over-vanishing-144 (0 single-entry survivors, higher monomial — a SEPARATE feeder); the
  cover/`jac`/`divisorMin` wiring of the reduction; the restriction of the chart family to the
  CLEAN-144 (the controller's integration).
-/

open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.CleanHentry334

/-- **The generic clean-leaf entry-equality** — dispatch on the node-1 pivot `p1 ∈ S1` to the 9
per-pivot lemmas. For a clean pivot-cross `(p1, p2)`, the born-native leaf composite exposes the
`(ijpair p1 p2)`-indexed `coreGen` entry as the survivor monomial `w p1 · w p2` exactly. -/
theorem clean_entry (p1 p2 p3 : Fin 21) (hp1 : p1 ∈ S1) (hp2 : p2 ∈ sigmaC1Fs p1)
    (hp3 : p3 ∈ sigmaC2Fs p1) (hcl : (p1, p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair p1 p2)) (leafMap p1 p2 p3 w) = w p1 * w p2 := by
  fin_cases hp1 <;>
    first
    | exact clean_entry_p0 _ _ hp2 hp3 hcl w
    | exact clean_entry_p1 _ _ hp2 hp3 hcl w
    | exact clean_entry_p2 _ _ hp2 hp3 hcl w
    | exact clean_entry_p3 _ _ hp2 hp3 hcl w
    | exact clean_entry_p4 _ _ hp2 hp3 hcl w
    | exact clean_entry_p5 _ _ hp2 hp3 hcl w
    | exact clean_entry_p6 _ _ hp2 hp3 hcl w
    | exact clean_entry_p7 _ _ hp2 hp3 hcl w
    | exact clean_entry_p20 _ _ hp2 hp3 hcl w

/-- **The CLEAN-144 `hentry`** — for a clean leaf `c`, the `k0 c`-indexed `coreGen` entry of the
whole-conjugate leaf composite `gFin c` equals the pivot-cross monomial `∏_d (w d)^(ek₀ c d)`
exactly (globally in `w`). Discharges the `hentry` field of
`rlctAt_coreGen334_ge_four_of_survivor_entries` on the CLEAN-144. -/
theorem clean_hentry (c : Fin numCharts) (hc : IsClean c) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (k0 c) (gFin c w) = ∏ d, (w d) ^ (ek₀ c d) := by
  rw [gFin_eq_leafMap, prod_ek₀]
  exact clean_entry (pivot1 c) (pivot2 c) (pivot3 c)
    (idxEquiv c).1.2 (idxEquiv c).2.1.2 (idxEquiv c).2.2.2 hc w

/-- **Non-vacuity** — the canonical leaf (`p1 = 20`, `p2 = 0`, `p3 = 1`) is clean; there is a clean
leaf, so `clean_hentry` is non-vacuous. -/
theorem exists_isClean : ∃ c : Fin numCharts, IsClean c := by
  refine ⟨idxEquiv.symm ⟨⟨20, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩
  have h := idxEquiv.apply_symm_apply
    (⟨⟨20, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩ : NativeFan334.Idx)
  show (pivot1 _, pivot2 _) ∈ cleanPairs
  rw [pivot1, pivot2, h]
  decide

-- Forced axiom gate: the CLEAN-144 `hentry` rests only on the clean-three foundational axioms.
#assert_banked_clean_batch [clean_entry, clean_hentry, exists_isClean]

end DLNFibre.DLN.Aoyagi.CleanHentry334
