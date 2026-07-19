import DLNFibre.DLN.RLCT.Engine.CenterIndices
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# `DLNFibre.DLN.RLCT.Engine.QNodeChart` — the parametric center-split Homeomorph (carrier remainder)

The blow-up chart's ambient coordinate split: `qOfCenter` takes an INJECTIVE center selector
`c : Fin d → Fin (flatDim M)` (the flat coordinates of a blow-up center — `resBlockCenterIndices` for
the residual/d-family, or the `u`-pivot's birth-corner coordinate for case-1(1)) and produces the
`Homeomorph` splitting `Params M` into the `d` center coordinates × the `flatDim M − d` rest. It is
PARAMETRIC in `c` (elder-gate9: the arithmetic selector is banked in `CenterIndices`; the `u`-pivot
coordinate enters as part of `c` at the call site, so this piece does not block on the `divBirthCoord`
field). The per-edge wrapper `qEdgeOf` computes `d = dCenterOfEdge` and instantiates `c`.

**PER-EDGE keying** (coverage seam Q4 / elder-gate9 amendment 1): `d_center` is the per-EDGE count
(`dCenterOfEdge`), not the node sum — coverage's per-edge `β_e`/`pivotChart` index `Fin d_center_edge`
matches `qOfCenter`'s `Fin d` factor directly, with no node-sum slicing (the gate partitions per-edge).

Traps (carrier-remainder-spec §1): B — the permutation from the injective selector, via range +
complement (`Equiv.ofInjective` + `Equiv.sumCompl`, the `Fintype.card` complement bookkeeping in
`centerPerm`); C — stay on the CLE (`paramsEquivFlatCLE`), do the split on the flat `Fin (flatDim M) →
ℝ` side (never on `Params M` directly, dodging the `Matrix.module`/`NormedSpace` diamond); D —
`arrowCongr` continuity via the banked finite-pi Homeomorph combinators.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The center permutation** (trap B): from an injective center selector `c : Fin d → Fin (flatDim M)`,
the equiv `Fin (flatDim M) ≃ Fin d ⊕ Fin (flatDim M − d)` splitting the flat coordinates into the `d`
center coordinates (the range of `c`) and the `flatDim M − d` rest (its complement). The complement
card is `flatDim M − d` (`card (range c) = d` by injectivity; `Fintype.card_subtype_compl`). -/
noncomputable def centerPerm (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) : Fin (flatDim M) ≃ Fin d ⊕ Fin (flatDim M - d) := by
  classical
  have hcardR : Fintype.card {x : Fin (flatDim M) // x ∈ Set.range c} = d := by
    have h := Fintype.card_congr (Equiv.ofInjective c hinj)
    rw [Fintype.card_fin] at h
    exact h.symm
  have hcardC : Fintype.card {x : Fin (flatDim M) // x ∉ Set.range c} = flatDim M - d := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardR]
  exact (Equiv.sumCompl (· ∈ Set.range c)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective c hinj).symm (Fintype.equivFinOfCardEq hcardC))

/-- **The center-split Homeomorph** (the intricate remainder): `Params M ≃ₜ (Fin d → ℝ) × (Fin
(flatDim M − d) → ℝ)`, splitting off the `d` center coordinates named by an injective `c`. Composed
`paramsEquivFlatCLE.toHomeomorph` (Params ≃ₜ flat, trap C: on the CLE instance) ∘ `piCongrLeft
(centerPerm)` (reindex the flat coords, trap D) ∘ `sumArrowHomeomorphProdArrow` (⊕ → ×). -/
noncomputable def qOfCenter (M : Fin (L + 1) → ℕ) {d : ℕ} (c : Fin d → Fin (flatDim M))
    (hinj : Function.Injective c) :
    Params M ≃ₜ (Fin d → ℝ) × (Fin (flatDim M - d) → ℝ) :=
  ((paramsEquivFlatCLE M).toHomeomorph.trans
      (Homeomorph.piCongrLeft (Y := fun _ : Fin d ⊕ Fin (flatDim M - d) => ℝ)
        (centerPerm M c hinj))).trans
    Homeomorph.sumArrowHomeomorphProdArrow

/-- **Per-edge center dimension** (elder-gate9 amendment 1; the count the `geometricLeafPaths` fan-out
uses). case-1(1) = `1` (the `u`-pivot chart); case-1(2) = `runLen · resCols` (the d-family, NOT
resRows); case-2 = `resRows · resCols`; rollover = `0` (chartless). -/
def dCenterOfEdge (node : StepData M) (e : Edge M) : ℕ :=
  match e.case with
  | StepCase.case11 => 1
  | StepCase.case12 => e.subst.runLen * node.resCols
  | StepCase.case2 => node.resRows * node.resCols
  | StepCase.rollover => 0

/-- **The residual-block selector with a totality fallback** (trap A): on the reachable cone the
bounds `J+rows ≤ M s.castSucc`, `J+cols ≤ M s.succ`, `s < L` hold and this is `resBlockCenterIndices`;
off the cone (junk states) it falls back to the canonical injective `Fin.castLE hd`. Injective either
way — so `qOfCenter` always applies. -/
noncomputable def resBlockOrFallback (M : Fin (L + 1) → ℕ) (s J rows cols : ℕ)
    (hd : rows * cols ≤ flatDim M) : Fin (rows * cols) → Fin (flatDim M) :=
  if h : ∃ hs : s < L, J + rows ≤ M (⟨s, hs⟩ : Fin L).castSucc ∧ J + cols ≤ M (⟨s, hs⟩ : Fin L).succ
  then resBlockCenterIndices M ⟨s, h.choose⟩ J rows cols h.choose_spec.1 h.choose_spec.2
  else Fin.castLE hd

theorem resBlockOrFallback_injective (M : Fin (L + 1) → ℕ) (s J rows cols : ℕ)
    (hd : rows * cols ≤ flatDim M) : Function.Injective (resBlockOrFallback M s J rows cols hd) := by
  unfold resBlockOrFallback
  split
  · exact resBlockCenterIndices_injective M _ J rows cols _ _
  · exact Fin.castLE_injective hd

/-- **The case-1(1) `u`-pivot selector** (`d = 1`): the merged divisor's immutable birth corner
`(s, J)` (`divBirthCoord mergeIdx`) as a flat coord `flatCoordOf M s ⟨J⟩ ⟨J⟩` — NOT node-local (the
divisor was born earlier). Totality fallback (trap A) off the reachable cone; injective trivially
(`Fin 1` is a subsingleton). -/
noncomputable def uCoordSel (M : Fin (L + 1) → ℕ) (node : StepData M) (es : ChartSubst M)
    (hd : 1 ≤ flatDim M) : Fin 1 → Fin (flatDim M) := fun _ =>
  if h : ∃ hm : es.mergeIdx < node.numDiv, (node.divBirthCoord ⟨es.mergeIdx, hm⟩).1 < L then
    let sc := node.divBirthCoord ⟨es.mergeIdx, h.choose⟩
    if h2 : sc.2 < M (⟨sc.1, h.choose_spec⟩ : Fin L).castSucc ∧
        sc.2 < M (⟨sc.1, h.choose_spec⟩ : Fin L).succ then
      flatCoordOf M ⟨sc.1, h.choose_spec⟩ ⟨sc.2, h2.1⟩ ⟨sc.2, h2.2⟩
    else Fin.castLE hd 0
  else Fin.castLE hd 0

theorem uCoordSel_injective (M : Fin (L + 1) → ℕ) (node : StepData M) (es : ChartSubst M)
    (hd : 1 ≤ flatDim M) : Function.Injective (uCoordSel M node es hd) :=
  fun a b _ => Subsingleton.elim a b

/-- **The per-edge center-split Homeomorph** (coverage's trigger): `qEdgeOf node e` splits `Params M`
along the per-EDGE center (case-2/case-1(2) residual block; case-1(1) `u`-pivot; rollover chartless).
Encapsulates the per-case selector dispatch + its injectivity + the totality fallback + the `d ≤
flatDim` bound (`hd`, from reachability). `Fin d` matches coverage's `d_center_edge` directly. -/
noncomputable def qEdgeOf (node : StepData M) (e : Edge M) (hd : dCenterOfEdge node e ≤ flatDim M) :
    Params M ≃ₜ (Fin (dCenterOfEdge node e) → ℝ) × (Fin (flatDim M - dCenterOfEdge node e) → ℝ) := by
  obtain ⟨ec, es, ech⟩ := e
  cases ec with
  | case11 => exact qOfCenter M (uCoordSel M node es hd) (uCoordSel_injective M node es hd)
  | case12 =>
      exact qOfCenter M (resBlockOrFallback M node.layer node.cleared es.runLen node.resCols hd)
        (resBlockOrFallback_injective M node.layer node.cleared es.runLen node.resCols hd)
  | case2 =>
      exact qOfCenter M (resBlockOrFallback M node.layer node.cleared node.resRows node.resCols hd)
        (resBlockOrFallback_injective M node.layer node.cleared node.resRows node.resCols hd)
  | rollover => exact qOfCenter M Fin.elim0 (fun a => a.elim0)

end DLNFibre.DLN.RLCT.Engine
