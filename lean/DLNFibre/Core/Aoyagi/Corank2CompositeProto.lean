import DLNFibre.Core.Aoyagi.Corank2HidealProto
import DLNFibre.Core.Aoyagi.Corank2TerminalProto
import DLNFibre.Core.Aoyagi.BlockBlowup

/-!
# `Core.Aoyagi.Corank2CompositeProto` — GATE-3 END-TO-END: composing the proven mechanisms on a chart map

The composition brick for the END-TO-END gate (= #112's first chart). The three ideal-identity mechanisms
are proven in ISOLATION (L-A block-elim over the coupled `Δ`; L-B maintenance over abstract `b_p/r/c/X`;
L-C terminal over a residual block). The END-TO-END question (charter §3: composition is where
isolated-green fails late at the consumer) is whether they COMPOSE on a literal chart map `g` through the
product. This module provides the missing composition primitive — `regionRepresents_comp` (precompose a
region-representation with a continuous chart map `g`) — and demonstrates it chains the L-A block-elim
under a genuine blow-up `g`, at the real ambient.

`regionRepresents_comp` + the banked `RegionRepresents.trans` + `terminal_bezout` are the three composition
operations the faithful (3,3,4) chart is assembled from; this pins the first (the precompose), which the
banked API lacked.
-/

open Matrix Set
open DLNFibre.Core.Aoyagi DLNFibre.Core.Aoyagi.Corank2Proto DLNFibre.Core.Aoyagi.Corank2HidealProto

namespace DLNFibre.Core.Aoyagi.Corank2CompositeProto

variable {n : ℕ}

/-- **`RegionRepresents` precomposes with a continuous chart map.** If `G` is represented by `F` on `V`,
then `Gᵢ∘g` is represented by `Fⱼ∘g` on `g⁻¹'V`, cofactors `aᵢⱼ∘g` (continuous by `ContinuousOn.comp`).
This is the composition primitive the faithful chart needs (pull the block-elim / maintenance ideal
identity back through the blow-up), and it was absent from the banked `RegionRepresents` API (which had
`.trans`/`.mono`/`.of_eqOn` but no precompose). -/
theorem regionRepresents_comp {m p : ℕ} {G : Fin p → (Fin n → ℝ) → ℝ}
    {F : Fin m → (Fin n → ℝ) → ℝ} {V : Set (Fin n → ℝ)} (h : RegionRepresents G F V)
    {g : (Fin n → ℝ) → (Fin n → ℝ)} (hg : Continuous g) :
    RegionRepresents (fun i ↦ G i ∘ g) (fun j ↦ F j ∘ g) (g ⁻¹' V) := by
  obtain ⟨a, ha, heq⟩ := h
  refine ⟨fun i j ↦ (a i j) ∘ g, fun i j ↦ (ha i j).comp hg.continuousOn (Set.mapsTo_preimage g V),
    fun u hu i ↦ ?_⟩
  simpa only [Function.comp_apply] using heq (g u) hu i

/-- **Composition demonstration — the L-A block-elim precomposed with a genuine blow-up `g`.** The gate-2
block-elim `⟨(∏C)⟩ = ⟨peeled⟩` (both directions, over the genuinely coupled `Δ`) pulls back through any
continuous chart map `g` (e.g. the banked `blockBlowupMap`): `⟨(∏C)∘g⟩ = ⟨peeled∘g⟩` on `g⁻¹'univ`,
cofactors the pulled-back `Q₁` entries (continuous). This exercises `regionRepresents_comp` on the real
coupled block-elim under a real chart map — the first composition step of the faithful (3,3,4) chart. -/
theorem blockElim_under_chart (g : (Fin 21 → ℝ) → (Fin 21 → ℝ)) (hg : Continuous g) :
    RegionRepresents
      (fun i ↦ flat (Pmat (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc) i ∘ g)
      (fun j ↦ flat (peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc) j ∘ g)
      (g ⁻¹' Set.univ) :=
  regionRepresents_comp (blockElim_step_fwd Set.univ) hg

end DLNFibre.Core.Aoyagi.Corank2CompositeProto
