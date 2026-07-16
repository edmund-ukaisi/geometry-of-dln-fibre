import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepRankGen
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotEnergyPos

set_option linter.style.longLine false

/-!
# `RouteMSJShellFrontChargeBinding` — the genericity-discharged shell→front-charge link (3a scaffold)

**Thread `genm-3abase` (aoyagi-full Stage 2), the terminal (3a) deep build — the G1↔G2 connective link.**
`shellSpine_le_frontCharge` (banked) threads two a.e.-genericity hypotheses `hGae`/`hEtopae`; this module
DISCHARGES both from the landed inputs at a BINDING cut, giving an unconditional shell→front-charge bound:

- `hGae` (corank Gram `Q_b Q_bᵀ` PosDef a.e.): `hGae_from_deepRank` (banked) ← `deepFactor_hZrank_of_le`
  (hZrank, landed) ← `M₁−(t+j) ≤ deepTailMin M` from `tailWidth_le_deepTailMin_of_binding` (banked, needs the
  binding-cut hypotheses `hbind`/`t+1 ≤ min(M₀,M₁)`).
- `hEtopae` (pivot energy `E_top > 0` a.e.): `deepFactor_hEtopae` (landed) ← `1 ≤ t`, all widths `≥ 1`.

So at a binding cut the shell-restricted spine integrand is UNCONDITIONALLY dominated by the coupled
front-charge box integral. This is the scaffold link between G1 (box → ∑-shell, unbuilt) and G2
(∫ front-charge < ⊤ via deepRankLE + the coupled per-cell `hfin`, unbuilt). Native, sorry-free, axiom-clean.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal

variable {L : ℕ}

/-- **Genericity-discharged shell → front-charge (binding cut).** At a binding cut `t` (`hbind`) with a
strict shell `j`, all widths `≥ 1`, and `1 ≤ t`, the shell-restricted spine integrand is dominated by the
coupled `(z, A_cor)`-box front-charge integral — the two a.e. hypotheses of `shellSpine_le_frontCharge`
discharged from the landed hZrank/hEtopae. -/
theorem shellSpine_le_frontCharge_binding (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) (ε c' : ℝ)
    (hj : j ≤ min (M 0 - t) (M 1 - t))
    (hc' : ((M 0 - (t + j) : ℕ) : ℝ) * ((M 1 - (t + j) : ℕ) : ℝ) / 2 < c')
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (htb : t + 1 ≤ min (M 0) (M 1))
    (hbind : minAdm M = peelCharge M t + minAdm (redChain t M)) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ p in paramsBoxM (redChain (t + j) M) 1 ×ˢ matBox (M 1 - (t + j)) (M 2) 1,
          frontChargeIntegrand M (t + j) c' p := by
  have hb : M 1 - t ≤ deepTailMin M := tailWidth_le_deepTailMin_of_binding M t htb hbind
  have hb' : M 1 - (t + j) ≤ deepTailMin M := le_trans (by omega) hb
  have hGae := hGae_from_deepRank M (t + j) (deepFactor_hZrank_of_le M (t + j) hb')
  have hEtopae := deepFactor_hEtopae M t j ht1 hnd
  exact shellSpine_le_frontCharge M t j κ ε c' hj hc' hGae hEtopae

end DLNFibre.DLN.RLCT
