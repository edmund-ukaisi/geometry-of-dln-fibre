import DLNFibre.DLN.RLCT.Foundations.Loss
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `DLNFibre.DLN.RLCT.Foundations.Rlct` — the real log-canonical threshold

The measure substrate on `Params`, the RLCT `rlctAt` (Aoyagi Definition 1, the
integral-supremum form), and the order `rlctOrderAt` (the analytic pole multiplicity θ).
This is the **heavy** layer: all `MeasureTheory` imports are isolated here.

## The measure substrate (design-spec §0)
`Params H` is *definitionally* a `Pi` of function spaces (a `Matrix` is a function
`m → n → ℝ`), so it inherits `TopologicalSpace`, `MeasurableSpace`, and `MeasureSpace`
from Mathlib's product instances via `inferInstanceAs`. The measure is the product
Lebesgue (`volume`) measure on `ℝ^N`, `N = Σ_s H⁽ˢ⁾·H⁽ˢ⁺¹⁾` — the faithful S0-measure.
No explicit flattening to `EuclideanSpace` is needed.

## `rlctAt` (design-spec §2; Aoyagi Def 1, p.5)
`λ_{w*}(F) = sup{ c : ∫_U |F(w)|^{−c} φ(w) dw < ∞ }` with `k = 1` over ℝ (integrand
`|F|^{−c}`), `φ` a `C^∞` bump with `φ(w*) ≠ 0`. The bump is dropped via the existential
over neighbourhoods (`∃ U ∈ 𝓝 w*`), which recovers the bump-independent threshold
(design-spec §2). Value in `ℝ≥0∞` so the locally-nonvanishing case (`F(w*) ≠ 0`, every
`c'` admissible) gives `+∞`. The supremum is over the down-set of admissible real
exponents `c' ≥ 0`; the threshold itself is generically **not attained** (the integral
diverges *at* `c = λ`), so `sSup` is the faithful operation.

> **Precondition for faithfulness (design-spec §2, Codex §6.2):** `rlctAt` is the standard
> RLCT only for `F` real-analytic and `≢ 0` near `w*`. `dlnLoss B` is polynomial ⇒
> real-analytic, so the precondition holds for every use here. The equality to the bumped
> Def-1 value, and `λ(⟨Fᵢ⟩) = λ(∑Fᵢ²)`, are S1 lemmas.

## `rlctOrderAt` (design-spec §3 — FLAGGED SEAM)
The order θ is the multiplicity of the largest pole of the zeta function `Z(z) = ∫_U |F|^z φ`
at `z = −λ` (Aoyagi Def 1). Its faithful analytic definition needs meromorphic continuation
of `∫|F|^z φ` (Atiyah / Bernstein–Gelfand), which Mathlib lacks entirely. So `rlctOrderAt` is
carried as an **opaque placeholder** (total, no axiom): a function symbol of the right type
whose *value* is pinned only by the S2 citation (`Skeleton.lean`), where the cited
normal-crossing extraction returns the order as the chart-count `⨆ Card{j : …}`. It is **not**
the naive count of minimisers of `M(T)` (verified distinct: (2,2,2,2,2) has 6 minimisers but
θ = a(ℓ−a)+1 = 5; design-spec §3). The combinatorial deliverable is `aoyagiθ` (`Lambda.lean`);
A2 proves chart-count = a(ℓ−a)+1.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Topology

variable {L : ℕ}

/-- `Params H` inherits the product topology (definitionally a `Pi` of function spaces). -/
instance instTopologicalSpaceParams (H : Fin (L + 1) → ℕ) : TopologicalSpace (Params H) :=
  inferInstanceAs (TopologicalSpace (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- `Params H` inherits the product Lebesgue measure space (the S0-measure on `ℝ^N`). -/
noncomputable instance instMeasureSpaceParams (H : Fin (L + 1) → ℕ) : MeasureSpace (Params H) :=
  inferInstanceAs (MeasureSpace (∀ s : Fin L, (Fin (H s.castSucc)) → (Fin (H s.succ)) → ℝ))

/-- The real log-canonical threshold of `F` at `w*` (Aoyagi Def 1, integral-supremum form): the
supremum in `ℝ≥0∞` of the down-set of real exponents `c' ≥ 0` for which `|F|^{−c'}` is locally
integrable near `w*`. The bump is dropped via the existential over neighbourhoods. -/
noncomputable def rlctAt (H : Fin (L + 1) → ℕ) (F : Params H → ℝ) (wstar : Params H) : ENNReal :=
  sSup { c : ENNReal | ∃ c' : NNReal, c = (c' : ENNReal) ∧
          ∃ U ∈ 𝓝 wstar, IntegrableOn (fun w => |F w| ^ (-(c' : ℝ))) U volume }

/-- The order θ: the multiplicity of the largest pole of the zeta function `Z(z) = ∫_U |F|^z φ`
at `z = −rlctAt F w*` (Aoyagi Def 1). Carried as an opaque placeholder (total, axiom-free); its
value is pinned by the S2 citation (`rlct_of_normalCrossing`), which returns the order as the
chart-count. Mathlib lacks the meromorphic continuation a direct analytic definition needs
(design-spec §3 seam). -/
opaque rlctOrderAt (H : Fin (L + 1) → ℕ) (F : Params H → ℝ) (wstar : Params H) : ℕ

end DLNFibre.DLN.RLCT
