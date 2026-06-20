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

/-! ## The weighted compact-set threshold `θ(G, ρ; K)` (S1 substrate; thread 05)

The clean abstraction unifying S1 and matching the narrowed S2: the supremum of exponents `c'` for
which the **weighted** density `|G|^{−c'}·ρ` is integrable on some open set containing the compact
fibre `K`. `rlctAt F w* = θ(F, 1, {w*})` (`rlctAt_eq_weightedThreshold`). After a resolution chart
the Jacobian becomes the weight `ρ`; the S1.1 transport (`Skeleton.lean`) is stated in this object.
Carried on a general `MeasureSpace`/`TopologicalSpace` source so it can host a resolution domain
`M`, not only `Params`. -/

/-- The weighted compact-set RLCT threshold `θ(G, ρ; K)` (thread 05): the `sSup` of exponents
`c' ≥ 0` for which `|G|^{−c'}·ρ` is integrable on some open set `Ω ⊇ K`. General source type
(hosts a resolution domain). -/
noncomputable def weightedThreshold {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    (G ρ : M → ℝ) (K : Set M) : ENNReal :=
  sSup { c : ENNReal | ∃ c' : NNReal, c = (c' : ENNReal) ∧
          ∃ Ω : Set M, IsOpen Ω ∧ K ⊆ Ω ∧
            IntegrableOn (fun w => |G w| ^ (-(c' : ℝ)) * ρ w) Ω volume }

/-- `rlctAt F w*` is the weighted threshold with trivial weight at the singleton fibre:
`θ(F, 1, {w*})`. The connector letting all of S1 (stated on `weightedThreshold`) specialise to
`rlctAt`. The
`∃ U ∈ 𝓝 w*` of `rlctAt` and the `∃ Ω open ⊇ {w*}` of `weightedThreshold` are interchangeable
(`mem_nhds_iff` + `IsOpen.mem_nhds`), and the weight `1` is dropped by `mul_one`. -/
theorem rlctAt_eq_weightedThreshold (H : Fin (L + 1) → ℕ) (F : Params H → ℝ) (wstar : Params H) :
    rlctAt H F wstar = weightedThreshold F (fun _ => 1) {wstar} := by
  unfold rlctAt weightedThreshold
  have hfun : ∀ c' : NNReal, (fun w : Params H => |F w| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) w)
      = (fun w => |F w| ^ (-(c' : ℝ))) := fun c' => by funext w; rw [mul_one]
  congr 1
  ext c
  constructor
  · rintro ⟨c', rfl, U, hU, hint⟩
    obtain ⟨Ω, hΩU, hΩopen, hwΩ⟩ := mem_nhds_iff.1 hU
    exact ⟨c', rfl, Ω, hΩopen, by simpa using hwΩ, by rw [hfun]; exact hint.mono_set hΩU⟩
  · rintro ⟨c', rfl, Ω, hΩopen, hKΩ, hint⟩
    rw [hfun] at hint
    exact ⟨c', rfl, Ω, hΩopen.mem_nhds (hKΩ rfl), hint⟩

/-- `rlctAt` on a general `MeasureSpace`/`TopologicalSpace` source: `θ(F, 1, {w*})`. The
network-agnostic RLCT, used to state S1.5 (disjoint-block additivity) on a product domain `X × Y`
whose factors need not be `Params`. On `Params` it agrees with `rlctAt` (both unfold to
`weightedThreshold F 1 {w*}` via `rlctAt_eq_weightedThreshold`). -/
noncomputable def rlctAtOn {M : Type*} [MeasureSpace M] [TopologicalSpace M]
    (F : M → ℝ) (wstar : M) : ENNReal :=
  weightedThreshold F (fun _ => 1) {wstar}

/-- On `Params`, `rlctAtOn` is `rlctAt` (both are `θ(F, 1, {w*})`). -/
theorem rlctAtOn_eq_rlctAt (H : Fin (L + 1) → ℕ) (F : Params H → ℝ) (wstar : Params H) :
    rlctAtOn F wstar = rlctAt H F wstar :=
  (rlctAt_eq_weightedThreshold H F wstar).symm

end DLNFibre.DLN.RLCT
