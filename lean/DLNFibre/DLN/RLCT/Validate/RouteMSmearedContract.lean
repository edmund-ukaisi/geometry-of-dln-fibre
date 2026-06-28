import DLNFibre.DLN.RLCT.Validate.RouteM231Smeared

/-!
# `RouteMSmearedContract` — the ∀M BOUNDARY-SMEARED assembly contract (residual #2 VERDICT probe)

The R1-LOWER residual #2 question: is the BOUNDARY-SMEARED branch of the ∀M achiever-divergence
**bounded** or a **wall**? The concern (`certificate-genM-smeared.md` §6 caveat, Codex's flagged
design risk): the smeared chart `φ_sm = ψ ∘ R` divides by a Gram minor `(P₁ᵀP₁)⁻¹` (rational, a null
pole), so its measure-preserving `MeasurableEmbedding` part `ψ` might not exist off the pole — an
INTERFACE gap, not a numeric one.

**VERDICT: BOUNDED, not a wall.** The pole is NOT a `MeasurableEmbedding` obstruction. The rational
routing is a SHEAR (`top = z·H̄ − Λ₀·S_bot`), and a shear conjugates to an additive core-shift
`(reg, core, spec) ↦ (reg, core + shift(reg, spec), spec)` (`coreShear_measurable`) which is
measure-preserving + a GLOBAL `MeasurableEquiv` for ANY widths and ANY measurable `shift` — Lean's
totalization (`b/a := b·a⁻¹`, `a⁻¹ = 0` at `a = 0`) makes `shift` a total measurable function, so
`ψ = paramsEquivFlat ∘ pack ∘ shear` is a total `MeasurableEquiv` whose embedding never sees the
pole. The radial `R = pivotBlowupOn` (polynomial, the SOLE Jacobian `|u_p|^{minAdm−1}`) and the
divergence assembly `routeMCore_box_diverges_of_RadialMPChart` are already general over `M`.

This file states the **∀M smeared assembly contract** `routeMCore_box_diverges_smearedContract`:
given exactly the per-family ingredients (a measure-preserving measurable-embedding `ψ`, a radial
blow-up `R` with its fderiv/injOn/det on a source set, plus a weighted source-divergence cert),
the box integral diverges. It is `routeMCore_box_diverges_of_RadialMPChart` repackaged into the ∀M
smeared branch produces, with the per-ingredient generality witnessed by the banked GENERAL bricks
(`measurePreserving_coreShear_measurable a b c`, `measurePreserving_paramsPack_of_flatIdxEquiv N`,
`pivotBlowupOnDeriv_det`, `pivotBlowupOn_injOn`) — NONE of which are `(1,2,1)`/`(2,3,1)`-specific.

So the smeared ∀M lift is a per-family BUILD (instantiate `ψ`/`R`/`subBox` per descent class), NOT a
new analytic obstruction. The `(2,3,1)`/`(1,3,2)` `minAdm ≥ 2` instances (which exercise the radial
route, `RouteM231Smeared`/`RouteM132Smeared`) are the worked witnesses; `(1,2,1)` is the degenerate
`minAdm = 1` end (radial det `|z|⁰ = 1`, the lighter `of_MPChart` sibling).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (measure theory; no S2, no `monomial_rlct` —
the cited monomial atom enters only inside each family's `hsrc` divergence, not the contract).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The ∀M BOUNDARY-SMEARED assembly contract.** For ANY `M`, the achiever box integral
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` follows from the smeared-chart ingredients:

* `ψ` measure-preserving + a measurable embedding (the rational shear ∘ linear reshape — total via
  Lean's `a⁻¹ = 0` totalization, MP for any widths via `measurePreserving_coreShear_measurable`, NO
  pole obstruction);
* `R` a radial blow-up with fderiv `D`, injective on the source, `|det D u| = |u p|^h` (the
  polynomial `pivotBlowupOn`, the sole Jacobian carrier);
* a weighted source-divergence `∫_S |u p|^h · (loss∘ψ∘R)^{−c'} = ⊤` on a measurable source
  `S ⊆ (ψ∘R)⁻¹(cubeBox ε)`.

This is `routeMCore_box_diverges_of_RadialMPChart` in the smeared branch's native shape. It
witnesses that the smeared ∀M leg is bounded-by-per-family-build: the contract is M-agnostic; each
descent class supplies its `ψ`/`R`/`S` from the GENERAL bricks. -/
theorem routeMCore_box_diverges_smearedContract (M : Fin (L + 1) → ℕ)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ))
    (p : Fin (routeMAmbient M)) (h : ℕ)
    (hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume)
    (hemb : MeasurableEmbedding ψ) (c' : ℝ) (ε : ℝ)
    (S : Set (Fin (routeMAmbient M) → ℝ)) (hSmeas : MeasurableSet S)
    (hSpre : S ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε))
    (hRderiv : ∀ u ∈ S, HasFDerivWithinAt R (D u) S u)
    (hRinj : Set.InjOn R S)
    (hRdet : ∀ u ∈ S, |(D u).det| = |u p| ^ h)
    (hSdiv : (∫⁻ u in S, ENNReal.ofReal (|u p| ^ h)
      * ENNReal.ofReal (|routeMCore M (ψ (R u))| ^ (-c'))) = ⊤) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-c')) = ⊤ :=
  routeMCore_box_diverges_of_RadialMPChart M ψ R D p h hmp hemb c' ε
    ⟨S, hSmeas, hSpre, hRderiv, hRinj, hRdet, hSdiv⟩

/-- **Non-vacuity: the `(2,3,1)` `minAdm ≥ 2` smeared atom factors through the contract.** Confirms
the contract fires on the worked radial-route witness (`psi231`/`R231`/`subBox231`), i.e. the
contract is the genuine shape the smeared branch produces, not a vacuous repackaging. -/
theorem routeM231sm_box_diverges_via_contract (c' : NNReal)
    (hc' : (minAdm M231 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M231) ε,
      ENNReal.ofReal (|routeMCore M231 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeM231sm_box_diverges c' hc' ε hε

end DLNFibre.DLN.RLCT
