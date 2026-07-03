import DLNFibre.Core.Analysis.RLCT.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support

/-!
# `RLCT.Zeta` — the local archimedean zeta function `ζ_{K,φ}(s) = ∫ K^s φ`

The **local archimedean zeta function** of a loss germ, the analytic object whose largest pole
locates the RLCT (paper `propdefn`, `main.tex` L1804–1809; Watanabe SLT). For a nonnegative germ
`K : (Fin n → ℝ) → ℝ` (`K ≥ 0`, e.g. `K = |F|` for a real-analytic `F`, or the DLN square loss) and
a **smooth compactly-supported cutoff** `φ : (Fin n → ℝ) → ℝ` with `φ ≥ 0` and `φ(x₀) ≠ 0`,

`ζ_{K,φ}(s) := ∫ (K x)^s · φ(x) dvol(x)`   (`s ∈ ℂ`, complex power `(K x)^s = Complex.cpow`).

The cutoff is a smooth `φ ∈ C_c^∞`, **not** a raw indicator `1_U` (certificate §1.1/§6.4): the
maximal pole is a robust germ invariant under a smooth cutoff, whereas with a raw `1_U` the full
pole set is cutoff-sensitive; the smooth `φ` matches the standard cited continuation theorem.

**What this file builds (cite-free).** The integral is well-defined and finite for `Re s > 0`:
`zetaIntegrand_integrable` — for `Re s > 0`, a *continuous* germ `K` (so `x ↦ (K x)^s` is
continuous, `0` at the zeros) and a continuous compactly-supported `φ`, the integrand `(K x)^s·φ(x)`
is continuous with compact support, hence integrable
(`Continuous.integrable_of_hasCompactSupport`). This is the elementary half-plane-of-holomorphy
content — **no continuation cited** (certificate §2.3). The meromorphic continuation to all of `ℂ`,
the pole structure, and the identification of the largest pole with `−rlct` are the ONE bundled
monument, isolated in `RLCT.Cited`.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Complex

namespace RLCT

variable {n : ℕ}

/-- The **zeta integrand** `x ↦ (K x)^s · φ(x)` (complex power `Complex.cpow` of the real base
`K x ≥ 0`, cast to `ℂ`; `φ` real, cast to `ℂ`). The integrand of the local zeta function. -/
noncomputable def zetaIntegrand (K φ : (Fin n → ℝ) → ℝ) (s : ℂ) : (Fin n → ℝ) → ℂ :=
  fun x ↦ (K x : ℂ) ^ s * (φ x : ℂ)

@[simp] lemma zetaIntegrand_apply (K φ : (Fin n → ℝ) → ℝ) (s : ℂ) (x : Fin n → ℝ) :
    zetaIntegrand K φ s x = (K x : ℂ) ^ s * (φ x : ℂ) := rfl

/-- The **local archimedean zeta function** `ζ_{K,φ}(s) := ∫ (K x)^s · φ(x) dvol`. Defined by the
Bochner integral over Lebesgue `volume`; finite for `Re s > 0` (`zeta_convergent`), where it is the
paper's holomorphic germ. Its meromorphic continuation / pole structure is the bundled cite
(`RLCT.Cited`). -/
noncomputable def zeta (K φ : (Fin n → ℝ) → ℝ) (s : ℂ) : ℂ :=
  ∫ x, zetaIntegrand K φ s x

lemma zeta_def (K φ : (Fin n → ℝ) → ℝ) (s : ℂ) :
    zeta K φ s = ∫ x, zetaIntegrand K φ s x := rfl

/-! ## Convergence for `Re s > 0` (buildable, cite-free) -/

/-- For `Re s > 0` the complex power `x ↦ (K x)^s` is continuous on `(Fin n → ℝ)` when `K` is
continuous — at the zeros `{K = 0}` the value is `0^s = 0` and continuity holds because `Re s > 0`
(`Complex.continuous_ofReal_cpow_const`). -/
lemma continuous_cpow_germ {K : (Fin n → ℝ) → ℝ} (hK : Continuous K) {s : ℂ} (hs : 0 < s.re) :
    Continuous (fun x ↦ (K x : ℂ) ^ s) :=
  (Complex.continuous_ofReal_cpow_const hs).comp hK

/-- The **zeta integrand is continuous** for `Re s > 0`, given a continuous germ `K` and a
continuous cutoff `φ`: it is the product of the continuous complex power `(K ·)^s` and the
continuous cast `φ`. -/
lemma continuous_zetaIntegrand {K φ : (Fin n → ℝ) → ℝ} (hK : Continuous K) (hφ : Continuous φ)
    {s : ℂ} (hs : 0 < s.re) : Continuous (zetaIntegrand K φ s) := by
  unfold zetaIntegrand
  exact (continuous_cpow_germ hK hs).mul (Complex.continuous_ofReal.comp hφ)

/-- The **zeta integrand has compact support** when `φ` does: `(K x)^s · φ(x)` vanishes wherever
`φ(x) = 0`, so its support is contained in the support of `φ`. -/
lemma hasCompactSupport_zetaIntegrand {K φ : (Fin n → ℝ) → ℝ} (hφ : HasCompactSupport φ) (s : ℂ) :
    HasCompactSupport (zetaIntegrand K φ s) := by
  refine hφ.mono ?_
  -- `support (zetaIntegrand …) ⊆ support φ`: where `φ x = 0` the integrand is `_ * 0 = 0`.
  intro x hx
  simp only [Function.mem_support, ne_eq, zetaIntegrand] at hx ⊢
  intro hφx
  exact hx (by rw [hφx, Complex.ofReal_zero, mul_zero])

/-- **Convergence for `Re s > 0` (BUILT, cite-free).** For a continuous nonnegative germ `K`, a
continuous compactly-supported cutoff `φ`, and `Re s > 0`, the zeta integrand `(K x)^s · φ(x)` is
integrable: it is continuous (`continuous_zetaIntegrand`) with compact support
(`hasCompactSupport_zetaIntegrand`), so
`Continuous.integrable_of_hasCompactSupport` applies. This defines the half-plane of holomorphy — no
meromorphic continuation is needed here (certificate §2.3). -/
theorem zetaIntegrand_integrable {K φ : (Fin n → ℝ) → ℝ} (hK : Continuous K) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {s : ℂ} (hs : 0 < s.re) :
    Integrable (zetaIntegrand K φ s) :=
  (continuous_zetaIntegrand hK hφ hs).integrable_of_hasCompactSupport
    (hasCompactSupport_zetaIntegrand hφc s)

end RLCT
