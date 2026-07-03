import DLNFibre.Core.Analysis.RLCT.Zeta
import DLNFibre.Core.Analysis.RLCT.Integrability
import DLNFibre.Core.Meta.Cited
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Basic

/-!
# `RLCT.Cited` — the ONE bundled meromorphic-continuation monument (Atiyah 1970 + Saito/SLT)

The single cited monument the zeta-pole RLCT definition rests on. Everything else in the RLCT
foundation is **built** (the zeta integral + its convergence, `RLCT.Zeta`; the integrability
threshold *value*, `RLCT.Integrability`; the real↔complex codim transfer, in `Core`) or **proved**;
this file isolates the one external analytic result, as a `@[cited]` `axiom` on the citation cordon
(`DLNFibre.Core.Meta.Cited`; module name ends in `Cited` ⟹ the location check passes).

## The monument (certificate §2.1)

For a **real-analytic nonnegative germ** `K : (Fin n → ℝ) → ℝ` (`K ≥ 0`, e.g. the DLN square loss),
a **smooth compactly-supported cutoff** `φ` (`φ ≥ 0`, `φ x₀ ≠ 0`), and a base point `x₀` that is a
**zero of the germ** (`K x₀ = 0`, so the singularity is present), the local zeta function
`ζ_{K,φ}(s) = ∫ K^s φ` (holomorphic on `{Re s > 0}`, built cite-free in `RLCT.Zeta`):

* **continues meromorphically** to all of `ℂ` (a function `Z` agreeing with `ζ` on `{Re s > 0}`);
* its **poles form a discrete set of negative rationals**;
* it has a **largest pole `s₀ < 0` of finite order `m₀ ≥ 1`**; and — the *bundled identification* —
* **`s₀ = −(integrability threshold of `K` on `U`)`**, i.e. the largest pole is minus the RLCT.

This last conjunct is the load-bearing bundle (certificate §3.1 / warning §6.5): a *bare*
meromorphic-continuation axiom does **not** on its own give `s₀ = −rlct` — that identification needs
the resolution / normal-crossing computation, so it must be *inside* the cited statement (as the
paper's `propdefn` bundles it). Here `integrabilityThreshold K U` is R2a's cite-free value, which is
exactly the paper's `rlct_x(F)` restricted to the nonnegative germ (certificate §1.3, §3.1); the
`1_U`-integrability threshold and the smooth-`φ` zeta agree on the *maximal* pole `λ` (certificate
§1.1), which is what the bundle asserts.

**Sources.** M. Atiyah, *Resolution of singularities and division of distributions*, Comm. Pure
Appl. Math. **23**(2) (1970) 145–150 (the meromorphic continuation of `∫|F|^s`, poles on `ℚ_{<0}`,
via real-analytic resolution of singularities — the paper's attribution, `main.tex` L1811); the
"largest pole `= −rlct`" packaging is the SLT-facing form (Saito, arXiv:math/0702056; Watanabe 2009,
*Algebraic Geometry and Statistical Learning Theory*, CUP, Ch. on zeta functions). Bundled as ONE
cite because it is what the `(λ, m)` definition consumes.

**What this cite buys and does NOT.** It buys the *existence* of the pole `s₀` and hence of the pair
`(λ, m)` with `λ = −s₀ > 0` and `m = m₀` the pole order (the honest multiplicity), and Link 1
`λ = integrabilityThreshold` (`RLCT.RLCTPair`). It does **not** evaluate `λ` for the DLN germ — that
is the *separate* Watanabe/Aoyagi bracket `rlct = ½·codim` (`DLNFibre.DLN.RLCT.AoyagiCited`, already
on the cordon), off this file.
-/

open MeasureTheory Set Complex

namespace RLCT

variable {n : ℕ}

/-! ## API pre-stage — pin the Mathlib meromorphic vocabulary used in the cite

Durable contracts (`example` blocks) pinning the exact names/types the cited axiom's conclusion
uses, so a Mathlib pin drift is caught here rather than inside the axiom. -/

/-- `MeromorphicOn Z Set.univ` is the continuation predicate (meromorphic at every point). -/
example (Z : ℂ → ℂ) : Prop := MeromorphicOn Z Set.univ

/-- A pole of order `m₀ ≥ 1` at `s₀` is `meromorphicOrderAt Z s₀ = −m₀` in `WithTop ℤ` (a negative
integer order = a pole; the order's magnitude is the pole order). -/
example (Z : ℂ → ℂ) (s₀ : ℂ) (m₀ : ℕ) : Prop :=
  meromorphicOrderAt Z s₀ = ((-(m₀ : ℤ) : ℤ) : WithTop ℤ)

/-! ## The bundled cited axiom -/

-- The `@[cited "…"]` source string is a single long literal (author, journal, the bundled
-- conclusion); it cannot wrap. Disable the long-line + whitespace linters for the axiom only.
set_option linter.style.longLine false in
set_option linter.style.whitespace false in
/-- **Cited (Atiyah 1970 + Saito/SLT — the ONE bundled meromorphic-continuation monument).** For a
real-analytic nonnegative germ `K` with a zero at `x₀`, a smooth cutoff `φ` (`φ ≥ 0`, `φ x₀ ≠ 0`)
**supported inside a relatively compact open neighbourhood `U ∋ x₀`** on which `K` is in the *pole
regime* (`admissibleExponents K U` bounded above — so the threshold is honest, not the `sSup ∅ = 0`
junk), the local zeta `ζ_{K,φ}` continues meromorphically to `ℂ`; **its poles all lie in the left
half-plane**, and there is a **largest one `s₀ < 0`** (maximal real part among poles) of finite
order `m₀ ≥ 1` with `s₀` rational and **`s₀ = −(integrabilityThreshold K U)`** (the bundled
largest-pole-`= −rlct` identity). This is the sole analytic monument under the zeta-pole `(λ, m)`
definition; the extraction of `λ`, `m` and Link 1 are *built* on it (`RLCT.RLCTPair`).

The **locality** hypotheses (`x₀ ∈ U`, `U` relatively compact open, `tsupport φ ⊆ U`) and the
**pole-regime** guard (`BddAbove …`) are load-bearing: the paper's `propdefn` (`main.tex` L1804) uses
a relatively compact open nbhd of `x` precisely so the smooth-`φ` zeta and the `U`-integrability
threshold agree on the *maximal* pole; without them `s₀ = −threshold` is not pinned. The
**maximality** conjunct (`∀ s, pole → s.re ≤ s₀`) makes `s₀` genuinely the *largest* pole (justifying
`RLCT.largestPole`), not merely *a* pole.

The **single-zero** hypothesis `hUzero` (`x₀` is the *only* zero of `K` on `closure U`) is what keeps
the axiom **consistent** — without it it yields `False`. The continuation `Z` is *pinned* by conjunct
(a) (`Z = ζ` on `Re s > 0`) + the identity theorem, so it is literally the meromorphic continuation
of `∫ K^s φ`; since `φ` is supported near `x₀`, `Z` is *holomorphic* away from `x₀`'s pole line. But
`integrabilityThreshold K U` sees *all* of `U`: a second zero of `K` in `U` with a sharper threshold
would make `−threshold` a value where `Z` has **no** pole, yet conjuncts (largest-pole order = `−m₀`,
`m₀ ≥ 1`) demand a pole there — contradiction, so the existential is empty and the axiom proves `False`
(rev-r2b + decorrelated Codex: convergent counterexample `K = x²(x−2)⁶`, `φ` near `0` — `Z` holomorphic
at `s = −1/6` but `threshold = 1/6` forces a pole there). With `hUzero` over `closure U` (foreclosing
boundary zeros too), `K > 0` on `closure U \ {x₀}`, so `s₀` and `integrabilityThreshold K U` are both
governed solely by `x₀` and the identity holds — the local Atiyah/Saito "small `U`, `x₀` the sole
singularity" setup. -/
@[cited "Atiyah 1970 (CPAM 23:145-150) + Saito/SLT: continuation of ∫|F|^s φ, poles ℚ_{<0}, largest pole = -rlct"]
axiom cited_zeta_meromorphic_continuation {n : ℕ} (K φ : (Fin n → ℝ) → ℝ)
    (x₀ : Fin n → ℝ) (U : Set (Fin n → ℝ))
    (hK : AnalyticOnNhd ℝ K Set.univ) (hKnn : ∀ x, 0 ≤ K x) (hKx₀ : K x₀ = 0)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφnn : ∀ x, 0 ≤ φ x) (hφx₀ : φ x₀ ≠ 0)
    -- locality: `φ` is supported inside a relatively compact open nbhd `U` of the zero `x₀`;
    (hx₀U : x₀ ∈ U) (hUopen : IsOpen U) (hUcpt : IsCompact (closure U)) (hφU : tsupport φ ⊆ U)
    -- single zero: `x₀` is the ONLY zero of `K` on `closure U` — keeps the cite CONSISTENT (else it
    -- proves `False`: the pinned continuation is holomorphic where `−threshold` demands a pole);
    (hUzero : ∀ x ∈ closure U, K x = 0 → x = x₀)
    -- pole regime: the threshold on `U` is honest (admissible set bounded above), not the junk `0`;
    (hpole : BddAbove (admissibleExponents K U)) :
    ∃ (Z : ℂ → ℂ) (s₀ : ℝ) (m₀ : ℕ),
      -- the continuation agrees with the built zeta on the convergent half-plane;
      (∀ s : ℂ, 0 < s.re → Z s = zeta K φ s) ∧
      -- it is meromorphic on all of `ℂ`;
      MeromorphicOn Z Set.univ ∧
      -- every pole (negative meromorphic order) lies in the open left half-plane;
      (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re < 0) ∧
      -- `s₀` is the LARGEST pole (maximal real part among poles) — justifies `largestPole`;
      (∀ s : ℂ, meromorphicOrderAt Z s < 0 → s.re ≤ s₀) ∧
      -- it is a negative rational of finite order `m₀ ≥ 1`;
      s₀ < 0 ∧ (∃ q : ℚ, s₀ = q) ∧ 1 ≤ m₀ ∧
      meromorphicOrderAt Z (s₀ : ℂ) = ((-(m₀ : ℤ) : ℤ) : WithTop ℤ) ∧
      -- and the BUNDLED identification: the largest pole is minus the integrability threshold.
      s₀ = -(integrabilityThreshold K U)

end RLCT
