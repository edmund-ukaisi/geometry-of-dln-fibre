import DLNFibre.Core.Analysis.RLCT.Zeta
import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Meta.Cited
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Basic

/-!
# `RLCT.Cited` — the ONE bundled **local** zeta-pole monument (Atiyah 1970 + Saito/SLT)

The single cited monument the zeta-pole RLCT definition rests on. Everything else in the RLCT
foundation is **built** (the zeta integral + its convergence, `RLCT.Zeta`; the local RLCT
`rlctAt`, `RLCT.Local`; the regional threshold, `RLCT.Integrability`; the real↔complex codim
transfer, in `Core`) or **proved**; this file isolates the one external analytic result, as a
`@[cited]` `axiom` on the citation cordon (`DLNFibre.Core.Meta.Cited`; module name ends in `Cited`
⟹ the location check passes).

## The monument — stated LOCALLY (certificate §7.5)

The cite is the paper's `propdefn` (`main.tex` L1804), **as a purely local statement about the germ
of `K` at one point `x₀`** — *not* a regional statement over a nbhd `U`. For a real-analytic
nonnegative germ `K` with `K x₀ = 0`, a smooth compactly-supported cutoff `φ` (`φ ≥ 0`, `φ x₀ ≠ 0`,
`supp φ` a small nbhd of `x₀`):

* `ζ_{K,φ}(s) = ∫ K^s φ` (holomorphic on `{Re s > 0}`, built cite-free in `RLCT.Zeta`) **continues
  meromorphically** to all of `ℂ`;
* its **poles form a discrete set of negative rationals** (all in the left half-plane);
* the **largest pole `s₀ < 0`** (maximal real part) has finite order `m₀ ≥ 1`; and — the bundled
  identification — **`s₀ = −rlctAt K x₀`**, the *local* RLCT of the germ at `x₀` (`RLCT.Local`).

## Why LOCAL, not regional (certificate §7 — the altitude fix)

The earlier form bundled the *regional* identity `s₀ = −integrabilityThreshold K U` (a threshold on
a whole nbhd `U`). That was an **altitude confusion** and was in fact **inconsistent**: the
continuation `Z` is pinned to the germ at `x₀` (`φ` supported near `x₀`), so it is holomorphic away
from `x₀`'s pole line, while the regional threshold sees a far-away sharper zero — forcing a pole
`Z` does not have (`⟹ False`; rev-r2b counterexample `K = x²(x−2)⁶`). Patching it with a *sole-zero*
hypothesis (`x₀` the only zero on `closure U`) restored consistency but **excluded the DLN fibre**
(`{K_B = 0} = mult⁻¹(B)` is a connected positive-dim zero set — never a sole zero), making the
cite un-instantiable at the payoff's germ.

The fix (certificate §7.2, the three-way split): state the cite **locally**. `s₀` and `rlctAt K x₀`
are **both germ-at-`x₀` data**, so `s₀ = −rlctAt K x₀` is the true content of the paper's prop
— a purely local identity **no far-away zero can contradict** (consistent), and **defined for a
non-isolated zero set** (`rlctAt` reads local integrability, fine on a connected fibre) so it is
**DLN-admissible at any fibre point** with no sole-zero hypothesis. The regional connection to R2a's
`integrabilityThreshold K U` is factored out as the separate, buildable **Bridge B**
(`RLCT.integrabilityThreshold_eq_localRlct_of_worst`); the DLN payoff routes through the *global*
Watanabe/Aoyagi cites (`AoyagiCited.lean`), never through instantiating this axiom at `K_B`.

**Sources.** M. Atiyah, *Resolution of singularities and division of distributions*, Comm. Pure
Appl. Math. **23**(2) (1970) 145–150 (the meromorphic continuation of `∫|F|^s`, poles on `ℚ_{<0}`,
via real-analytic resolution — the paper's attribution, `main.tex` L1811); the "largest pole
`= −rlct_x`" packaging is the SLT-facing form (Saito, arXiv:math/0702056; Watanabe 2009, *Algebraic
Geometry and Statistical Learning Theory*, CUP, Ch. on zeta functions). ONE `@[cited]` axiom.

**What this cite buys and does NOT.** It buys the *existence* of the pole `s₀` and hence of the pair
`(λ, m)` with `λ = −s₀ = rlctAt K x₀ > 0` and `m = m₀` the pole order (the multiplicity), and the
*local* Link 1 `λ = rlctAt K x₀` (`RLCT.RLCTPair`). It does **not** evaluate `λ` for the DLN germ
— that is the *separate global* Watanabe/Aoyagi bracket `rlct = ½·codim`
(`DLNFibre.DLN.RLCT.AoyagiCited`), off this file.
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

/-! ## The bundled cited axiom — LOCAL -/

-- The `@[cited "…"]` source string is a single long literal (author, journal, the bundled
-- conclusion); it cannot wrap. Disable the long-line + whitespace linters for the axiom only.
set_option linter.style.longLine false in
set_option linter.style.whitespace false in
/-- **Cited (Atiyah 1970 + Saito/SLT — the ONE bundled LOCAL zeta-pole monument).** For a
real-analytic nonnegative germ `K` with a zero at `x₀` and a smooth cutoff `φ` (`φ ≥ 0`, `φ x₀ ≠ 0`)
supported in a small open nbhd `U ∋ x₀`, the local zeta `ζ_{K,φ}` continues meromorphically to `ℂ`;
its poles all lie in the left half-plane; there is a **largest pole `s₀ < 0`** (maximal real part) of
finite order `m₀ ≥ 1`, rational; and — the bundled identification — **`s₀ = −rlctAt K x₀`** (minus the
*local* RLCT of the germ at `x₀`). This is the sole analytic monument under the zeta-pole `(λ, m)`
definition; `λ`, `m` and the local Link 1 are *built* on it (`RLCT.RLCTPair`).

**Local, with ONE worst-point hypothesis on `supp φ`** (certificate §7.5, round-5 fix): `s₀` is a
`supp φ`-quantity — the zeta `∫ K^s φ` sees *all* of `supp φ`, so `s₀ = −inf_{x ∈ supp φ} rlct_x`. The
hypothesis `hWorst : ∀ x ∈ tsupport φ, rlctAt K x₀ ≤ rlctAt K x` (`x₀` a worst singularity **on
`supp φ`**) makes that `inf` equal `rlctAt K x₀`, so the bundled `s₀ = −rlctAt K x₀` is *true*. Without
it the cite is **inconsistent**: a wide `φ` covering a separate, sharper zero forces a pole `Z` does
not have at `−rlctAt K x₀` (`K = x²(x−1)⁸`, `φ` over both zeros ⟹ `s₀ = −1/8 ≠ −1/2`). This is the
paper's "`U` small enough" as a *threshold* condition on `supp φ` — **not** a sole-zero condition, so
it **admits the DLN fibre**: at a smooth fibre point the local RLCT is (locally) constant along the
connected fibre, so `hWorst` holds with equality and the cite fires at `K_B`. The `U` still only
localizes `φ`'s support (`x₀ ∈ U`, `U` open, `tsupport φ ⊆ U`). The maximality conjunct
(`∀ s, pole → s.re ≤ s₀`) makes `s₀` genuinely the *largest* pole (justifying `RLCT.largestPole`). -/
@[cited "Atiyah 1970 (CPAM 23:145-150) + Saito/SLT (paper propdefn L1804): local ∫K^s φ continues meromorphically, poles ℚ_{<0}, largest pole = -rlct_{x₀}"]
axiom cited_local_zeta_pole {n : ℕ} (K φ : (Fin n → ℝ) → ℝ)
    (x₀ : Fin n → ℝ) (U : Set (Fin n → ℝ))
    (hK : AnalyticOnNhd ℝ K Set.univ) (hKnn : ∀ x, 0 ≤ K x) (hKx₀ : K x₀ = 0)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφnn : ∀ x, 0 ≤ φ x) (hφx₀ : φ x₀ ≠ 0)
    -- `φ` is supported in a small open nbhd `U ∋ x₀` (localizes the cutoff; NO regional threshold);
    (hx₀U : x₀ ∈ U) (hUopen : IsOpen U) (hφU : tsupport φ ⊆ U)
    -- worst-point on `supp φ`: `x₀` has the smallest local RLCT over `tsupport φ`, so the pole `s₀`
    -- (a `supp φ`-quantity) equals `−rlctAt K x₀`. Admits the DLN fibre (equal-threshold zeros are OK);
    (hWorst : ∀ x ∈ tsupport φ, rlctAt K x₀ ≤ rlctAt K x) :
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
      -- and the BUNDLED LOCAL identification: the largest pole is minus the LOCAL RLCT at `x₀`.
      s₀ = -(rlctAt K x₀)

end RLCT
