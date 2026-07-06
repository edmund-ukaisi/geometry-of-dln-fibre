import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# `RLCT.Global` — the cite-free **global** RLCT `rlctGlobal K` (Def 8.1(i))

The **global** real log-canonical threshold of a loss germ `K : X → ℝ` on a real-analytic parameter
space `X` (here: any measure + topological space):

`rlctGlobal K := sSup { c ≥ 0 | K^(-c) is globally locally integrable }`,

where "globally locally integrable" is `∀ x, IntegrableAtFilter (K^(-c)) (𝓝 x)` — integrable on
*some* neighbourhood of *every* point. This is the paper's global `rlct(F)` (Def 8.1(i),
`main.tex` L1786–1791) verbatim: `sup { s | |F|^{-s} locally integrable }`. Cite-free.

**Polymorphic in the parameter space.** Unlike the local zeta theory (`RLCT.Local`/`RLCT.Zeta`/
`RLCT.Cited`, fixed to `Fin n → ℝ` for the archimedean-zeta continuation cite), the global RLCT is
stated over an arbitrary `{X} [MeasureSpace X] [TopologicalSpace X]`, so it applies directly to the
DLN loss `lossDLN d B : Rep_d → ℝ` — whose domain `Rep_d = Tuple d` is a product of matrix spaces,
not literally `Fin n → ℝ`. The negative power `negPow` and the local threshold `rlctAt` are
redefined polymorphically here (they intentionally mirror the `Fin n → ℝ` `RLCT.Basic`/`RLCT.Local`
versions, which stay tied to the zeta cite); `name = content` throughout.

## Why `sSup` of the global set, not `⨅ x, rlctAt K x`

The paper's Prop 8.3(iii) reads `rlct(F) = inf_{x ∈ X} rlct_x(F)`. That inf is over **all** of `X`,
but a *regular* point `x` (`F x ≠ 0`) contributes `rlct_x(F) = +∞` (Prop 8.3(i)), so the inf is
really over the **zero locus** `{F = 0}`. Our ℝ-valued `rlctAt` returns the **junk `0`** at a
regular point (its admissible set is unbounded — the honest `+∞` is out of the ℝ `sSup`'s scope),
so a bare `⨅ x, rlctAt K x` over *all* `x` would be identically `0` (the junk-0 trap). Defining
`rlctGlobal` directly by the paper's `sSup` sidesteps this: it is honest exactly when the global
admissible set is bounded above — the *pole* regime, i.e. `{K = 0} ≠ ∅` (Prop 8.3(i):
`rlct(F) < ∞ ⟺ F⁻¹(0) ≠ ∅`), which is the payoff germ (the DLN fibre is nonempty).

## What is proved here

* `rlctGlobal_le_rlctAt` — the **elementary `≤` half of Prop 8.3(iii)**: global local-integrability
  at the exponent `c` *is* local integrability at each point `x`, so `globalAdmissibleExponents K ⊆
  localAdmissibleExponents K x`; under `BddAbove (localAdmissibleExponents K x)` (the pole regime at
  `x`) this gives `rlctGlobal K ≤ rlctAt K x` (`csSup_le_csSup`). Unconditional in the germ.
* `rlctGlobal_le_sInf_zeroLocus` — the same `≤`, folded over the zero locus: `rlctGlobal K ≤
  sInf (rlctAt K '' {K = 0})` (the infimum of the local RLCT over the zeros). The `sInf`-over-image
  form avoids the junk-`0` a conditionally-complete `⨅ x ∈ s` would inject at non-members (ℝ has no
  `⊤`, so `⨅ _ : (x ∉ s)` collapses to `0`, not `+∞`).
* `rlctGlobal_eq_sInf_zeroLocus_of_glue` — the **full characterization as a clean conditional**
  (Prop 8.3(iii)): the reverse `≥` direction (every `c` below the zero-locus inf is globally
  admissible) is a **paracompactness/gluing lift** — the paper itself flags it (the inf "is not
  always attained… because of potential issues at infinity", attained e.g. for `X` compact or `X,F`
  algebraic). It is stated here with that gluing supplied as the explicit hypothesis `hGlue`, so the
  equality is a genuine (checked) theorem *modulo* the named analytic input, never a `sorry`.
  Proving `hGlue` for the algebraic DLN germ is a separate analytic build (roadmapped); the DLN
  payoff does NOT route through this characterization — it rides the two cited Watanabe/Aoyagi
  bounds stated directly on `rlctGlobal` (`DLNFibre.DLN.RLCT.AoyagiCited`).

Nested namespace `RLCT.Global` (network-free); its helper names mirror the `Fin n → ℝ` local zeta
theory (`RLCT.Basic`/`RLCT.Local`) without clashing.
-/

open MeasureTheory Set Filter Topology

-- Nested namespace `RLCT.Global` for the polymorphic global-RLCT machinery. The helper names
-- (`negPow`, `localAdmissibleExponents`, `rlctAt`) intentionally mirror the `Fin n → ℝ` local zeta
-- theory (`RLCT.negPow` in `RLCT.Basic`, `RLCT.rlctAt` in `RLCT.Local`); nesting under
-- `RLCT.Global` keeps both in one `import DLNFibre` environment without a name clash (the local
-- theory stays fixed to `Fin n → ℝ` for the archimedean-zeta continuation cite). The payoff object
-- is `RLCT.Global.rlctGlobal`.
namespace RLCT.Global

variable {X : Type*}

/-- The negative power `K^{-c}` of a loss germ `K : X → ℝ` (`Real.rpow`). Polymorphic mirror of the
`Fin n → ℝ` `RLCT.Basic.negPow`; the object whose local integrability defines the RLCT
thresholds. -/
noncomputable def negPow (K : X → ℝ) (c : ℝ) : X → ℝ :=
  fun x ↦ (K x) ^ (-c)

@[simp] lemma negPow_apply (K : X → ℝ) (c : ℝ) (x : X) : negPow K c x = (K x) ^ (-c) := rfl

/-- `K^0 = 1` everywhere. -/
@[simp] lemma negPow_zero (K : X → ℝ) : negPow K 0 = fun _ ↦ (1 : ℝ) := by
  funext x; simp [negPow]

variable [MeasureSpace X] [TopologicalSpace X]

/-- An exponent `c` is **locally admissible** for `K` at `x` when `c ≥ 0` and `K^(-c)` is integrable
on some neighbourhood of `x`. Polymorphic mirror of `RLCT.Local.localAdmissibleExponents`. -/
def localAdmissibleExponents (K : X → ℝ) (x : X) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x)}

lemma mem_localAdmissibleExponents {K : X → ℝ} {x : X} {c : ℝ} :
    c ∈ localAdmissibleExponents K x ↔ 0 ≤ c ∧ IntegrableAtFilter (negPow K c) (𝓝 x) := Iff.rfl

/-- The **local RLCT** `rlctAt K x`: the supremum of the locally-admissible exponents at `x` — the
paper's `rlct_x(K)` (Def 8.1(ii)). Cite-free. Honest in the pole regime (bounded admissible set);
`sSup ∅ = 0` / unbounded is the documented out-of-scope (regular points, honest value `+∞`). -/
noncomputable def rlctAt (K : X → ℝ) (x : X) : ℝ :=
  sSup (localAdmissibleExponents K x)

lemma rlctAt_def (K : X → ℝ) (x : X) : rlctAt K x = sSup (localAdmissibleExponents K x) := rfl

/-- An exponent `c` is **globally admissible** for `K` when `c ≥ 0` and `K^(-c)` is integrable on
*some* neighbourhood of *every* point (`∀ x, IntegrableAtFilter … (𝓝 x)`) — the paper's "locally
integrable" (everywhere) in Def 8.1(i). -/
def globalAdmissibleExponents (K : X → ℝ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∀ x, IntegrableAtFilter (negPow K c) (𝓝 x)}

lemma mem_globalAdmissibleExponents {K : X → ℝ} {c : ℝ} :
    c ∈ globalAdmissibleExponents K ↔ 0 ≤ c ∧ ∀ x, IntegrableAtFilter (negPow K c) (𝓝 x) := Iff.rfl

/-- The **global RLCT** `rlctGlobal K`: the supremum of the globally-admissible exponents — the
paper's `rlct(F)` (Def 8.1(i)). Cite-free. Honest in the pole regime (bounded admissible set, i.e.
`{K = 0} ≠ ∅`); `sSup ∅ = 0` / unbounded is the documented out-of-scope, as for `rlctAt`. -/
noncomputable def rlctGlobal (K : X → ℝ) : ℝ :=
  sSup (globalAdmissibleExponents K)

lemma rlctGlobal_def (K : X → ℝ) : rlctGlobal K = sSup (globalAdmissibleExponents K) := rfl

/-- `0` is globally admissible when the constant germ `1` is locally integrable at every point (a
small nbhd of each `x` has finite measure): `K^0 = 1`. Witness that the global admissible set is
nonempty, so `rlctGlobal K ≥ 0` in the pole regime. -/
lemma zero_mem_globalAdmissibleExponents {K : X → ℝ}
    (h : ∀ x : X, IntegrableAtFilter (fun _ ↦ (1 : ℝ)) (𝓝 x)) :
    (0 : ℝ) ∈ globalAdmissibleExponents K := by
  refine ⟨le_rfl, fun x ↦ ?_⟩
  simpa [negPow_zero] using h x

/-- **Global admissibility is local admissibility at every point.** A globally-admissible exponent
`c` is admissible at each individual point `x`: the global integrability `∀ y, IntegrableAtFilter …
(𝓝 y)` instantiates at `y = x`. Hence
`globalAdmissibleExponents K ⊆ localAdmissibleExponents K x`. -/
lemma globalAdmissibleExponents_subset_localAdmissibleExponents (K : X → ℝ) (x : X) :
    globalAdmissibleExponents K ⊆ localAdmissibleExponents K x := by
  rintro c ⟨hc0, hglob⟩
  exact ⟨hc0, hglob x⟩

/-- **The elementary `≤` half of Prop 8.3(iii): `rlctGlobal K ≤ rlctAt K x`.** Global
local-integrability at an exponent implies local integrability at `x`
(`globalAdmissibleExponents ⊆ localAdmissibleExponents K x`), so the global threshold is at most the
local threshold at every point `x`. The `BddAbove (localAdmissibleExponents K x)` hypothesis is the
pole-regime guard at `x` (`sSup` in ℝ is the honest local value only when bounded); the global set
is nonempty via `hne`. -/
lemma rlctGlobal_le_rlctAt {K : X → ℝ} (x : X)
    (hbdd : BddAbove (localAdmissibleExponents K x))
    (hne : (globalAdmissibleExponents K).Nonempty) :
    rlctGlobal K ≤ rlctAt K x :=
  csSup_le_csSup hbdd hne (globalAdmissibleExponents_subset_localAdmissibleExponents K x)

/-- **The `≤` half folded over the zero locus:** `rlctGlobal K ≤ sInf (rlctAt K '' {K = 0})`. Each
zero `x` gives `rlctGlobal K ≤ rlctAt K x` (`rlctGlobal_le_rlctAt`), so the global threshold is a
lower bound of the image family, hence `≤` its infimum (`le_csInf`). Requires the zero locus
nonempty (`hzero`, the pole regime — where the infimum is honest), the local pole-regime bound at
every zero (`hbdd`), and the global-set nonemptiness (`hne`). -/
lemma rlctGlobal_le_sInf_zeroLocus {K : X → ℝ}
    (hzero : {x : X | K x = 0}.Nonempty)
    (hbdd : ∀ x, K x = 0 → BddAbove (localAdmissibleExponents K x))
    (hne : (globalAdmissibleExponents K).Nonempty) :
    rlctGlobal K ≤ sInf (rlctAt K '' {x : X | K x = 0}) := by
  refine le_csInf (hzero.image _) ?_
  rintro b ⟨x, hx, rfl⟩
  exact rlctGlobal_le_rlctAt x (hbdd x hx) hne

/-- **Prop 8.3(iii), the full characterization — a clean conditional.** The global RLCT equals the
infimum of the local RLCT over the **zero locus** `{K = 0}` (never all of `X`; regular points carry
the honest `+∞`, junk-`0` here). The elementary `≤` is `rlctGlobal_le_sInf_zeroLocus`. The reverse
`≥` — that every exponent below the zero-locus infimum is globally admissible — is a
**paracompactness/gluing lift**: local integrability holds near each zero (below the local threshold
there) and near each regular point (`K` continuous, nonzero ⟹ `K^{-c}` continuous ⟹ loc-integrable),
and these local pieces glue to global local-integrability. The paper flags this: the inf "is not
always attained … because of potential issues at infinity", but is attained for `X` compact or
`X, F` algebraic (Prop 8.3(iii)). The gluing is supplied as the explicit hypothesis `hGlue`; the
equality is then a genuine theorem modulo that named analytic input. Proving `hGlue` for the
algebraic DLN germ is a separate build (roadmapped); the payoff does NOT use this
characterization. -/
theorem rlctGlobal_eq_sInf_zeroLocus_of_glue {K : X → ℝ}
    (hzero : {x : X | K x = 0}.Nonempty)
    (hbdd : ∀ x, K x = 0 → BddAbove (localAdmissibleExponents K x))
    (hne : (globalAdmissibleExponents K).Nonempty)
    (hGlue : sInf (rlctAt K '' {x : X | K x = 0}) ≤ rlctGlobal K) :
    rlctGlobal K = sInf (rlctAt K '' {x : X | K x = 0}) :=
  le_antisymm (rlctGlobal_le_sInf_zeroLocus hzero hbdd hne) hGlue

end RLCT.Global
