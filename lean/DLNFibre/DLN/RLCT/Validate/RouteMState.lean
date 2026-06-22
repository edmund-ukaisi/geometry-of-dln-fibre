import DLNFibre.DLN.RLCT.Skeleton
import Mathlib.Data.Prod.Lex

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMState` — the Route M recursion carrier + measure + leaf datum (fm3)

The complete FOUNDATION for the Route M dispatcher (`RouteMTree.lean`): the node state `RouteState`,
the well-founded termination measure `lex(L, ΣM, ncDefect)`, the per-leaf monomial datum `MonoData`,
and the leaf (unit) datum + its `monomialThreshold = ⊤` fact. Split out from the dispatcher so this
committable bedrock banks independently of the (in-progress) `classify`/cover-fact bodies. Fully
proven (no proof gaps); rests on `monomial_rlct` (the S2 cited threshold axiom) only.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- A node state: the chain depth `L` and the widths `M`. The recursion's carrier. -/
structure RouteState where
  L : ℕ
  M : Fin (L + 1) → ℕ

/-- `ΣM`, the total width (the second lex component; drops at a C1 node). -/
def RouteState.widthSum (S : RouteState) : ℕ := ∑ i, S.M i

/-- The normal-crossing defect (the third lex component; drops at a C3 NC-completion pass). The number
of non-normal-crossing exceptional intersections; pinned at `0` here (refined per-leaf by C3). -/
def RouteState.ncDefect (_S : RouteState) : ℕ := 0

/-- The termination measure: `lex(L, ΣM, ncDefect)` on `ℕ³` (well-founded). -/
abbrev RouteMeasure := ℕ ×ₗ ℕ ×ₗ ℕ

/-- The lex measure of a state. -/
def routeMeasure (S : RouteState) : RouteMeasure :=
  toLex (S.L, toLex (S.widthSum, S.ncDefect))

/-- The recursion's well-founded relation: strictly-smaller lex measure. -/
def routeRel (S T : RouteState) : Prop := routeMeasure S < routeMeasure T

/-- `routeRel` is well-founded (pullback of `<` on `ℕ³ₗ` along `routeMeasure`). -/
theorem routeRel_wf : WellFounded routeRel :=
  InvImage.wf routeMeasure wellFounded_lt

/-- The per-leaf monomial datum: dimension `d` + the `(k, h)` exponents for `monomialThreshold`. -/
structure MonoData where
  d : ℕ
  k : Fin d → ℕ
  h : Fin d → ℕ

/-- **The leaf (unit) datum.** At a leaf (`L=1` / rank-0 core, `F = ‖C₁‖²` already a unit after all
singular directions are blown up), the chart carries NO monomial: `k = h = 0` over the `d` ambient
coordinates (the (d,k,h)-accumulation BASE; each blow-up node SETS its pivot axis to `(1, card−1)`
outward). NOT a smooth block `d/2` — that is the off-path additive squeeze; the `d/2`-type RLCT rides
the accumulated pivot `(k,h)` via `⨅ axisRatio`. -/
def leafMonoData (d : ℕ) : MonoData := ⟨d, fun _ => 0, fun _ => 0⟩

/-- **The leaf threshold is `⊤`.** A unit leaf (`k ≡ 0`) imposes no monomial threshold:
`monomialThreshold d 0 h = ⨅ⱼ axisRatio (h j) 0 = ⨅ⱼ ⊤ = ⊤` (every axis is a spectator, `axisRatio _ 0
= ⊤`). So the leaf NEVER binds the cover `⨅` — the RLCT comes entirely from the accumulated pivot
divisors above it. (Rests on `monomial_rlct`, the S2 cited threshold axiom.) -/
theorem leafMonoData_threshold (d : ℕ) :
    monomialThreshold (leafMonoData d).d (leafMonoData d).k (leafMonoData d).h = ⊤ := by
  rw [(monomial_rlct (leafMonoData d).d (leafMonoData d).k (leafMonoData d).h).1]
  simp only [leafMonoData]
  exact le_antisymm le_top (le_iInf (fun j => by rw [axisRatio]; simp))

/-! ## Per-node `(d,k,h)` accumulation — appending a pivot divisor (fork-independent value bedrock)

A C1/C5 blow-up node ADDS one exceptional divisor to the accumulated chart datum: a fresh axis with
`(k, h) = (1, card−1)` (the codim-`card` pivot stratum, `axisRatio = card/2`). On `MonoData` this is
`appendDivisor` (snoc the new axis at the end). Its effect on the chart threshold is the `⨅`/`min`
update `monomialThreshold (append) = min (card/2) (monomialThreshold old)` — the binding `⨅` takes
the min with the new axis's ratio. Pure threshold combinatorics (via `monomial_rlct.1`), INDEPENDENT
of how the recursion accumulates: the leaf-data semantics every division (A/B/C) shares. -/

/-- `⨅` over `Fin (d+1)` splits as `min` of the last coordinate and the `⨅` over the `castSucc`
prefix. Generic `ℝ≥0∞` fact (`le_antisymm` + `Fin.lastCases`, no named Mathlib `Fin`-iInf lemma). -/
theorem iInf_fin_succ_eq_min_last {d : ℕ} (f : Fin (d + 1) → ℝ≥0∞) :
    (⨅ j : Fin (d + 1), f j) = min (f (Fin.last d)) (⨅ j : Fin d, f j.castSucc) := by
  apply le_antisymm
  · exact le_min (iInf_le _ (Fin.last d)) (le_iInf fun j => iInf_le _ j.castSucc)
  · refine le_iInf fun j => ?_
    refine Fin.lastCases ?_ ?_ j
    · exact min_le_left _ _
    · exact fun i => le_trans (min_le_right _ _) (iInf_le _ i)

/-- Append a pivot divisor `(k,h) = (1, c−1)` (the codim-`c` exceptional axis) to a `MonoData`. -/
def MonoData.appendDivisor (md : MonoData) (c : ℕ) : MonoData :=
  ⟨md.d + 1, Fin.snoc md.k 1, Fin.snoc md.h (c - 1)⟩

/-- **Per-node threshold update (the value-side accumulation step).** Appending a codim-`c` pivot
divisor `(1, c−1)` takes the chart threshold to the `min` of its old value and the new axis's ratio
`c/2`: `monomialThreshold (md.appendDivisor c) = min (c/2) (monomialThreshold md)` (`1 ≤ c`). The
`⨅ axisRatio` over the snoc'd family splits (via `iInf_fin_succ_eq_min_last`) into the last axis
(`axisRatio (c−1) 1 = c/2`, `axisRatio_regularSeq`) and the prefix (the old `⨅`). The `min`-fold is
how the binding minimal-codim divisor controls the cover `⨅` (`achiever` / `threshold_ge`). Rests on
`monomial_rlct` (S2). -/
theorem monomialThreshold_appendDivisor (md : MonoData) (c : ℕ) (hc : 1 ≤ c) :
    monomialThreshold (md.appendDivisor c).d (md.appendDivisor c).k (md.appendDivisor c).h
      = min ((c : ℝ≥0∞) / 2) (monomialThreshold md.d md.k md.h) := by
  rw [(monomial_rlct (md.appendDivisor c).d (md.appendDivisor c).k (md.appendDivisor c).h).1,
    (monomial_rlct md.d md.k md.h).1]
  simp only [MonoData.appendDivisor]
  rw [iInf_fin_succ_eq_min_last]
  congr 1
  · rw [Fin.snoc_last, Fin.snoc_last, axisRatio_regularSeq c hc]
  · exact iInf_congr fun j => by rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- **(C≥ step) Appending a codim-`≥m₀` divisor preserves the `≥ m₀/2` lower bound.** If a chart's
threshold is `≥ m₀/2` and the next pivot divisor has codim `c ≥ m₀` (`1 ≤ m₀`), the updated threshold
is still `≥ m₀/2` (the new axis's ratio `c/2 ≥ m₀/2` does not lower the `min`). This is the inductive
step of `IsResolutionAtlas.threshold_ge` along any append-fold — fork-independent. -/
theorem monomialThreshold_appendDivisor_ge (md : MonoData) (c m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hcm : m₀ ≤ c)
    (hge : (m₀ : ℝ≥0∞) / 2 ≤ monomialThreshold md.d md.k md.h) :
    (m₀ : ℝ≥0∞) / 2
      ≤ monomialThreshold (md.appendDivisor c).d (md.appendDivisor c).k (md.appendDivisor c).h := by
  rw [monomialThreshold_appendDivisor md c (le_trans hm₀ hcm)]
  refine le_min ?_ hge
  exact ENNReal.div_le_div_right (by exact_mod_cast hcm) 2

/-- **(C=∃ seed) The binding codim-`m₀` divisor caps the threshold at `m₀/2`.** Appending a divisor of
codim exactly `m₀` (`1 ≤ m₀`) makes the chart threshold `≤ m₀/2` (the new axis binds the `min`). This
is the achiever's upper bound: on the minimising path, the binding divisor realises `½·m₀`. With the
matching `≥` (from `monomialThreshold_appendDivisor_ge` down to a `⊤` leaf), `le_antisymm` gives the
exact `= m₀/2`. Fork-independent. -/
theorem monomialThreshold_appendDivisor_le_binding (md : MonoData) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    monomialThreshold (md.appendDivisor m₀).d (md.appendDivisor m₀).k (md.appendDivisor m₀).h
      ≤ (m₀ : ℝ≥0∞) / 2 := by
  rw [monomialThreshold_appendDivisor md m₀ hm₀]
  exact min_le_left _ _

/-! ## A leaf's accumulated datum — folding the pivot divisors along one path

A single chart (one leaf of the resolution tree) accumulates the codim-`c` pivot divisors along its
reduction PATH. `foldDivisors cs` appends them over the codim list `cs` onto the empty `d=0` base
(threshold `⊤`). This is the per-leaf value, fork-independent: a leaf's `(d,k,h)` is its path's appends,
however the branching is organised. The threshold of the fold is the `min` over `cs` of the ratios
`c/2`, so a path whose binding (minimal-codim) divisor is `m₀` has threshold exactly `½·m₀`. -/

/-- A leaf's `MonoData`: fold `appendDivisor` over the codim list `cs`, base the empty `d=0` datum. -/
def MonoData.foldDivisors (cs : List ℕ) : MonoData :=
  cs.foldr (fun c md => md.appendDivisor c) (leafMonoData 0)

/-- The `ℝ≥0∞` min-fold of the divisor ratios `c/2` over a codim list. -/
noncomputable def ratioMinFold (cs : List ℕ) : ℝ≥0∞ :=
  cs.foldr (fun c acc => min ((c : ℝ≥0∞) / 2) acc) ⊤

@[simp] theorem ratioMinFold_nil : ratioMinFold [] = ⊤ := rfl

@[simp] theorem ratioMinFold_cons (c : ℕ) (cs : List ℕ) :
    ratioMinFold (c :: cs) = min ((c : ℝ≥0∞) / 2) (ratioMinFold cs) := rfl

/-- **The leaf threshold is the `min`-fold of the path's divisor ratios.** For a codim list `cs` of
positive codims, `monomialThreshold (foldDivisors cs) = ratioMinFold cs` — the binding (minimal-codim)
divisor on the path controls it (empty list ⟹ `⊤`). The achiever value for one path, closed form. -/
theorem monomialThreshold_foldDivisors (cs : List ℕ) (hpos : ∀ c ∈ cs, 1 ≤ c) :
    monomialThreshold (MonoData.foldDivisors cs).d (MonoData.foldDivisors cs).k
        (MonoData.foldDivisors cs).h
      = ratioMinFold cs := by
  induction cs with
  | nil => simpa [MonoData.foldDivisors, ratioMinFold] using leafMonoData_threshold 0
  | cons c cs ih =>
      have hc : 1 ≤ c := hpos c List.mem_cons_self
      have ihp : ∀ c' ∈ cs, 1 ≤ c' := fun c' hc' => hpos c' (List.mem_cons_of_mem c hc')
      have hstep : MonoData.foldDivisors (c :: cs) = (MonoData.foldDivisors cs).appendDivisor c := rfl
      rw [hstep, monomialThreshold_appendDivisor _ c hc, ih ihp, ratioMinFold_cons]

/-- The `ratioMinFold` is `≤ m₀/2` when the binding codim `m₀` appears in the list. -/
theorem ratioMinFold_le_of_mem (cs : List ℕ) (m₀ : ℕ) (hbind : m₀ ∈ cs) :
    ratioMinFold cs ≤ (m₀ : ℝ≥0∞) / 2 := by
  induction cs with
  | nil => exact absurd hbind List.not_mem_nil
  | cons c cs ih =>
      rw [ratioMinFold_cons]
      rcases List.mem_cons.1 hbind with hceq | hmem
      · exact hceq ▸ min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih hmem)

/-- The `ratioMinFold` is `≥ m₀/2` when every codim in the list is `≥ m₀`. -/
theorem ratioMinFold_ge_of_all_ge (cs : List ℕ) (m₀ : ℕ) (hge : ∀ c ∈ cs, m₀ ≤ c) :
    (m₀ : ℝ≥0∞) / 2 ≤ ratioMinFold cs := by
  induction cs with
  | nil => exact le_top
  | cons c cs ih =>
      rw [ratioMinFold_cons]
      refine le_min ?_ (ih fun c' hc' => hge c' (List.mem_cons_of_mem c hc'))
      exact ENNReal.div_le_div_right (by exact_mod_cast hge c List.mem_cons_self) 2

/-- **(C=∃, one path) A path whose binding divisor is the minimum `m₀` realises threshold `= ½·m₀`.**
If every codim on the path is `≥ m₀` and `m₀` itself appears (`1 ≤ m₀`), the leaf threshold is exactly
`m₀/2` — the achiever value (pp2 g148). `le_antisymm` of `ratioMinFold`'s two bounds. -/
theorem monomialThreshold_foldDivisors_eq_of_binding (cs : List ℕ) (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hge : ∀ c ∈ cs, m₀ ≤ c) (hbind : m₀ ∈ cs) :
    monomialThreshold (MonoData.foldDivisors cs).d (MonoData.foldDivisors cs).k
        (MonoData.foldDivisors cs).h
      = (m₀ : ℝ≥0∞) / 2 := by
  rw [monomialThreshold_foldDivisors cs (fun c hc => le_trans hm₀ (hge c hc))]
  exact le_antisymm (ratioMinFold_le_of_mem cs m₀ hbind) (ratioMinFold_ge_of_all_ge cs m₀ hge)

/-- **(C≥, one path) Every path whose divisors are all codim-`≥m₀` has threshold `≥ ½·m₀`.** The
no-undershoot lower bound for `IsResolutionAtlas.threshold_ge`: a non-minimising path (binding codim
`> m₀`) still stays `≥ ½·m₀`. `monomialThreshold_foldDivisors` + `ratioMinFold_ge_of_all_ge`. The
companion to `_eq_of_binding`: the achiever path hits `= ½·m₀`, every other path is `≥`. -/
theorem monomialThreshold_foldDivisors_ge (cs : List ℕ) (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hge : ∀ c ∈ cs, m₀ ≤ c) :
    (m₀ : ℝ≥0∞) / 2
      ≤ monomialThreshold (MonoData.foldDivisors cs).d (MonoData.foldDivisors cs).k
          (MonoData.foldDivisors cs).h := by
  rw [monomialThreshold_foldDivisors cs (fun c hc => le_trans hm₀ (hge c hc))]
  exact ratioMinFold_ge_of_all_ge cs m₀ hge

/-! ## The value-side ⟹ IsResolutionAtlas consistency bridge (the pp2-dispatcher contract, fork-indep)

The contract pp2's #68 dispatcher must satisfy so its leaf monomials AGREE with this value-side, yielding
crux2's `IsResolutionAtlas` (`threshold_ge` C≥ + `achiever` C=∃) over `m₀ = (Adm M).inf' Mval`:
- every leaf path `i`'s codim-list `codimsOf i` has all codims `≥ m₀` (⟹ `threshold_ge`);
- the minimising path `i₀` has `m₀ ∈ codimsOf i₀` (⟹ `achiever`).
Stated over an abstract leaf family `(ι, codimsOf)` so it is independent of the `IsResolutionAtlas` Lean
structure version (my branch carries the stale `stratum`/`threshold_eq` form; crux2's `route-m-atlas` has
the `threshold_ge`/`achiever` form). The two outputs below ARE crux2's two atlas fields, branch-agnostic. -/

/-- **(C≥) family-level threshold_ge.** If every leaf `i`'s codim-list has all codims `≥ m₀` (`1 ≤ m₀`),
every leaf's `foldDivisors` threshold is `≥ ½·m₀`. The `IsResolutionAtlas.threshold_ge` fact, over a leaf
family. (Lifts `monomialThreshold_foldDivisors_ge` over the index.) -/
theorem foldFamily_threshold_ge {ι : Type*} (codimsOf : ι → List ℕ) (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hge : ∀ i, ∀ c ∈ codimsOf i, m₀ ≤ c) (i : ι) :
    (m₀ : ℝ≥0∞) / 2
      ≤ monomialThreshold (MonoData.foldDivisors (codimsOf i)).d
          (MonoData.foldDivisors (codimsOf i)).k (MonoData.foldDivisors (codimsOf i)).h :=
  monomialThreshold_foldDivisors_ge (codimsOf i) m₀ hm₀ (hge i)

/-- **(C=∃) family-level achiever.** If the minimising leaf `i₀`'s codim-list has all codims `≥ m₀` and
contains `m₀` (`1 ≤ m₀`), `i₀`'s `foldDivisors` threshold is `= ½·m₀`. The `IsResolutionAtlas.achiever`
fact. (Specialises `monomialThreshold_foldDivisors_eq_of_binding` at the minimiser.) -/
theorem foldFamily_achiever {ι : Type*} (codimsOf : ι → List ℕ) (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (i₀ : ι) (hge₀ : ∀ c ∈ codimsOf i₀, m₀ ≤ c) (hbind₀ : m₀ ∈ codimsOf i₀) :
    ∃ i : ι, monomialThreshold (MonoData.foldDivisors (codimsOf i)).d
        (MonoData.foldDivisors (codimsOf i)).k (MonoData.foldDivisors (codimsOf i)).h
      = (m₀ : ℝ≥0∞) / 2 :=
  ⟨i₀, monomialThreshold_foldDivisors_eq_of_binding (codimsOf i₀) m₀ hm₀ hge₀ hbind₀⟩

/-! ## The §2 codim-witness ⟹ no-undershoot bridge (pp2 g183, the load-bearing C1-condition)

pp2's #68 cert §2 (decorrelated-Codex-confirmed): the SINGLE seam making the dispatcher CERTIFIED vs
green-but-wrong is that every pivot divisor's `codim = Mval M T` for an ADMISSIBLE rank-pattern `T`
(NOT the raw coordinate cardinality / Jacobian rank — the `(4,3,2)` thin-product trap). Given that
witness, the no-undershoot `m₀ ≤ codim` is AUTOMATIC: `m₀ = (Adm M).inf' Mval` is the min over `Adm M`,
so `inf' Mval ≤ Mval M T` for any `T ∈ Adm M` (`Finset.inf'_le`). This lemma names that discharge — the
admissible-`T` witness mechanically feeds `foldFamily_threshold_ge`'s `m₀ ≤ c` hypothesis. -/

/-- **The admissible-`T` witness discharges no-undershoot.** For `T ∈ Adm M`, the minimal codim
`m₀ = ((Adm M).inf' Mval).toNat` is `≤ (Mval M T).toNat`. So a pivot divisor certified as `codim =
Mval M T` (`T` admissible) automatically satisfies `m₀ ≤ codim` — the C≥ per-divisor guarantee (pp2
§2). `Mval ≥ 0` on `Adm` (`Mval_nonneg_adm`-style; here via the `inf'`-nonneg round-trip). -/
theorem minAdm_le_Mval_toNat (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    (((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat) ≤ (Mval M T).toNat := by
  have hle : (Adm M).inf' (Adm_nonempty M) (Mval M) ≤ Mval M T := Finset.inf'_le _ hT
  exact Int.toNat_le_toNat hle

/-- **§2 ⟹ C≥ family-level**: if every leaf's codim-list comes from admissible-`T` witnesses (each
`c = (Mval M T).toNat`, `T ∈ Adm M`), every leaf threshold is `≥ ½·m₀` (`m₀ = minAdm`). Composes the
witness discharge (`minAdm_le_Mval_toNat`) with `foldFamily_threshold_ge` — the pp2 §2 certificate's C≥
consequence, value-side. The hypothesis is exactly what pp2's `witness : {T // Adm M T ∧ codim = Mval}`
field delivers. -/
theorem foldFamily_threshold_ge_of_admWitness {ι : Type*} (M : Fin (L + 1) → ℕ)
    (codimsOf : ι → List ℕ) (hm₀ : 1 ≤ ((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat)
    (hwit : ∀ i, ∀ c ∈ codimsOf i, ∃ T ∈ Adm M, c = (Mval M T).toNat) (i : ι) :
    ((((Adm M).inf' (Adm_nonempty M) (Mval M)).toNat : ℝ≥0∞)) / 2
      ≤ monomialThreshold (MonoData.foldDivisors (codimsOf i)).d
          (MonoData.foldDivisors (codimsOf i)).k (MonoData.foldDivisors (codimsOf i)).h := by
  refine foldFamily_threshold_ge codimsOf _ hm₀ (fun i' c hc => ?_) i
  obtain ⟨T, hT, hcT⟩ := hwit i' c hc
  rw [hcT]; exact minAdm_le_Mval_toNat M T hT

end DLNFibre.DLN.RLCT
