import DLNFibre.Core.Analysis.RLCT.Pair
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Constructions

/-!
# `RLCT.Witness` — an instantiability witness for the local zeta-pole cite

A concrete `RLCT.ZetaSetup 1` discharging **every** hypothesis of the LOCAL zeta-pole cite
(`RLCT.cited_local_zeta_pole`, via `ZetaSetup.cite`) at a genuine singular germ. This makes
**non-vacuity a build-time fact**: the hypotheses of the cite are jointly satisfiable at a real
germ, so the cite is not silently empty (the round-7 defect — a hypothesis set unsatisfiable at
every genuine germ passes the cordon green yet never fires). The cordon philosophy applied to
*hypotheses*, not just axioms (citation-cordon policy, "check both ends").

The germ is `K = fun x ↦ (x 0)^2` on `Fin 1 → ℝ` (a genuine analytic nonnegative germ with a single
zero at `x₀ = 0`), the cutoff a `ContDiffBump 0` (smooth, compact support, `= 1` on a ball, so
`≥ 0` and `≠ 0` at `0`), and `U = Set.univ`. The load-bearing discharges:

* **`hKne`** — `K (fun _ ↦ 1) = 1 ≠ 0` (the round-7 non-triviality guard is met);
* **`hWorst`** (zero-guarded) — the *only* zero of `K` is `0 = x₀`, so `K x = 0 → x = x₀`, and the
  inequality is then `rlctAt K x₀ ≤ rlctAt K x₀` by `le_refl` — **no `rlctAt` value computed** (the
  guard makes the worst-point hypothesis trivially dischargeable at a single-zero germ);
* **`hK`** — `(x 0)^2` is analytic: the coordinate projection `ContinuousLinearMap.proj 0` is
  analytic (a continuous linear map, `CPolynomial`), squared via `AnalyticOnNhd.pow`.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Topology

namespace RLCT

/-- The witness germ `K = fun x ↦ (x 0)^2` on `Fin 1 → ℝ`: analytic, nonneg, single zero at `0`. -/
noncomputable def sqGerm : (Fin 1 → ℝ) → ℝ := fun x ↦ (x 0) ^ 2

@[simp] lemma sqGerm_apply (x : Fin 1 → ℝ) : sqGerm x = (x 0) ^ 2 := rfl

/-- The witness germ is real-analytic: `x ↦ x 0` is the continuous-linear coordinate projection
(hence analytic), and `sqGerm = (· 0)^2` is its square. -/
lemma analyticOnNhd_sqGerm : AnalyticOnNhd ℝ sqGerm Set.univ := by
  have hproj : AnalyticOnNhd ℝ (fun x : Fin 1 → ℝ ↦ x 0) Set.univ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0).analyticOnNhd Set.univ
  simpa [sqGerm] using hproj.pow 2

/-- The only zero of `sqGerm` is `x₀ = 0`: `(x 0)^2 = 0 ↔ x 0 = 0 ↔ x = 0` (on `Fin 1 → ℝ`). -/
lemma sqGerm_eq_zero_iff {x : Fin 1 → ℝ} : sqGerm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx0 : x 0 = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      simpa [sqGerm] using this
    funext i; fin_cases i; simpa using hx0
  · rintro rfl; simp [sqGerm]

/-- The witness cutoff: a `ContDiffBump` centred at `0` with radii `1 < 2`. Smooth, compactly
supported, nonnegative, and `= 1` on the closed unit ball (so nonzero at `0`). -/
noncomputable def sqBump : ContDiffBump (0 : Fin 1 → ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The **instantiability witness** `zetaSetupSq : ZetaSetup 1` — a concrete germ + cutoff at the
genuine singular germ `K = (x 0)^2`, discharging every hypothesis of the local zeta-pole cite. Its
mere existence (elaboration) proves the cite's hypotheses are jointly satisfiable at a real germ:
non-vacuity is now a build-time fact. -/
noncomputable def zetaSetupSq : ZetaSetup 1 where
  K := sqGerm
  φ := (sqBump : (Fin 1 → ℝ) → ℝ)
  x₀ := 0
  U := Set.univ
  hK := analyticOnNhd_sqGerm
  hKnn := fun x ↦ by simp only [sqGerm]; positivity
  hKx₀ := by simp [sqGerm]
  hKne := ⟨fun _ ↦ 1, by simp [sqGerm]⟩
  hφ := sqBump.contDiff
  hφc := sqBump.hasCompactSupport
  hφnn := fun x ↦ sqBump.nonneg
  hφx₀ := by
    -- `sqBump 0 = 1 ≠ 0` (center is in the closed `rIn`-ball).
    have : (sqBump : (Fin 1 → ℝ) → ℝ) 0 = 1 :=
      sqBump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, sqBump])
    rw [this]; norm_num
  hx₀U := Set.mem_univ _
  hUopen := isOpen_univ
  hφU := Set.subset_univ _
  hWorst := by
    -- The only zero of `sqGerm` is `0 = x₀`; the guard `K x = 0` forces `x = 0`, so the inequality
    -- is `rlctAt sqGerm 0 ≤ rlctAt sqGerm 0` — `le_refl`, no `rlctAt` value needed.
    intro x _ hKx
    rw [sqGerm_eq_zero_iff] at hKx
    subst hKx
    exact le_refl _

end RLCT
