import DLNFibre.DLN.Aoyagi.RecursionAdapter

/-!
# `DLN.Aoyagi.Corank2Realize334` — RUNG 5a: discharging `AtlasRealizesExponents` for (3,3,4)

The seam `AtlasRealizesExponents d res` (`RecursionAdapter`) is the GEOMETRIC obligation of
`exists_coreResolution`: (i) every chart binding-axis exponent `jac a + 1` is a terminal exponent of
the Engine's built tree; (ii) the tree's `minAdm`-attaining leaf divisor is matched by a chart
binding axis. This module discharges it for the concrete (3,3,4) `t=(1,0)` atlas whose
Jacobian/ideal data were built in rungs 5b (`Corank2ChartJac`: `jac = [E:7, α:3, c11:8]`) and part-C
(`Corank2CoreGenWrap`: dominant monomial `⟨c11·E⟩`, so `bindingAxes = {E, c11}`).

**The tree side (the real content).** `terminalExponents (buildTree ![3,3,4] …)` is the
value-support `{(Mval ![3,3,4] a).toNat : a realized}`, all `≥ minAdm = 8`
(`minAdm_le_terminalExponents`). The
binding-axis values are `{E : 8, c11 : 9}`. `8 = minAdm` is banked (`o5_core_realized`). `9` is NOT
banked (it is not the minimizer) — it is the c11-axis value the controller flagged (the fan/orbit
worry). It is discharged directly: `clearableAdm_mval_mem_terminalExponents` runs the banked descent
invariant `realize_aux` on the CLEARABLE ADMISSIBLE profile `(2,0)` (`Mval = 9`), reading `9` off
its realized leaf — sorry-free, WITHOUT the retired R7 fossil. So `{8, 9} ⊆ terminalExponents` and
the fan/orbit worry dissolves: `9` is genuinely a terminal exponent (the `(2,0)`-profile leaf), not
an over-count.

**The chart side (the wiring).** `atlasRealizesExponents_334` is the reduction: given a resolution
whose charts all carry binding axes `{aE, aC}` with `jac aE = 7`, `jac aC = 8` (the 5b/part-C data),
the seam follows from `{8,9} ⊆ terminalExponents`. It is stated over a generic ambient dimension `D`
and axis pair `(aE, aC)` so the rung-5d assembly can supply the concrete (3,3,4) chart (with
`aE = ⟨0,_⟩` the `E`-axis, `aC = ⟨20,_⟩` the `c11`-axis) and apply it.

The general bridge `clearableAdm_mval_mem_terminalExponents` is reusable engine-grade: every
clearable admissible profile's `Mval` is a terminal exponent — the value-consequence of R7's `⊇`
direction for a SINGLE profile, which `realize_aux` proves sorry-free. General-`d` 5a consumes it.
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

/-- `Clearable` is decidable (a bounded `∀` over `Fin L` with a decidable body) — enables `decide`
on concrete width/profile instances. -/
instance {L : ℕ} (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) : Decidable (Clearable M a) := by
  unfold Clearable; infer_instance

/-! ## The reusable tree-side bridge -/

/-- **Every clearable admissible profile's `Mval` is a terminal exponent.** Runs the banked descent
invariant `realize_aux` (cert §4, sorry-free) on `a` from the root — `a` is realized as an analytic
`t̃ = 0` leaf divisor profile — then reads `(Mval M a).toNat = l.divExp k` off that leaf via
`isFullMonomialization_buildTree_conRoot`. The value-consequence of R7's `⊇` direction for a single
profile; needs positive widths (achievability is false at a zero width — see `tStar_realized`) but
NOT the retired R7 set-equality fossil. -/
theorem clearableAdm_mval_mem_terminalExponents {L : ℕ} (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hMpos : ∀ i, 0 < M i) (a : Fin L → ℕ) (ha : a ∈ Adm M) (hc : Clearable M a) :
    (Mval M a).toNat ∈
      ResolutionTree.terminalExponents (buildTree M (conOracle M) (conRoot : ConState L)) := by
  obtain ⟨l, hl, k, hk⟩ := realize_aux M a ha hc hMpos conRoot (SteerInv_conRoot M a hL)
  have hexp : l.divExp k = (Mval M (l.divProfile k)).toNat :=
    ((isFullMonomialization_buildTree_conRoot M hL l hl).1 k).1
  rw [ResolutionTree.terminalExponents]
  refine List.mem_flatMap.mpr ⟨l, hl, ?_⟩
  refine List.mem_append.mpr (Or.inl ?_)
  refine List.mem_map.mpr ⟨k, List.mem_finRange k, ?_⟩
  rw [hexp, hk]

/-! ## The (3,3,4) instances: `{8, 9} ⊆ terminalExponents` -/

/-- `Mval ![3,3,4] (1,0) = 8 = minAdm` (the E-axis value, the running-min minimizer). -/
example : (Mval (![3,3,4] : Fin 3 → ℕ) (![1,0] : Fin 2 → ℕ)).toNat = 8 := by decide

/-- `Mval ![3,3,4] (2,0) = 9` (the c11-axis value; NOT the minimizer — the fan/orbit exponent). -/
example : (Mval (![3,3,4] : Fin 3 → ℕ) (![2,0] : Fin 2 → ℕ)).toNat = 9 := by decide

/-- **`8 ∈ terminalExponents (buildTree ![3,3,4] …)`** — the E-axis / `minAdm` value, via the
realized running-min minimizer profile `(1,0)`. -/
theorem mem_terminalExponents_334_eight :
    (8 : ℕ) ∈ ResolutionTree.terminalExponents
      (buildTree (![3,3,4] : Fin 3 → ℕ) (conOracle (![3,3,4] : Fin 3 → ℕ))
        (conRoot : ConState 2)) := by
  have h := clearableAdm_mval_mem_terminalExponents (![3,3,4] : Fin 3 → ℕ) (by norm_num) (by decide)
    (![1,0] : Fin 2 → ℕ) (by decide) (by decide)
  rwa [show (Mval (![3,3,4] : Fin 3 → ℕ) (![1,0] : Fin 2 → ℕ)).toNat = 8 from by decide] at h

/-- **`9 ∈ terminalExponents (buildTree ![3,3,4] …)`** — the c11-axis value, via the realized
clearable admissible profile `(2,0)`. This is the flagged fan/orbit exponent: NOT the minimizer, so
`o5_core` does not deliver it — the direct `realize_aux` on `(2,0)` does, sorry-free. -/
theorem mem_terminalExponents_334_nine :
    (9 : ℕ) ∈ ResolutionTree.terminalExponents
      (buildTree (![3,3,4] : Fin 3 → ℕ) (conOracle (![3,3,4] : Fin 3 → ℕ))
        (conRoot : ConState 2)) := by
  have h := clearableAdm_mval_mem_terminalExponents (![3,3,4] : Fin 3 → ℕ) (by norm_num) (by decide)
    (![2,0] : Fin 2 → ℕ) (by decide) (by decide)
  rwa [show (Mval (![3,3,4] : Fin 3 → ℕ) (![2,0] : Fin 2 → ℕ)).toNat = 9 from by decide] at h

/-! ## The reduction: chart data ⟹ `AtlasRealizesExponents ![3,3,4]` -/

/-- **RUNG 5a — the (3,3,4) realization seam, discharged.** Given a resolution `res` of `∑ Fᵢ²` at
the origin whose every chart carries binding axes `{aE, aC}` (the `E`- and `c11`-axes) with Jacobian
exponents `jac aE = 7`, `jac aC = 8` (the rung-5b `Corank2ChartJac` / part-C `Corank2CoreGenWrap`
data), `AtlasRealizesExponents ![3,3,4] res` holds. Clause (i): each binding value is `7+1 = 8` or
`8+1 = 9`, both terminal exponents (`mem_terminalExponents_334_{eight,nine}`). Clause (ii): the
`minAdm = 8` attainment is matched by the `E`-axis (`jac aE + 1 = 8`). Generic in the ambient
dimension `D` and axis pair so rung 5d supplies the concrete chart (`aE = ⟨0,_⟩`, `aC = ⟨20,_⟩`). -/
theorem atlasRealizesExponents_334 {D Mgen : ℕ} {F : Fin Mgen → (Fin D → ℝ) → ℝ}
    (res : Resolution F (0 : Fin D → ℝ)) (aE aC : Fin D)
    (hbind : ∀ c : Fin res.numCharts,
      bindingAxes ((res.charts c).bexp (res.charts c).k₀) = {aE, aC})
    (hjE : ∀ c : Fin res.numCharts, (res.charts c).jac aE = 7)
    (hjC : ∀ c : Fin res.numCharts, (res.charts c).jac aC = 8) :
    AtlasRealizesExponents (![3,3,4] : Fin 3 → ℕ) res := by
  refine ⟨?_, ?_⟩
  · -- clause (i): every binding-axis value is a terminal exponent
    intro c a ha
    rw [hbind c, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [hjE c]; exact mem_terminalExponents_334_eight
    · rw [hjC c]; exact mem_terminalExponents_334_nine
  · -- clause (ii): the minAdm attainment is matched by the E-axis
    intro l _ k hk
    obtain ⟨c, -⟩ := res.hne
    refine ⟨c, aE, ?_, ?_⟩
    · rw [hbind c]; exact Finset.mem_insert_self aE {aC}
    · rw [hjE c, hk]; decide

end DLNFibre.DLN.Aoyagi
