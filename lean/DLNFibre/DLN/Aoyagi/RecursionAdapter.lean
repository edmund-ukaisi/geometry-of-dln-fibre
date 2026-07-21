import DLNFibre.Core.Aoyagi.ProductResolution
import DLNFibre.DLN.RLCT.Engine.O5Realization
import DLNFibre.DLN.RLCT.Validate.MinAdmCCodim

/-!
# `DLN.Aoyagi.RecursionAdapter` — the salvage adapter: Engine combinatorics ⟹ `hlb`/`hattain`

**BOOKKEEPING (charter §2), not geometric progress.** The two combinatorial conjuncts of
`exists_coreResolution` — `hlb` (no binding divisor undershoots `qipMin`) and `hattain` (some binding
divisor attains it) — are ALREADY PROVED, at full generality and axiom-clean, in the (retired-but-
kernel-checked) Engine combinatorics and the `MinAdmCCodim` bridge:

* `Engine.minAdm_le_terminalExponents` — every terminal exponent of the built tree is `≥ minAdm d`
  (the `hlb` content, width-free);
* `Engine.o5_core_realized` — some leaf divisor of the built tree attains `minAdm d` (the `hattain`
  content; needs positive widths);
* `RLCT.minAdm_eq_cCodim` ∘ `Core.cCodim_eq_qipMin` — the bridge `minAdm d = cCodim d 0 = qipMin d`.

This module wires those into the `Chart`/`Resolution` vocabulary via an **exponent-realization seam**
(`AtlasRealizesExponents`): the hypothesis that a geometric atlas' binding-axis exponents match the
built tree's terminal divisor exponents (a match of ℕ-valued value-supports, NOT a structural
chart↔leaf correspondence). Given the seam, `hlb ∧ hattain` follows sorry-free. The seam itself — that
the geometric charts realize the tree's exponents — is the remaining GEOMETRIC obligation (the coupled
monument), deliberately isolated here and NOT discharged.

**Import discipline (charter §3 / RETIRED.md).** This imports ONLY the audited-green combinatorial
closure (`O5Realization`, `EngineConstruction`, `MinAdmCCodim`); it never imports or concludes any
`Geo*`/`ChartBridge*`/`CanonicalResolution` module (the F1-killed chart route). The four salvage
theorems are axiom-clean (`[propext, Classical.choice, Quot.sound]`); the fossil `sorry` in
`ClearableReify` (a transitive import of `O5Realization`) is a SEPARATE theorem off all four cones.

**Kill-set anchors (C2).** The Engine's `minAdm` reconciles with the decorrelated `Mval` battery
(`theory/aoyagi-2023-reproduction/g-monument-mval-instances.py`) at both defect witnesses — the
non-monotone Case-2 witness `(2,2,3,2)` (running-min `3`, NOT the raw label `6`) and the
`T`-profile-incomparability witness `(2,2,1,1)` (`1`); see the `example`s below.
-/

open MeasureTheory Set Filter Topology
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N D Mgen : ℕ}

/-- **The exponent-realization seam.** A geometric atlas `res` of `∑ Fᵢ²` at the origin *realizes the
exponents* of the Engine's built resolution tree of widths `d` when (i) every chart binding-axis
exponent `jac a + 1` matches some terminal exponent of the tree (so the tree's lower bound applies to
it), and (ii) every `minAdm`-ATTAINING leaf divisor exponent is matched by some chart binding-axis
exponent (so the tree's attained minimum is realized by a chart). This is a match of the ℕ-valued
exponent value-supports ONLY — NOT a structural chart↔leaf correspondence (no coordinate/multiplicity
map is asserted); both clauses hold for the actual Aoyagi atlas, where each chart's binding axes carry
its `t̃=0` terminal divisor exponents. Clause (ii) is conditioned on `= minAdm d` — the weakest form
that yields `hattain` (no all-leaf surjectivity is demanded of the residual). This is the GEOMETRIC
obligation the coupled monument must discharge; here it is a hypothesis. -/
def AtlasRealizesExponents (d : Fin (N + 1) → ℕ) {F : Fin Mgen → (Fin D → ℝ) → ℝ}
    (res : Resolution F (0 : Fin D → ℝ)) : Prop :=
  (∀ (c : Fin res.numCharts) (a : Fin D),
      a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
      ((res.charts c).jac a + 1) ∈
        ResolutionTree.terminalExponents (buildTree d (conOracle d) (conRoot : ConState N)))
  ∧ (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
      ∀ k : Fin l.numDiv, l.divExp k = minAdm d →
        ∃ (c : Fin res.numCharts) (a : Fin D),
          a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
          (res.charts c).jac a + 1 = l.divExp k)

/-- **The salvage bridge `qipMin d = minAdm d`** (as `ℤ`). Composes the `MinAdmCCodim` all-width
identity `minAdm = cCodim` with `Core`'s `cCodim = qipMin` (monotone `d`). -/
theorem qipMin_eq_minAdm (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    qipMin d hne = (minAdm d : ℤ) := by
  rw [← cCodim_eq_qipMin d hd h hne, minAdm_eq_cCodim d (by omega) h]

/-- **The adapter (bookkeeping).** Given the realization seam, the two combinatorial conjuncts of
`exists_coreResolution` — `hlb` and `hattain` against `qipMin d` — hold, sorry-free. `hlb` rides
`minAdm_le_terminalExponents`; `hattain` rides `o5_core_realized`; both via `qipMin_eq_minAdm`. Zero
geometric content — the geometry lives entirely in `AtlasRealizes`, which is a hypothesis here. -/
theorem hlb_hattain_of_atlasRealizesExponents (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty)
    {F : Fin Mgen → (Fin D → ℝ) → ℝ} (res : Resolution F (0 : Fin D → ℝ))
    (hreal : AtlasRealizesExponents d res) :
    (∀ (c : Fin res.numCharts) (a : Fin D),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin D),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  obtain ⟨hmem, hrealize⟩ := hreal
  have hbridge : qipMin d hne = (minAdm d : ℤ) := qipMin_eq_minAdm d hd hN h hne
  refine ⟨?_, ?_⟩
  · intro c a ha
    have hlb_nat : minAdm d ≤ (res.charts c).jac a + 1 :=
      minAdm_le_terminalExponents d (by omega) _ (hmem c a ha)
    rw [hbridge]
    exact_mod_cast hlb_nat
  · obtain ⟨l, hl, k, hk⟩ := o5_core_realized d (by omega) hpos
    obtain ⟨c, a, ha, hval⟩ := hrealize l hl k hk
    refine ⟨c, a, ha, ?_⟩
    rw [hbridge]
    have hattain_nat : (res.charts c).jac a + 1 = minAdm d := by rw [hval, hk]
    exact_mod_cast hattain_nat

/-- **The leaf-shaped reduction (sorry-free) — `exists_coreResolution` ⟸ the geometric obligation.**
Given a realizing atlas exists (`hgeo` — the coupled ideal-route monument, isolated as the sole
residual), the FULL `∃ res, hlb ∧ hattain` conclusion of `exists_coreResolution` follows. The Kostant
nonemptiness is derived internally from `hne` (`kostant_nonempty_iff_qipFeasible_nonempty`, monotone
`d`), so wiring the leaf is: supply `hgeo` (a `sorry`), then `exact` this. Generic in the ambient
dimension `D` and family `F` — instantiated at `D = flatDim d`, `F = coreGen d e`. -/
theorem exists_hlb_hattain_of_exists_atlasRealizesExponents (d : Fin (N + 1) → ℕ) (hd : Monotone d)
    (hN : 0 < N) (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    {F : Fin Mgen → (Fin D → ℝ) → ℝ}
    (hgeo : ∃ res : Resolution F (0 : Fin D → ℝ), AtlasRealizesExponents d res) :
    ∃ res : Resolution F (0 : Fin D → ℝ),
      (∀ (c : Fin res.numCharts) (a : Fin D),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin D),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  have h : (kostantPartitions d 0).Nonempty :=
    (kostant_nonempty_iff_qipFeasible_nonempty d hd).mpr hne
  obtain ⟨res, hreal⟩ := hgeo
  exact ⟨res, hlb_hattain_of_atlasRealizesExponents d hd hN hpos h hne res hreal⟩

/-! ## Kill-set anchors (C2) — the Engine `minAdm` reconciles with the decorrelated `Mval` battery -/

/-- Case-2 defect witness `(2,2,3,2)` (non-monotone): `minAdm = 3` — the running-min physical value,
NOT the raw Case-2 label `6`. Matches `g-monument-mval-instances.py`'s `qipMin((2,2,3,2)) = 3`. -/
example : minAdm ![2, 2, 3, 2] = 3 := by decide

/-- `T`-profile incomparability witness `(2,2,1,1)`: `minAdm = 1`. The adapter leans on no profile
comparability. Matches the battery's `Mval((2,2,1,1), (2,1,0)) = 1`. -/
example : minAdm ![2, 2, 1, 1] = 1 := by decide

/-- Certificate cross-check `(3,3,4)`: `minAdm = 8` (thread 27). -/
example : minAdm ![3, 3, 4] = 8 := by decide

/-- Certificate cross-check `(4,4,4)`: `minAdm = 12` (thread 28). -/
example : minAdm ![4, 4, 4] = 12 := by decide

end DLNFibre.DLN.Aoyagi
