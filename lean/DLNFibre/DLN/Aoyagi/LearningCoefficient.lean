import DLNFibre.Core.Aoyagi.Engine
import DLNFibre.DLN.RlctPayoff
import Meta.Cordon

/-!
# `DLN.Aoyagi.LearningCoefficient` — the corollary/test: `rlct(K^DLN_0) = C/2` VIA THE ENGINE

**BLUEPRINT (v3/v4).** The learning-coefficient theorem as a **corollary and test** of Objects A–D
(charter §0: the objects are the goal). It routes the value entirely through the engine, so its axiom
cone has `sorryAx` (the frontier leaves) but **NOT** `cited_aoyagi_lower_ax`/`cited_watanabe_upper_ax`.

## Soundness fixes carried (v2 defects 3 & 5, and the v4 un-bundling)

* **Concrete `F` (no adversarial existential).** The resolved family is the CONCRETE flattened
  product-map entry family `coreGen d e` (`(∏C)ᵢⱼ` in flat coordinates), not an `∃ F` an adversary
  could pick to trivially satisfy the conjuncts.
* **The reduction is a SEPARATE named leaf.** `coreReduction` (the deepest-point Thm 4 + the
  regular-block/flatten R0 + the ℝ≥0∞→ℝ carrier bridge) is un-bundled from the resolution existence;
  it rides banked machinery (`deepest_le_of_homogeneous_core`, the measure-preserving flatten). The
  genuinely-new content it names is the carrier bridge.
* **Defect 5.** The resolution is OBTAINED from `exists_coreResolution` (B's existence on the cone);
  no analytic side condition is user-facing.
* **Defect 3.** `exists_coreResolution` guarded by `0 < N` + positive widths.
* **Scope (named future leaf).** The `Monotone d` hypothesis is the QIP-side scope; the non-monotone
  extension rides the banked permutation-invariance of `(C, θ)` — a future leaf, not a hidden gap.
-/

open MeasureTheory Filter Topology
open Meta.Cordon
open DLNFibre.Core DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- The **flattened parameter dimension** `∑ᵢ d(i+1)·d(i)` — the number of real coordinates of
`Rep_d` (a matrix tuple), the source dimension of the resolution charts. -/
def flatDim (d : Fin (N + 1) → ℕ) : ℕ := ∑ i : Fin N, d i.succ * d i.castSucc

/-- The **concrete flattened core-generator family**: `coreGen d e k u = (∏ C)ᵢⱼ` where `(i,j)` is the
`k`-th entry of the product `mult d` evaluated at the tuple `e u` (the flatten `e` of the exceptional
coordinates `u`). The entries of the multiplication map — Aoyagi's core `∏ C`, worked.tex:120–128.
Definable and concrete (no existential family). -/
noncomputable def coreGen (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ᵐ Tuple (k := ℝ) d) :
    Fin (d (Fin.last N) * d 0) → (Fin (flatDim d) → ℝ) → ℝ :=
  fun k u ↦ (mult d (e u)) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- **FRONTIER leaf (bookkeeping) — the measure-preserving flatten exists.** `Rep_d ≃ᵐ ℝ^flatDim`
sending the deepest tuple `0` to `0`, volume-preserving (a coordinate reindexing of a product of
matrix spaces). Rides the banked flatten machinery (`ParamsFlat`-style); named as a bookkeeping leaf
(R0), not a hidden gap. -/
@[blueprint]
theorem exists_flatten (d : Fin (N + 1) → ℕ) :
    ∃ e : (Fin (flatDim d) → ℝ) ≃ᵐ Tuple (k := ℝ) d, MeasurePreserving e ∧ e 0 = 0 := by
  -- map: DLN-flatten (measure-preserving coordinate reindexing Rep_d ≃ᵐ ℝ^flatDim; R0 bookkeeping)
  sorry

/-- **FRONTIER leaf — the deepest-point + flatten + carrier reduction.** `rlctGlobal (lossDLN d 0) =
rlctAt (∑ (coreGen d e)ᵢ²) 0`: the global RLCT of the zero-product loss equals the local RLCT of the
flattened core `∑ (∏C)ᵢⱼ²` at the origin. This composes (i) the deepest-point reduction (Aoyagi Thm 4,
worked.tex:437–458: the origin is the worst point of the homogeneous core — banked
`deepest_le_of_homogeneous_core`), (ii) the flatten `e` (measure-preserving, `e 0 = 0`; at `r = 0`
there is no regular block so the flat core loss `∑(coreGen)²` equals `lossDLN d 0 ∘ e` by the
Frobenius identity `‖M‖²_F = ∑ Mᵢⱼ²`), and (iii) the ℝ≥0∞→ℝ **carrier bridge** — the genuinely-new
content named here (`RLCT.Global.rlctGlobal` on `Rep_d` ↔ `RLCT.rlctAt` on `ℝ^flatDim`). -/
@[blueprint]
theorem coreReduction (d : Fin (N + 1) → ℕ) (hN : 0 < N)
    (e : (Fin (flatDim d) → ℝ) ≃ᵐ Tuple (k := ℝ) d) (hemp : MeasurePreserving e) (he0 : e 0 = 0) :
    RLCT.Global.rlctGlobal (lossDLN d 0) = RLCT.rlctAt (sumSqFam (coreGen d e)) 0 := by
  -- map: DLN-reduction (Thm4 deepest ∘ flatten ∘ Frobenius ∘ carrier bridge ℝ≥0∞→ℝ)
  sorry

/-- **FRONTIER leaf (the geometric MONUMENT) — the core resolution exists.** For a genuine deep
network (`0 < N`) with positive widths (`hpos`), the flattened zero-product core `∑ (coreGen d e)ᵢ²`
admits a certified resolution **atlas** (Object B) at the deepest point `0`, whose binding divisors —
across all charts — realise the QIP spectrum with **min-attainment** (Object D, defect-4 form:
`hlb` no undershoot + `hattain` some chart's divisor attains `qipMin`). The atlas's existence is
Aoyagi's Hironaka construction with the explicit coupled `diag(b)` recursion for corank ≥ 2
(worked.tex:475–520; the genuine frontier this expedition must build, charter §1.B); the
min-attainment is Aoyagi's Lemma 3 minimisation (worked.tex:529–542). `F = coreGen d e` is concrete.
This is the single genuine-mathematics frontier leaf of the blueprint (the reduction is bookkeeping). -/
@[blueprint]
theorem exists_coreResolution (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ᵐ Tuple (k := ℝ) d) :
    ∃ res : Resolution (coreGen d e) 0,
      (∀ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne) := by
  -- map: DLN-existence (Hironaka + coupled diag(b) ATLAS + Lemma-3 min-attainment; F concrete)
  sorry

/-- **The learning coefficient `rlct(K^DLN_0) = C/2`, VIA THE ENGINE (the corollary/test).** For a
genuine deep network with positive widths, the global RLCT of the zero-product square-Frobenius DLN
loss equals half the combinatorial codimension `C = cCodim d 0` — DLNs are mildly singular. Wired:
the flatten (`exists_flatten`) + the reduction (`coreReduction`: `rlctGlobal = rlctAt (∑coreGenᵢ²) 0`),
then the engine value `2·rlctAt (∑coreGenᵢ²) 0 = cCodim d 0`
(`Resolution.two_mul_rlctAt_eq_cCodim` = Object B's atlas-min CoV/monomial rule ∘ Object D's QIP
bridge), obtaining the resolution from `exists_coreResolution`. The axiom cone is
`{propext, sorryAx, Classical.choice, Quot.sound}` — the DLN cites are NOT invoked (the value is
derived, not cited); the kill-path (charter §3). -/
@[blueprint]
theorem aoyagi_learning_coefficient_via_engine (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    RLCT.Global.rlctGlobal (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 := by
  obtain ⟨e, hemp, he0⟩ := exists_flatten d
  obtain ⟨res, hlb, hattain⟩ := exists_coreResolution d hd hN hpos hne e
  have hred : RLCT.Global.rlctGlobal (lossDLN d 0) = RLCT.rlctAt (sumSqFam (coreGen d e)) 0 :=
    coreReduction d hN e hemp he0
  have heng : 2 * RLCT.rlctAt (sumSqFam (coreGen d e)) 0 = ((cCodim d 0 h).toNat : ℝ) :=
    res.two_mul_rlctAt_eq_cCodim d hd h hne hlb hattain
  rw [hred]; linarith [heng]

end DLNFibre.DLN.Aoyagi
