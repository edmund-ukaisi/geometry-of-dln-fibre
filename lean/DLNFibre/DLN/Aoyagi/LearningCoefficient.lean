import DLNFibre.Core.Aoyagi.Engine
import DLNFibre.DLN.RlctPayoff
import Meta.Cordon

/-!
# `DLN.Aoyagi.LearningCoefficient` — the corollary/test: `rlct(K^DLN_0) = C/2` VIA THE ENGINE

**BLUEPRINT (v3).** The learning-coefficient theorem as a **corollary and test** of Objects A–D
(charter §0: the objects are the goal, this is the test). It routes the value entirely through the
engine — the certified resolution (B), its monomial rule (C), and the combinatorial bridge (D) — and
so its axiom cone contains `sorryAx` (the frontier leaves) but **NOT** `cited_aoyagi_lower_ax` nor
`cited_watanabe_upper_ax`. Proving `aoyagi_learning_coefficient_via_engine` and confirming its
`#print axioms` is `{propext, sorryAx, Classical.choice, Quot.sound}` is the kill-path for the DLN
lower-bound cite (charter §3).

## The soundness fixes it carries (v2 defects 3 & 5)

* **Defect 5 (obtains the resolution + discharges side conditions internally).** The resolution is
  OBTAINED from `exists_coreResolution` — B's existence is genuinely on the cone — not taken as a
  hypothesis. No measurability / a.e.-nonzero analytic side condition is user-facing: they are
  discharged inside the engine (Object A's germ lemmas consume the resolution's analyticity fields;
  Object C's unit is `|unit|` from the Jacobian certificate). The user-facing hypotheses are only the
  genuine ones: `0 < N` (deep network), positive widths `hpos` (nondegeneracy), monotone `d`, and the
  Kostant/QIP nonemptiness.

* **Defect 3 (nondegeneracy).** `exists_coreResolution` is guarded by `0 < N` and `hpos : ∀ k, 0 < d k`
  (positive widths); at a degenerate width the QIP minimum can be `0` and no divisor can attain it, so
  the resolution existence is scoped to the nondegenerate regime (matching the corollary's guards).

## The reduction bundled into existence (Thm 4 + R0)

`exists_coreResolution`'s first conjunct `rlctGlobal (lossDLN d 0) = rlctAt (∑Fᵢ²) 0` is the
deepest-point reduction (Aoyagi Thm 4, worked.tex:437–458: the origin is the worst point of the
homogeneous core, so the global RLCT is the local RLCT at `0`) composed with the regular-block/flatten
bookkeeping R0 (`Rep_d ≃ᵐ ℝᴰ`, measure-preserving, `0 ↦ 0`; at `r = 0` there is no regular block, so
the core loss *is* `lossDLN d 0` in flat coordinates). Both are "built bookkeeping" (charter §1);
bundled here as the named reduction conjunct of the existence leaf.
-/

open MeasureTheory Filter Topology
open Meta.Cordon
open DLNFibre.Core DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **FRONTIER leaf (the geometric MONUMENT + R0/Thm-4 reduction) — the core resolution exists.**
For a genuine deep network (`0 < N`) with positive widths (`hpos`), the zero-product DLN core loss
`lossDLN d 0`, in flattened coordinates, admits a **certified `Resolution`** (Object B) at the
deepest point `0`, whose binding divisors realise the QIP spectrum with **min-attainment** (Object D,
v2 defect 4: `hdiv_lb` no undershoot + `hdiv_attain` some divisor attains `qipMin`). Bundled first
conjunct: the deepest-point + flatten reduction `rlctGlobal (lossDLN d 0) = rlctAt (∑Fᵢ²) 0`
(Thm 4 + R0). The resolution's existence is Aoyagi's Hironaka construction with the explicit coupled
`diag(b)` recursion for corank ≥ 2 (worked.tex:475–520; the genuine frontier this expedition must
build, per charter §1.B); the min-attainment is Aoyagi's Lemma 3 minimisation (worked.tex:529–542).
This is the single genuine-mathematics frontier leaf of the whole blueprint. -/
@[blueprint]
theorem exists_coreResolution (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    ∃ (D M : ℕ) (F : Fin M → (Fin D → ℝ) → ℝ) (res : Resolution F 0),
      RLCT.Global.rlctGlobal (lossDLN d 0) = RLCT.rlctAt (sumSqFam F) 0 ∧
      (∀ a ∈ bindingAxes (res.bexp res.k₀), qipMin d hne ≤ (res.jac a + 1 : ℤ)) ∧
      (∃ a ∈ bindingAxes (res.bexp res.k₀), (res.jac a + 1 : ℤ) = qipMin d hne) := by
  -- map: DLN-existence (Hironaka + coupled diag(b) resolution + Thm4/R0 reduction + Lemma-3 min-attainment)
  sorry

/-- **The learning coefficient `rlct(K^DLN_0) = C/2`, VIA THE ENGINE (the corollary/test).** For a
genuine deep network with positive widths, the global RLCT of the zero-product square-Frobenius DLN
loss equals half the combinatorial codimension `C = cCodim d 0` — DLNs are mildly singular. Wired:
the certified resolution from `exists_coreResolution` (its deepest-point/flatten reduction gives
`rlctGlobal = rlctAt (∑Fᵢ²) 0`), then the engine value `2·rlctAt (∑Fᵢ²) 0 = cCodim d 0`
(`Resolution.two_mul_rlctAt_eq_cCodim` = Object B's CoV/monomial rule ∘ Object D's QIP bridge). The
axiom cone is `{propext, sorryAx, Classical.choice, Quot.sound}` — the DLN cites
`cited_aoyagi_lower_ax`/`cited_watanabe_upper_ax` are NOT invoked (the value is derived, not cited);
that is the kill-path (charter §3). -/
@[blueprint]
theorem aoyagi_learning_coefficient_via_engine (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (h : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :
    RLCT.Global.rlctGlobal (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 := by
  obtain ⟨D, M, F, res, hred, hlb, hattain⟩ := exists_coreResolution d hd hN hpos h hne
  have heng : 2 * RLCT.rlctAt (sumSqFam F) 0 = ((cCodim d 0 h).toNat : ℝ) :=
    res.two_mul_rlctAt_eq_cCodim d hd h hne hlb hattain
  rw [hred]
  linarith [heng]

end DLNFibre.DLN.Aoyagi
