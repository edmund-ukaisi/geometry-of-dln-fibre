/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.CTheta
import DLNFibre.Core.CCodimCornerMono
import DLNFibre.DLN.RLCT.Validate.MinAdmCCodim
import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

set_option linter.style.longLine false

/-!
# `RouteMSJDeepCodim` — geometric codimension = the composite-rank recursion (Finding B(2))

**Thread `genm-deepatlas`, aoyagi-full Stage 2 (branch α).** The honest discharge of crstrat's
**Finding B(2)** — "CRrec = geometric κ_k". This is an exact **codimension equality**, not a chart
cover: the deferred "charts-exhaust {rank ≤ s}" set-coverage is vacuous (the size-`0` empty-minor pivot
chart is the whole space), so the genuine content — that the composite-rank recursion equals the actual
geometric codimension of the product rank locus — is the equality proved here.

Both sides are already banked; this file is the ~1-lemma **assembly**:

    codim Σ̄^r  =  cCodim d r        (`Core.SigmaCodim`, quiver/orbit-closure; `[IsAlgClosed][CharZero]`)
    cCodim d r =  cCodim (d−r) 0     (`Core.CTheta.cCodim_rankShift`, Lehalleur–Rimányi Lemma 4.5)
    cCodim (d−r) 0 =  minAdm (d−r)   (`MinAdmCCodim.minAdm_eq_cCodim`, the QIP ↔ Ext identity)
    minAdm (d−r) =  minAdmRec (d−r)  (`RouteMLayerSplit.minAdmRec_eq_minAdm`, the layer-peel recursion)

so `codim Σ̄^r = minAdmRec (d − r)` = the composite-rank (CR) recursion value `κ`.

## Scope and the ℝ/ℂ RESIDUAL (named, not faked)

This equality lives over `Core.Tuple` and an **algebraically closed field of characteristic 0** (the
setting of the quiver/orbit-closure codimension machinery — the paper's native algebraic setting). The
analytic RLCT capstone works over the **real** parameter space `Params H` (`Foundations.Loss`). The
statement "the real codimension of the real product rank locus equals `minAdmRec (d−r)`" needs an
**ℝ/ℂ codimension bridge for this locus, which is NOT banked** — a separate obligation (a later bridge
lane), deliberately not discharged or papered over here. The transpose map identifies `prod` with the
transpose of `Core.mult` (orientation), but does not by itself supply the real↔complex codim bridge.

## What lands here (sorry-free)

* **`codimRepCanonical_productRankLocusLE_eq_minAdmRec`** —
  `codimRepCanonical (productRankLocusLE d r) = (minAdmRec (dminus d r) : ℕ∞)`, for `1 ≤ N`,
  `∀ i, r ≤ d i`, over `[Field k] [IsAlgClosed k] [CharZero k]`. The geometric codimension of the
  closed product rank-`≤ r` locus equals the composite-rank recursion `κ`.

Standalone (NOT aggregator-wired). Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core

universe u

namespace DeepAtlas

/-- **Geometric codimension = composite-rank recursion (`κ`).** The geometric codimension of the closed
product rank-`≤ r` locus `Σ̄^r = productRankLocusLE d r` equals the composite-rank (CR) recursion value
`minAdmRec (d − r)`. This is the honest, non-vacuous discharge of "CRrec = geometric κ_k" (crstrat
Finding B(2)) — an exact codimension equality, assembled from the banked geometric side
(`codimRepCanonical_productRankLocusLE_eq_cCodim_enat`, quiver/orbit-closure), the rank-shift
(`cCodim_rankShift`), the QIP↔Ext identity (`minAdm_eq_cCodim`), and the layer-peel recursion
(`minAdmRec_eq_minAdm`).

Over `[IsAlgClosed k] [CharZero k]` (the paper's algebraic setting). **RESIDUAL:** the real-parameter
capstone would need an ℝ/ℂ codim bridge for this locus, which is NOT banked (a separate lane). -/
theorem codimRepCanonical_productRankLocusLE_eq_minAdmRec
    {N : ℕ} {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hN : 1 ≤ N) (hr : ∀ i, r ≤ d i) :
    codimRepCanonical (productRankLocusLE (k := k) d r) = (minAdmRec (dminus d r) : ℕ∞) := by
  have h_dr : (kostantPartitions d r).Nonempty := kostantPartitions_nonempty_of_le hN hr
  have h_d0 : (kostantPartitions (dminus d r) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ => Nat.zero_le _)
  -- the ℕ core: `(cCodim d r).toNat = minAdmRec (d−r)`, via rankShift → minAdm ↔ cCodim → layer-peel
  have hkey : (cCodim d r h_dr).toNat = minAdmRec (dminus d r) := by
    rw [← cCodim_rankShift hr h_d0 h_dr, ← minAdm_eq_cCodim (dminus d r) hN h_d0,
      Int.toNat_natCast, minAdmRec_eq_minAdm]
  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h_dr, hkey]

/-- Non-vacuity at the anchor `(2,2,2)`: the theorem instantiates on `d = ![2,2,2]`, `r = 0` (over any
algebraically closed char-0 field) — `codim Σ̄^0 = minAdmRec ![2,2,2]` (`= 3`, Lehalleur–Rimányi's
`C = 3`; the value is banked as `minAdm_d222_eq_three`). -/
example {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] :
    codimRepCanonical (productRankLocusLE (k := k) Core.d222 0)
      = (minAdmRec (dminus Core.d222 0) : ℕ∞) :=
  codimRepCanonical_productRankLocusLE_eq_minAdmRec Core.d222 0 (by norm_num) (fun _ => Nat.zero_le _)

end DeepAtlas

end DLNFibre.DLN.RLCT
