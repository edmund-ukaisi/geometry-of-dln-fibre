import DLNFibre.Core.EndBaseChangeSweep
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.RadicalCatenary

/-!
# `DLNFibre.Core.RouteCAssembly` — route-c assembly `codim(fibre d B) = C + δ` (conditional bank)

The downstream **arithmetic assembly** of the equivariant homogeneous-sweep route (thread 27/28
certificate): from the sweep dimension identity, the closure/density bridge, and the
dimension/codimension relations, the fibre codimension is the combinatorial codimension `C` plus the
matrix-stratum shift `δ`:

> `codimRepCanonical (fibre d B) = (cCodim d r).toNat + r·(d_N + d_0 − r)`   (`B` rank `r`).

**The conditional-bank pattern.** The one genuinely-hard rung — the homogeneous-sweep dimension
identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the closure/density bridge
`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`) are carried as **explicit named hypotheses** (this is
the conditional bank), so everything *around* them is machine-checked. Both are since **discharged
in-repo**: `hSweep` in `Core.FibreCodimFinal` (the route-β chart build), `hClosure` in
`Core.ClosureBridge` (`varietyDim_productRankLocus_eq_productRankLocusLE` — proved, **not** Cited).
The two dimension/codimension
relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
`hCatFibre`/`hCatSigma` in the base theorem; the primed variant discharges them from the
reducible-locus catenary `Core.RadicalCatenary` (true for any nonempty subset of affine space),
leaving ONLY the sweep + closure. Nothing in this module claims the sweep or the closure.

The arithmetic is **purely additive** (no `ℕ∞` truncated subtraction): chaining
`C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F` and cancelling the finite `dim F`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The route-c assembly (conditional bank) -/

/-- **Route-c assembly: `codim(fibre d B) = C + δ` (conditional bank).** For a rank-`r` target `B`
(`N ≥ 1`, alg-closed char 0), the geometric codimension of the fibre `mult⁻¹(B)` is `C = cCodim d r`
plus the matrix-stratum shift `δ = r·(d_N + d_0 − r)` — carrying the homogeneous-sweep dimension
identity `hSweep`, the closure bridge `hClosure`, and the two reducible-locus catenary
relations `hCatFibre`/`hCatSigma` as explicit named hypotheses. The proof is the additive chain
`C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F`, cancelling the finite `dim F`. -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hB : B.rank = r)
    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
          + varietyDim (canonicalCoord d '' fibre d B))
    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
    (hCatFibre : codimRepCanonical (fibre d B)
        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
    (hCatSigma : codimRepCanonical (productRankLocusLE (k := k) d r)
        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
          = (Nat.card (RepCoord d) : ℕ∞)) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) := by
  -- `codim Σ̄^r = C` (LANDED Brick A).
  have hCsigma : codimRepCanonical (productRankLocusLE (k := k) d r)
      = ((cCodim d r h).toNat : ℕ∞) :=
    codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h
  -- `dim Σ̄^r = dim Σ^r = δ + dim F` (closure then sweep).
  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
      = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
        + varietyDim (canonicalCoord d '' fibre d B) := by
    rw [← hClosure, hSweep]
  -- `dim F` is finite (`hCatFibre`: `codim F + dim F = card`, a finite total).
  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hCatFibre
    exact (ENat.coe_ne_top (Nat.card (RepCoord d))) hCatFibre.symm
  -- substitute `codim Σ̄^r = C`, `dim Σ̄^r = δ + dim F` into `hCatSigma`: `C + (δ + dim F) = card`.
  rw [hCsigma, hdimSigma] at hCatSigma
  -- additive chain `(dim F) + codim F = card = (dim F) + (C + δ)`; left-cancel the finite `dim F`.
  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
      = varietyDim (canonicalCoord d '' fibre d B)
        + (((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)) := by
    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
          rw [add_comm]
      _ = (Nat.card (RepCoord d) : ℕ∞) := hCatFibre
      _ = ((cCodim d r h).toNat : ℕ∞)
            + (((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
      _ = varietyDim (canonicalCoord d '' fibre d B)
            + (((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)) := by
          rw [← add_assoc, add_comm]
  exact ENat.add_right_injective_of_ne_top hdimF_ne key

/-! ## The catenary hypotheses discharged (only the sweep + closure remain) -/

/-- **Route-c assembly with the catenary hypotheses discharged.** For a rank-`r` target `B`
(`N ≥ 1`, alg-closed char 0), `codimRepCanonical (fibre d B) = C + δ`, carrying ONLY the
homogeneous-sweep dimension identity `hSweep` and the closure bridge `hClosure` as named
hypotheses — the two reducible-locus catenary relations are now **proved** from
`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
fibre and `Σ̄^r` are nonempty (their canonical flattenings have a point). -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep' [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hB : B.rank = r)
    (hFne : (canonicalCoord d '' fibre d B).Nonempty)
    (hSigmaNe : (canonicalCoord d '' productRankLocusLE (k := k) d r).Nonempty)
    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
          + varietyDim (canonicalCoord d '' fibre d B))
    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) :=
  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep d r h B hB hSweep hClosure
    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)

end DLNFibre.Core
