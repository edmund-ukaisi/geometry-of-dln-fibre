import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.ThetaComponentCount
import DLNFibre.Core.CThetaPermInvariance

/-!
# `DLNFibre.Core.CThetaGeometricPerm` — geometric transfer of the `(C, θ)` permutation invariance

The combinatorial Cor 5.10 (`cCodim_comp_perm`, `CThetaPermInvariance`) transferred to the genuine
**geometric** codimension of the rank loci. The LANDED Brick A
(`codimRepCanonical_productRankLocusLE_eq_cCodim`, `SigmaCodim`) identifies the geometric codimension
of the closed rank-`≤ r` product locus `Σ̄^r = productRankLocusLE d r` with the combinatorial `cCodim d r`.
Composing with `cCodim_comp_perm` gives:

`codim (Σ̄^r of d ∘ σ) = codim (Σ̄^r of d)` — the geometric codimension depends only on the multiset of `d`.

(A *combinatorial-codimension*-driven result; the `rlct = ½·codim` reading stays Cited — Aoyagi/Watanabe.)
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ} {k : Type u} [Field k]

/-- **Geometric Cor 5.10 (codimension):** the geometric codimension of the closed rank-`≤ r` product
locus `Σ̄^r` is permutation-invariant — `codim (Σ̄^r of d ∘ σ) = codim (Σ̄^r of d)`. Brick A
(`codimRepCanonical_productRankLocusLE_eq_cCodim`) on both sides + the combinatorial `cCodim_comp_perm`
in the middle. Stated on the `.toNat` (the codimension is finite and non-negative). -/
theorem codimRepCanonical_productRankLocusLE_comp_perm [IsAlgClosed k] [CharZero k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ σ) r).Nonempty) (h' : (kostantPartitions d r).Nonempty) :
    (codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat
      = (codimRepCanonical (productRankLocusLE (k := k) d r)).toNat := by
  have e1 : ((codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat : ℤ)
      = cCodim (d ∘ σ) r h := codimRepCanonical_productRankLocusLE_eq_cCodim (d ∘ σ) r h
  have e2 : ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ)
      = cCodim d r h' := codimRepCanonical_productRankLocusLE_eq_cCodim d r h'
  have : ((codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat : ℤ)
      = ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) := by
    rw [e1, e2, cCodim_comp_perm σ d r hr h h']
  exact_mod_cast this

/-- **Geometric Cor 5.10, sorted form:** the geometric codimension of `Σ̄^r` equals that of the
monotone rearrangement `Σ̄^r of d ∘ Tuple.sort d`. -/
theorem codimRepCanonical_productRankLocusLE_comp_sort [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ _root_.Tuple.sort d) r).Nonempty)
    (h' : (kostantPartitions d r).Nonempty) :
    (codimRepCanonical (productRankLocusLE (k := k) (d ∘ _root_.Tuple.sort d) r)).toNat
      = (codimRepCanonical (productRankLocusLE (k := k) d r)).toNat :=
  codimRepCanonical_productRankLocusLE_comp_perm (_root_.Tuple.sort d) d r hr h h'

/-- **Geometric Cor 5.10 (component count):** the number of top-dimensional components of `Σ̄^r` is
permutation-invariant — `#topComponents (d ∘ σ) r = #topComponents d r`. Given the geometric recovery
hypotheses (`hLowerBound` / `hRecover`, the per-`d` inputs of `numTop_eq_ncard_topComponents_of`) on
both sides, the combinatorial `numTop_comp_perm` transfers through. The hypotheses are stated, not
discharged: they are the geometric content that connects `numTop` to the component count. -/
theorem topComponents_ncard_comp_perm [IsAlgClosed k] [CharZero k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ σ) r).Nonempty) (h' : (kostantPartitions d r).Nonempty)
    (hLB : ∀ M' : Tuple (k := k) (d ∘ σ), (mult (d ∘ σ) M').rank ≤ r →
      ((cCodim (d ∘ σ) r h).toNat : ℕ∞) ≤ codimRepCanonical (orbitRankLocus M'))
    (hRec : ∀ p ∈ topComponents (k := k) (d ∘ σ) r h,
      ∃ m ∈ kostantPartitions (d ∘ σ) r, partitionIdeal (k := k) (d ∘ σ) r m = p)
    (hLB' : ∀ M' : Tuple (k := k) d, (mult d M').rank ≤ r →
      ((cCodim d r h').toNat : ℕ∞) ≤ codimRepCanonical (orbitRankLocus M'))
    (hRec' : ∀ p ∈ topComponents (k := k) d r h',
      ∃ m ∈ kostantPartitions d r, partitionIdeal (k := k) d r m = p) :
    (topComponents (k := k) (d ∘ σ) r h).ncard = (topComponents (k := k) d r h').ncard := by
  rw [← numTop_eq_ncard_topComponents_of (d ∘ σ) r h hLB hRec,
    ← numTop_eq_ncard_topComponents_of d r h' hLB' hRec',
    numTop_comp_perm σ d r hr h h']

end DLNFibre.Core
