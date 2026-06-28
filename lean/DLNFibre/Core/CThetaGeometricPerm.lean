import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.CCodimZeroStrict
import DLNFibre.Core.CThetaPermInvariance

/-!
# `DLNFibre.Core.CThetaGeometricPerm` — geometric transfer of the `(C, θ)` permutation invariance

The combinatorial Cor 5.10 (`cCodim_comp_perm` / `numTop_comp_perm`, `CThetaPermInvariance`) carried to
the genuine **geometric** `(C, θ)` of the rank loci, by composing with the LANDED
geometric = combinatorial bridges:

* `codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (`SigmaCodim`) — `codim Σ̄^r = (cCodim d r).toNat`.
* `numTop_eq_ncard_topComponents` (`CCodimZeroStrict`) — `numTop d r = #topComponents`, the bridge that
  no longer needs the earlier `hLowerBound`/`hRecover` gating hypotheses.

So the geometric codimension of `Σ̄^r` and its top-dimensional component count both depend only on the
multiset of `d`. The permutation statements hold **given the Kostant-set finsets are nonempty**; the
`_of_le` variants discharge that from `1 ≤ N` and `r ≤ min d` (via
`kostantPartitions_nonempty_of_le`). (A *geometric-codimension / component-count* result; the
`rlct = ½·codim` reading stays Cited — Aoyagi/Watanabe. Nothing here is named `rlct_`.)
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ} {k : Type u} [Field k]

/-- **Geometric Cor 5.10 (codimension):** the geometric codimension of the closed rank-`≤ r` product
locus `Σ̄^r` is permutation-invariant — `codim (Σ̄^r of d ∘ σ) = codim (Σ̄^r of d)`. The bridge
`codimRepCanonical_productRankLocusLE_eq_cCodim` (`codim Σ̄^r = cCodim`) on both sides + the
combinatorial `cCodim_comp_perm`. The `.toNat` form (the ℕ∞ form is below). -/
theorem codim_productRankLocusLE_toNat_comp_perm [CharZero k] [Infinite k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ σ) r).Nonempty) (h' : (kostantPartitions d r).Nonempty) :
    (codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat
      = (codimRepCanonical (productRankLocusLE (k := k) d r)).toNat := by
  have e1 : ((codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat : ℤ)
      = cCodim (d ∘ σ) r h := codimRepCanonical_productRankLocusLE_eq_cCodim (d ∘ σ) r h
  have e2 : ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ)
      = cCodim d r h' := codimRepCanonical_productRankLocusLE_eq_cCodim d r h'
  have hz : ((codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)).toNat : ℤ)
      = ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) := by
    rw [e1, e2, cCodim_comp_perm σ d r hr h h']
  exact_mod_cast hz

/-- **Geometric Cor 5.10, sorted form:** the geometric codimension of `Σ̄^r` equals that of the
monotone rearrangement `Σ̄^r of d ∘ Tuple.sort d`. -/
theorem codim_productRankLocusLE_toNat_comp_sort [CharZero k] [Infinite k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ _root_.Tuple.sort d) r).Nonempty)
    (h' : (kostantPartitions d r).Nonempty) :
    (codimRepCanonical (productRankLocusLE (k := k) (d ∘ _root_.Tuple.sort d) r)).toNat
      = (codimRepCanonical (productRankLocusLE (k := k) d r)).toNat :=
  codim_productRankLocusLE_toNat_comp_perm (_root_.Tuple.sort d) d r hr h h'

/-- **Geometric Cor 5.10 (codimension, ℕ∞ form):** the geometric codimension of `Σ̄^r` (in `ℕ∞`) is
permutation-invariant. The `ℕ∞` form is preferred over `.toNat` — it does not silently erase a `⊤`
case (finiteness is known here, but the stronger statement is the cleaner public API). -/
theorem codimRepCanonical_productRankLocusLE_comp_perm [CharZero k] [Infinite k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ σ) r).Nonempty) (h' : (kostantPartitions d r).Nonempty) :
    codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)
      = codimRepCanonical (productRankLocusLE (k := k) d r) := by
  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat (d ∘ σ) r h,
      codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h',
      cCodim_comp_perm σ d r hr h h']

/-- **Geometric Cor 5.10 (component count):** the number of top-dimensional components of `Σ̄^r` is
permutation-invariant — `#topComponents (d ∘ σ) r = #topComponents d r`, given both Kostant-set
finsets are nonempty. The bridge `numTop_eq_ncard_topComponents` on both sides + the combinatorial
`numTop_comp_perm`. -/
theorem ncard_topComponents_comp_perm [CharZero k] [Infinite k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ σ) r).Nonempty) (h' : (kostantPartitions d r).Nonempty) :
    (topComponents (k := k) (d ∘ σ) r h).ncard = (topComponents (k := k) d r h').ncard := by
  rw [← numTop_eq_ncard_topComponents (d ∘ σ) r h, ← numTop_eq_ncard_topComponents d r h',
    numTop_comp_perm σ d r hr h h']

/-- **Geometric Cor 5.10 (component count), sorted form.** -/
theorem ncard_topComponents_comp_sort [CharZero k] [Infinite k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ j, r ≤ d j)
    (h : (kostantPartitions (d ∘ _root_.Tuple.sort d) r).Nonempty)
    (h' : (kostantPartitions d r).Nonempty) :
    (topComponents (k := k) (d ∘ _root_.Tuple.sort d) r h).ncard
      = (topComponents (k := k) d r h').ncard :=
  ncard_topComponents_comp_perm (_root_.Tuple.sort d) d r hr h h'

/-! ## Discharged public API (from `1 ≤ N` + `r ≤ min d`)

The Kostant-set nonemptiness on both sides is discharged by `kostantPartitions_nonempty_of_le`, so
the following are conditional only on `1 ≤ N` and `r ≤ min d` (at every vertex). -/

/-- **Geometric Cor 5.10 (codimension, ℕ∞), from `1 ≤ N` + `r ≤ min d`.** The Kostant-set
nonemptiness is discharged by `kostantPartitions_nonempty_of_le`. -/
theorem codimRepCanonical_productRankLocusLE_comp_perm_of_le [CharZero k] [Infinite k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hN : 1 ≤ N) (hr : ∀ j, r ≤ d j) :
    codimRepCanonical (productRankLocusLE (k := k) (d ∘ σ) r)
      = codimRepCanonical (productRankLocusLE (k := k) d r) :=
  codimRepCanonical_productRankLocusLE_comp_perm σ d r hr
    (kostantPartitions_nonempty_of_le hN (fun j ↦ hr (σ j)))
    (kostantPartitions_nonempty_of_le hN hr)

/-- **Geometric Cor 5.10 (component count), from `1 ≤ N` + `r ≤ min d`.** -/
theorem ncard_topComponents_comp_perm_of_le [CharZero k] [Infinite k]
    (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hN : 1 ≤ N) (hr : ∀ j, r ≤ d j) :
    (topComponents (k := k) (d ∘ σ) r
        (kostantPartitions_nonempty_of_le hN (fun j ↦ hr (σ j)))).ncard
      = (topComponents (k := k) d r (kostantPartitions_nonempty_of_le hN hr)).ncard :=
  ncard_topComponents_comp_perm σ d r hr _ _

end DLNFibre.Core
