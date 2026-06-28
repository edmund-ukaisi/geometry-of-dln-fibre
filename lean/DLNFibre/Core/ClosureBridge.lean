/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.RadicalCatenary
import DLNFibre.Core.FibreCodim
import DLNFibre.Core.RouteCAssembly

/-!
# `DLNFibre.Core.ClosureBridge` — `hClosure`: `varietyDim Σ^r = varietyDim Σ̄^r`

The closure/density bridge that `RouteCAssembly` carries as a hypothesis (`hClosure`), proved
in-repo (zero-cite) by the **codimension sandwich** (thread 32 certificate, Route 2), sidestepping
the naive set-closure `Σ̄^r = repClosure(Σ^r)` (which would need an unbuilt rank-raising/density
theorem).

The argument, with `C = cCodim d r`:
- Both loci satisfy the irreducibility-free catenary `codim Z + varietyDim Z = card`
  (`RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty`), so `varietyDim Σ^r =
  varietyDim Σ̄^r ⟺ codim Σ^r = codim Σ̄^r` (left-cancel the finite codim).
- `codim Σ̄^r = C` is LANDED (`SigmaCodim`).
- Sandwich for `codim Σ^r = C`:
  - `C = codim Σ̄^r ≤ codim Σ^r` by anti-monotonicity on `Σ^r ⊆ Σ̄^r`.
  - `codim Σ^r ≤ C` by exhibiting ONE corner-exactly-`r` orbit `W ⊆ Σ^r` with `codim W = C` — the
    minimising-Kostant realizer `realizerD hm₀`'s `G_d`-orbit (corner is `G_d`-invariant; `codim W =
    codim(orbitRankLocus M₀) = C` via `vanishingIdeal_orbitRankLocus_eq_orbitSet`). Only ONE top
    piece
    of `Σ^r` is needed — lower strata are lower-dimensional "closed junk" that cannot change
    `varietyDim` — which is why this dodges the rank-raising theorem.

## Main results
- `codimRepCanonical_productRankLocus_eq_cCodim_enat` — `codim Σ^r = C` (the sandwich, L8).
- `varietyDim_productRankLocus_eq_productRankLocusLE` — `hClosure` (L9).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- `Σ^r ⊆ Σ̄^r`: the exact-rank locus sits in the rank-`≤ r` locus (`rank = r ⟹ rank ≤ r`). -/
theorem productRankLocus_subset_productRankLocusLE (d : Fin (N + 1) → ℕ) (r : ℕ) :
    productRankLocus (k := k) d r ⊆ productRankLocusLE (k := k) d r :=
  fun _ hA ↦ hA.le

/-- The `G_d`-orbit of a tuple `M`, as a subset of `Tuple d`. Its `canonicalCoord`-image is
`orbitSet M`. -/
def orbitAsTuples (M : Tuple (k := k) d) : Set (Tuple (k := k) d) :=
  {A | ∃ P : BaseChangeGroup (k := k) d, P • M = A}

theorem image_orbitAsTuples (M : Tuple (k := k) d) :
    canonicalCoord d '' orbitAsTuples M = orbitSet M := rfl

/-- The `G_d`-orbit of the minimising-Kostant realizer sits in `Σ^r`: the corner (`= rank ∘ mult`)
is `G_d`-invariant (`rankPattern_eq_of_smul`), and `= r` at the realizer (`rank_mult_realizerD`). -/
theorem orbitAsTuples_realizerD_subset_productRankLocus {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    orbitAsTuples (realizerD (k := k) hm) ⊆ productRankLocus (k := k) d r := by
  rintro A ⟨P, rfl⟩
  show (mult d (P • realizerD (k := k) hm)).rank = r
  rw [← corner_rankPattern_eq_rank,
    ← rankPattern_eq_of_smul P rfl 0 (Fin.last N) (Fin.zero_le _),
    corner_rankPattern_eq_rank, rank_mult_realizerD hm]

/-- The realizer orbit attains codimension `C`: its vanishing ideal is that of `orbitRankLocus M₀`
(`vanishingIdeal_orbitRankLocus_eq_orbitSet`), whose codim is `C`
(`codimRepCanonical_orbitRankLocus_realizerD`). -/
theorem codimRepCanonical_orbitAsTuples_realizerD [CharZero k] [Infinite k]
    {d : Fin (N + 1) → ℕ} {r : ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions d r) :
    codimRepCanonical (orbitAsTuples (realizerD (k := k) hm))
      = codimRepCanonical (orbitRankLocus (realizerD (k := k) hm)) := by
  rw [codimRepCanonical, codimRepCanonical, codimRep, codimRep, image_orbitAsTuples,
    vanishingIdeal_orbitRankLocus_eq_orbitSet]

/-- **L8 — `codim Σ^r = C` (the codimension sandwich).** `C = codim Σ̄^r ≤ codim Σ^r` (anti-mono on
`Σ^r ⊆ Σ̄^r`), and `codim Σ^r ≤ C` via the realizer orbit `W ⊆ Σ^r` with `codim W = C`. -/
theorem codimRepCanonical_productRankLocus_eq_cCodim_enat [CharZero k] [Infinite k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    codimRepCanonical (productRankLocus (k := k) d r) = ((cCodim d r h).toNat : ℕ∞) := by
  -- a minimising Kostant partition `m₀` and its realizer `M₀`
  obtain ⟨m₀, hm₀, hval⟩ := Finset.exists_mem_eq_inf' h (fun m ↦ codimForm N (extendℤ m))
  -- the realizer orbit attains `C` (mirrors `SigmaCodim`'s `hreal`)
  have hreal : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))
      = ((cCodim d r h).toNat : ℕ∞) := by
    have hfin : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀)) ≠ ⊤ := by
      rw [codimRepCanonical_orbitRankLocus_eq_height]
      exact Ideal.height_ne_top
        (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
    have hceq : cCodim d r h = codimForm N (extendℤ m₀) := hval
    have hnn : 0 ≤ cCodim d r h := by
      rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
      exact fun m' _ ↦ Int.natCast_nonneg _
    have htn : ((codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))).toNat : ℤ)
        = (cCodim d r h).toNat := by
      rw [codimRepCanonical_orbitRankLocus_realizerD hm₀, hceq]
      omega
    rw [← ENat.coe_toNat hfin]
    exact_mod_cast htn
  refine le_antisymm ?_ ?_
  · -- `codim Σ^r ≤ C`: the realizer orbit `W ⊆ Σ^r` has `codim W = C`
    calc codimRepCanonical (productRankLocus (k := k) d r)
        ≤ codimRepCanonical (orbitAsTuples (realizerD (k := k) hm₀)) :=
          codimRepCanonical_mono (orbitAsTuples_realizerD_subset_productRankLocus hm₀)
      _ = codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀)) :=
          codimRepCanonical_orbitAsTuples_realizerD hm₀
      _ = ((cCodim d r h).toNat : ℕ∞) := hreal
  · -- `C = codim Σ̄^r ≤ codim Σ^r`
    rw [← codimRepCanonical_productRankLocusLE_eq_cCodim_enat (k := k) d r h]
    exact codimRepCanonical_mono (productRankLocus_subset_productRankLocusLE d r)

/-- `Σ^r` is nonempty (its `canonicalCoord`-image): the realizer of a minimising Kostant partition
lies in it. -/
theorem nonempty_image_productRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    (canonicalCoord d '' productRankLocus (k := k) d r).Nonempty := by
  obtain ⟨m₀, hm₀, _⟩ := Finset.exists_mem_eq_inf' h (fun m ↦ codimForm N (extendℤ m))
  exact ⟨canonicalCoord d (realizerD (k := k) hm₀),
    realizerD (k := k) hm₀, rank_mult_realizerD hm₀, rfl⟩

/-- **L9 — `hClosure`: `varietyDim Σ^r = varietyDim Σ̄^r`.** Both loci satisfy the
irreducibility-free catenary `codim Z + varietyDim Z = card`; with `codim Σ^r = C = codim Σ̄^r`
(L8 + `SigmaCodim`), left-cancelling the finite codim gives equal `varietyDim`. -/
theorem varietyDim_productRankLocus_eq_productRankLocusLE [CharZero k] [Infinite k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
      = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r) := by
  -- nonemptiness of both loci (realizer ∈ Σ^r ⊆ Σ̄^r)
  have hSigNe : (canonicalCoord d '' productRankLocus (k := k) d r).Nonempty :=
    nonempty_image_productRankLocus d r h
  have hSigBarNe : (canonicalCoord d '' productRankLocusLE (k := k) d r).Nonempty :=
    hSigNe.mono (Set.image_mono (productRankLocus_subset_productRankLocusLE d r))
  -- the two catenary identities
  have hcatSig := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := k) hSigNe
  have hcatSigBar := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := k) hSigBarNe
  -- equal codims
  have hcod : codimRepCanonical (productRankLocus (k := k) d r)
      = codimRepCanonical (productRankLocusLE (k := k) d r) := by
    rw [codimRepCanonical_productRankLocus_eq_cCodim_enat d r h,
      codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]
  -- left-cancel the finite codim from `codim + dim = card`
  have hcodne : codimRepCanonical (productRankLocusLE (k := k) d r) ≠ ⊤ := by
    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]; exact ENat.coe_ne_top _
  -- `codim Σ̄^r + dim Σ^r = codim Σ̄^r + dim Σ̄^r` (rewrite codim Σ^r = codim Σ̄^r in `hcatSig`)
  have key : codimRepCanonical (productRankLocusLE (k := k) d r)
        + varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
      = codimRepCanonical (productRankLocusLE (k := k) d r)
        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r) := by
    rw [hcatSigBar, ← hcod, hcatSig]
  exact ENat.add_right_injective_of_ne_top hcodne key

/-- **Route-c assembly with `hClosure` discharged: `codim(fibre d B) = C + δ` carrying ONLY
`hSweep`.** Wires the in-repo `hClosure` (`varietyDim_productRankLocus_eq_productRankLocusLE`) into
`RouteCAssembly.codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'`, so the only remaining named
hypothesis is the homogeneous-sweep dimension identity `hSweep`. Zero-cite: the closure bridge is
proved, not assumed. -/
theorem codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep_closure
    [CharZero k] [Infinite k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (hB : B.rank = r)
    (hFne : (canonicalCoord d '' fibre d B).Nonempty)
    (hSigmaNe : (canonicalCoord d '' productRankLocusLE (k := k) d r).Nonempty)
    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
        = ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞)
          + varietyDim (canonicalCoord d '' fibre d B)) :
    codimRepCanonical (fibre d B)
      = ((cCodim d r h).toNat : ℕ∞) + ((r * (d (Fin.last N) + d 0 - r) : ℕ) : ℕ∞) :=
  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep' d r h B hB hFne hSigmaNe hSweep
    (varietyDim_productRankLocus_eq_productRankLocusLE d r h)

end DLNFibre.Core
