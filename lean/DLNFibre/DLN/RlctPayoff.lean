import DLNFibre.Core.Setup
import DLNFibre.Core.SigmaComponents
import DLNFibre.Core.CThetaGeometric
import DLNFibre.Core.CTheta
import DLNFibre.Core.ThetaComponentCount
import DLNFibre.Core.CCodimCornerMono
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.DLN.RlctPayoff` — the square-Frobenius loss, its zero-set, and the RLCT payoff (r = 0)

The application layer (`DLNFibre.DLN`, consuming `Core`): the deep-linear-network square-Frobenius
loss `K^DLN_B`, its zero-set (the multiplication fibre `mult⁻¹(B)`), the geometric codimension of
the zero-product fibre at corner `r = 0`, and the real-log-canonical-threshold payoff
`rlct(K^DLN_0) = ½·codim mult⁻¹(0)` through a **Cited** analytic interface.

## What is Proved / Cited / scoped here

* **D2 (Proved, field = ℝ).** `lossDLN d B A = ‖mult A − B‖²_F = Tr((mult A − B)ᵀ (mult A − B))`,
  `lossDLN_nonneg`, and the load-bearing **`zeroLocus_lossDLN_eq_fibre`** (the loss vanishes exactly
  on the fibre `mult⁻¹(B)`). The Frobenius core `Tr(MᵀM) = 0 ↔ M = 0` is Mathlib's
  `Matrix.trace_conjTranspose_mul_self_eq_zero_iff` (over ℝ, `conjTranspose = transpose`).

* **D3 bridge (a) (Proved, `[IsAlgClosed k]`).** The geometric codimension of the zero-product fibre
  `mult⁻¹(0) = Σ̄^0` equals the minimum codimension over its orbit closures
  (`codimRepCanonical_fibre_zero_eq_iInf_orbitCodim`): "codim of a finite union = min codim of its
  components", from `minimalPrimes_sigmaIdeal_eq` + Mathlib's `Ideal.height`.

* **D3 bridge (b) (Proved, `[IsAlgClosed k] [CharZero k]`).** That infimum equals the combinatorial
  `cCodim d 0 = C`: **`codimRepCanonical_fibre_zero_eq_cCodim`** — `codim mult⁻¹(0) = C`. The per-orbit
  lower bound uses the Gabriel→Kostant recovery (`Core.CCodimCornerMono.gabrielPartition`, which at
  corner `0` lands in `kostantPartitions d 0` directly — no corner-monotonicity); the realizer of a
  minimising partition attains it (`Core.ThetaComponentCount.realizerD`).

* **(2,2,2) witness (Proved).** `codimRepCanonical (fibre d222 0) = 3` over `AlgebraicClosure ℚ`, and
  the payoff `rlct(K^DLN_0) = 3/2` over `ℂ` — the geometric reading of `cCodim d222 0 = 3` (LR Ex 4.3).

* **R1 / R2 (Cited interface, name = content).** `RlctInterface` carries the rlct as an opaque map and
  the **Cited** equality `cited_aoyagi_dln` (Aoyagi Thm 1 / Lehalleur–Rimányi Thm 8.6) bridging the
  real-loss rlct to `½·codim mult⁻¹(B)` over the algebraically-closed field where the codimension
  lives. R2 (`rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`) transports through bridge (b) to `C/2`,
  with the interface explicit in the type (the Cited dependency visible) and `via_aoyagi` in the name.
  **This is not an unconditional `rlct = C/2` claim** — the analytic equality is the carried hypothesis
  `I.cited_aoyagi_dln`, not a proved fact (so `#print axioms` on R2 stays `[propext, Classical.choice,
  Quot.sound]`).

**Dependency rule:** `DLN` depends on `Core`; `Core` never imports `DLN`.
-/

namespace DLNFibre.DLN

open Matrix DLNFibre.Core

universe u

/-! ## D2 — the square-Frobenius loss and its zero-set -/

variable {N : ℕ}

/-- The **square-Frobenius DLN loss** `K^DLN_B (A) = ‖mult A − B‖²_F = Tr((mult A − B)ᵀ (mult A − B))`
over ℝ (no prefactor; the rlct is scale-invariant). -/
def lossDLN (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (A : Tuple (k := ℝ) d) : ℝ :=
  ((mult d A - B)ᵀ * (mult d A - B)).trace

/-- The loss is nonnegative: `Tr(MᵀM) ≥ 0` (`MᵀM` is positive semidefinite over ℝ). -/
theorem lossDLN_nonneg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (A : Tuple (k := ℝ) d) :
    0 ≤ lossDLN d B A := by
  have h : (mult d A - B)ᵀ = (mult d A - B)ᴴ := (conjTranspose_eq_transpose_of_trivial _).symm
  rw [lossDLN, h]
  exact (posSemidef_conjTranspose_mul_self _).trace_nonneg

/-- **The loss vanishes exactly on the fibre** `mult⁻¹(B)`: `{A | K^DLN_B(A) = 0} = mult⁻¹(B)`. The
load-bearing zero-set identity, via the Frobenius fact `Tr(MᵀM) = 0 ↔ M = 0`. -/
theorem zeroLocus_lossDLN_eq_fibre (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) :
    {A : Tuple (k := ℝ) d | lossDLN d B A = 0} = fibre d B := by
  ext A
  rw [Set.mem_setOf_eq, lossDLN, mem_fibre,
    show (mult d A - B)ᵀ = (mult d A - B)ᴴ from (conjTranspose_eq_transpose_of_trivial _).symm,
    trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]

/-! ## D3 — the zero-product fibre `mult⁻¹(0) = Σ̄^0` and its geometric codimension

Over a field, the corner-`0` fibre is the closed rank-`≤ 0` product locus, and its geometric
codimension is the minimum codimension over its orbit closures (bridge (a): "codim of a finite union
= min codim of its irreducible components"). -/

section D3

open MvPolynomial Ideal

variable {k : Type u} [Field k]

/-- **The zero-product fibre is the closed rank-`≤ 0` locus** `mult⁻¹(0) = Σ̄^0`: over a field
`rank M = 0 ↔ M = 0`, so `mult A = 0 ↔ rank (mult A) ≤ 0`. -/
theorem fibre_zero_eq_productRankLocusLE_zero (d : Fin (N + 1) → ℕ) :
    fibre (k := k) d 0 = productRankLocusLE (k := k) d 0 := by
  ext A
  rw [mem_fibre, mem_productRankLocusLE, Nat.le_zero]
  constructor
  · intro h; rw [h, Matrix.rank_zero]
  · intro h; exact matrix_eq_zero_of_rank_eq_zero _ h

/-- `codimRepCanonical (mult⁻¹(0))` is the height of the aggregate ideal `sigmaIdeal d 0` of `Σ̄^0`
(definitional, via `fibre_zero_eq_productRankLocusLE_zero`). -/
theorem codimRepCanonical_fibre_zero_eq_height_sigmaIdeal (d : Fin (N + 1) → ℕ) :
    codimRepCanonical (fibre (k := k) d 0)
      = (sigmaIdeal (k := k) d 0).height := by
  rw [fibre_zero_eq_productRankLocusLE_zero]
  rfl

/-- **Bridge (a): `codim` of the zero-product fibre = min `codim` over its orbit closures.** The
geometric codimension of `mult⁻¹(0) = Σ̄^0` equals the infimum, over the corner-`0` orbit closures
`Ō_M`, of their geometric codimensions — "codimension of a finite union is the minimum codimension
of its irreducible components". The height of `sigmaIdeal d 0 = sInf (orbitIdeals d 0)`
(`sigmaIdeal_eq_sInf_orbitIdeals`) is the infimum over its minimal primes
(`minimalPrimes_sigmaIdeal_eq`); each such prime is an orbit ideal, and every orbit ideal contains a
minimal one of `≤` height, so the two infima agree. `[IsAlgClosed k]` (orbit-ideal primality). This
is the **per-orbit** aggregate reading; identifying the infimum with `cCodim d 0` needs the
Kostant-partition encoding bridge (Deferred — see module header). -/
theorem codimRepCanonical_fibre_zero_eq_iInf_orbitCodim [IsAlgClosed k] (d : Fin (N + 1) → ℕ) :
    codimRepCanonical (fibre (k := k) d 0)
      = ⨅ M ∈ {M : Tuple (k := k) d | (mult d M).rank ≤ 0},
          codimRepCanonical (orbitRankLocus M) := by
  rw [codimRepCanonical_fibre_zero_eq_height_sigmaIdeal, Ideal.height]
  -- LHS: ⨅ over minimal primes of `sigmaIdeal d 0`, of primeHeight.
  -- RHS: ⨅ over corner-0 tuples M, of `codimRepCanonical (Ō_M) = (vanishingIdeal Ō_M).height`.
  apply le_antisymm
  · -- every orbit ideal contains a minimal prime of `≤` height ⟹ LHS ≤ each RHS summand
    refine le_iInf₂ (fun M hM ↦ ?_)
    have hmem : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M)) ∈ orbitIdeals (k := k) d 0 := ⟨M, hM, rfl⟩
    have hle : sigmaIdeal (k := k) d 0
        ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus M) := by
      rw [sigmaIdeal_eq_sInf_orbitIdeals]; exact sInf_le hmem
    haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
        (canonicalCoord d '' orbitRankLocus M)).IsPrime :=
      isPrime_vanishingIdeal_orbitRankLocus M
    obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le hle
    haveI := Ideal.minimalPrimes_isPrime hp
    calc ⨅ J ∈ (sigmaIdeal (k := k) d 0).minimalPrimes,
            @Ideal.primeHeight _ _ J (Ideal.minimalPrimes_isPrime ‹_›)
        ≤ p.primeHeight := by
          refine iInf₂_le_of_le p hp ?_
          exact le_of_eq (by congr)
      _ ≤ _ := by
          rw [← Ideal.height_eq_primeHeight]
          exact (Ideal.height_mono hple).trans_eq
            (codimRepCanonical_orbitRankLocus_eq_height d M).symm
  · -- each minimal prime IS an orbit ideal ⟹ RHS ≤ LHS
    refine le_iInf₂ (fun J hJ ↦ ?_)
    haveI := Ideal.minimalPrimes_isPrime hJ
    -- J is a minimal prime, hence in orbitIdeals (minimalPrimes_sigmaIdeal_eq), so J = Ō_M's ideal
    have hJfam : J ∈ orbitIdeals (k := k) d 0 := by
      have := (minimalPrimes_sigmaIdeal_eq (k := k) d 0).symm ▸ hJ
      exact ((minimalPrimes_sigmaIdeal_eq (k := k) d 0) ▸ hJ).1
    obtain ⟨M, hM, rfl⟩ := hJfam
    refine iInf₂_le_of_le M hM ?_
    rw [codimRepCanonical_orbitRankLocus_eq_height, Ideal.height_eq_primeHeight]

/-! ### Bridge (b) — the orbit-codim infimum equals the combinatorial `C` (r = 0)

For corner-`0` the Gabriel→Kostant recovery is unconditional (a corner-`0` orbit's Gabriel partition
*is* a corner-`0` Kostant partition — no corner-monotonicity needed), so the per-orbit codimension is
bounded below by `cCodim d 0`; the realizer of the minimising partition attains it. Hence the
geometric codimension of `mult⁻¹(0)` equals the combinatorial `C = cCodim d 0`. -/

/-- **Per-orbit lower bound (r = 0).** Every corner-`0` orbit closure has geometric codimension at
least `cCodim d 0`: its Gabriel partition is a corner-`0` Kostant partition realising the same orbit,
and `codimForm` of any Kostant partition is `≥ cCodim`. (At `r = 0` the Gabriel partition's corner is
the product rank `= 0` directly — no corner-monotonicity argument is needed.) -/
theorem cCodim_le_codimRepCanonical_orbitRankLocus_of_rank_le_zero
    [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ)
    (h : (kostantPartitions d 0).Nonempty) (M : Tuple (k := k) d) (hM : (mult d M).rank ≤ 0) :
    ((cCodim d 0 h).toNat : ℕ∞) ≤ codimRepCanonical (orbitRankLocus M) := by
  have hrank : (mult d M).rank = 0 := Nat.le_zero.mp hM
  -- the Gabriel partition of M is a corner-0 Kostant partition realising Ō_M
  have hmem : gabrielPartition d M ∈ kostantPartitions d 0 := by
    have := gabrielPartition_mem d M; rwa [hrank] at this
  -- `codimForm (extendℤ (gabrielPartition M)) ≥ cCodim d 0`
  have hge : cCodim d 0 h ≤ codimForm N (extendℤ (gabrielPartition d M)) :=
    Finset.inf'_le _ hmem
  -- `codimRepCanonical(Ō_M).toNat = codimForm(extendℤ (gabrielPartition M))`
  have hval : ((codimRepCanonical (orbitRankLocus M)).toNat : ℤ)
      = codimForm N (extendℤ (gabrielPartition d M)) := by
    rw [← orbitRankLocus_realizerD_gabrielPartition d M,
      codimRepCanonical_orbitRankLocus_realizerD (gabrielPartition_mem d M)]
  -- transport the bound to ℕ∞, using finiteness of the height (finite Krull dim)
  have hfin : codimRepCanonical (orbitRankLocus M) ≠ ⊤ := by
    rw [codimRepCanonical_orbitRankLocus_eq_height]
    exact Ideal.height_ne_top (isPrime_vanishingIdeal_orbitRankLocus M).ne_top
  have hnn : 0 ≤ cCodim d 0 h := by
    rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
    exact fun m' _ ↦ Int.natCast_nonneg _
  have : (cCodim d 0 h).toNat ≤ (codimRepCanonical (orbitRankLocus M)).toNat := by
    have h1 : (cCodim d 0 h).toNat ≤ codimForm N (extendℤ (gabrielPartition d M)) := by
      omega
    omega
  calc ((cCodim d 0 h).toNat : ℕ∞)
      ≤ ((codimRepCanonical (orbitRankLocus M)).toNat : ℕ∞) := by exact_mod_cast this
    _ = codimRepCanonical (orbitRankLocus M) := ENat.coe_toNat hfin

/-- The geometric codimension of `mult⁻¹(0)` as an `ℕ∞` equals the combinatorial `C = cCodim d 0`:
both inequalities come from bridge (a) — the per-orbit lower bound and the realizer of a minimising
Kostant partition attaining the minimum. -/
theorem codimRepCanonical_fibre_zero_eq_cCodim_enat [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (h : (kostantPartitions d 0).Nonempty) :
    codimRepCanonical (fibre (k := k) d 0) = ((cCodim d 0 h).toNat : ℕ∞) := by
  rw [codimRepCanonical_fibre_zero_eq_iInf_orbitCodim]
  apply le_antisymm
  · -- ≤ : the realizer of a minimising partition is a corner-0 orbit attaining `C`
    obtain ⟨m₀, hm₀, hval⟩ := Finset.exists_mem_eq_inf' h (fun m ↦ codimForm N (extendℤ m))
    have hcorner : (mult d (realizerD (k := k) hm₀)).rank ≤ 0 := by
      rw [rank_mult_realizerD hm₀]
    have hreal : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))
        = ((cCodim d 0 h).toNat : ℕ∞) := by
      have hfin : codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀)) ≠ ⊤ := by
        rw [codimRepCanonical_orbitRankLocus_eq_height]
        exact Ideal.height_ne_top
          (isPrime_vanishingIdeal_orbitRankLocus (realizerD (k := k) hm₀)).ne_top
      have hnn : 0 ≤ cCodim d 0 h := by
        rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
        exact fun m' _ ↦ Int.natCast_nonneg _
      have hceq : cCodim d 0 h = codimForm N (extendℤ m₀) := hval
      have htn : ((codimRepCanonical (orbitRankLocus (realizerD (k := k) hm₀))).toNat : ℤ)
          = (cCodim d 0 h).toNat := by
        rw [codimRepCanonical_orbitRankLocus_realizerD hm₀, hceq]
        omega
      rw [← ENat.coe_toNat hfin]
      exact_mod_cast htn
    refine iInf₂_le_of_le (realizerD (k := k) hm₀) hcorner ?_
    rw [hreal]
  · -- ≥ : every corner-0 orbit codim is ≥ C (the per-orbit lower bound)
    exact le_iInf₂ (fun M hM ↦ cCodim_le_codimRepCanonical_orbitRankLocus_of_rank_le_zero d h M hM)

/-- **Bridge (b): `codim mult⁻¹(0) = C`.** The geometric codimension of the zero-product fibre
`mult⁻¹(0) = Σ̄^0` equals the combinatorial codimension `cCodim d 0 = C` (Lehalleur–Rimányi's `C`).
The per-orbit lower bound (Gabriel→Kostant recovery, unconditional at `r = 0`) and the realizer of a
minimising Kostant partition pin the orbit-codim infimum (bridge (a)) to `C`. `[IsAlgClosed k]
[CharZero k]` (the Voigt-discharge scope where `C` is the geometric codimension). -/
theorem codimRepCanonical_fibre_zero_eq_cCodim [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (h : (kostantPartitions d 0).Nonempty) :
    ((codimRepCanonical (fibre (k := k) d 0)).toNat : ℤ) = cCodim d 0 h := by
  rw [codimRepCanonical_fibre_zero_eq_cCodim_enat d h, ENat.toNat_coe]
  have hnn : 0 ≤ cCodim d 0 h := by
    rw [cCodim_eq_inf_geomCodim (k := k), Finset.le_inf'_iff]
    exact fun m' _ ↦ Int.natCast_nonneg _
  omega

end D3

/-! ## R — the RLCT payoff through a Cited analytic interface

The real log-canonical threshold (rlct) is a **real-analytic** invariant of the loss; it is not in
Mathlib, and the DLN equality `rlct(K^DLN_B) = ½·codim mult⁻¹(B)` is **Aoyagi's analytic theorem**
(Aoyagi Thm 1 / Lehalleur–Rimányi Thm 8.6), not a geometric consequence of the codimension. We carry
it as a **Cited interface**: an opaque `rlct` map plus the equality as a structure FIELD
`cited_aoyagi_dln` (a hypothesis, NOT a global axiom), so the Cited content is visible in every type
that depends on it and `#print axioms` on the payoff stays clean.

**Field interplay (the one subtlety).** The loss lives over ℝ; the geometric codimension `C`
(`codimRepCanonical` / `cCodim`) lives over an algebraically-closed char-`0` field `K` (the scope of
the Voigt discharge). The interface carries `K`, a ring embedding `ι : ℝ →+* K`, and bridges the
real-loss rlct to the codimension of the base-changed fibre `mult⁻¹(B.map ι)` over `K` — exactly the
real↔complex passage that is part of what Aoyagi Cites. No from-scratch real↔complex codimension
base-change lemma is needed. -/

section R

open MvPolynomial

universe v

/-- **The Cited DLN rlct interface (Aoyagi Thm 1 / Lehalleur–Rimányi Thm 8.6).** An ASSUMED analytic
interface, not proved here: an opaque real-log-canonical-threshold map `rlct` on ℝ-losses, together
with the **Cited** equality `cited_aoyagi_dln` bridging the rlct of the DLN square-Frobenius loss to
half the geometric codimension of the multiplication fibre, computed over the algebraically-closed
char-`0` field `K` (via the embedding `ι : ℝ →+* K`). The equality stops at `½·codim mult⁻¹(B)` — so
the payoff R2 is genuine transport into the zero-product codimension, not a restatement. The field
`cited_aoyagi_dln` is a carried hypothesis (NOT a global `axiom`); the Cited dependency is visible in
any type using this structure. -/
structure RlctInterface (d : Fin (N + 1) → ℕ)
    (K : Type v) [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K) where
  /-- The opaque real log-canonical threshold of a (real) loss function on `Rep_d`. -/
  rlct : (Tuple (k := ℝ) d → ℝ) → ℝ
  /-- **Cited (Aoyagi Thm 1 / LR Thm 8.6):** the rlct of the DLN loss `K^DLN_B` equals half the
  geometric codimension of the multiplication fibre `mult⁻¹(B)` (base-changed to `K`). Assumed
  analytic content, not a proved fact. -/
  cited_aoyagi_dln : ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ),
    B.rank = r → r ≤ (Finset.univ.inf' Finset.univ_nonempty d) →
    rlct (lossDLN d B)
      = ((codimRepCanonical (fibre (k := K) d (B.map ι))).toNat : ℝ) / 2

variable {d : Fin (N + 1) → ℕ}
  {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

/-- **The RLCT payoff at `r = 0`, through the Cited Aoyagi interface.** Given the Cited interface `I`,
the rlct of the zero-product DLN loss `K^DLN_0` equals half the geometric codimension of the
zero-product fibre `mult⁻¹(0) = Σ̄^0` (over `K`). The interface `I : RlctInterface …` is an explicit
hypothesis — the Cited dependency is visible in the type — and `via_aoyagi` names the source; this is
**not** an unconditional `rlct = ½·codim`. From `I.cited_aoyagi_dln` at `B = 0`, `r = 0`, using
`(0).map ι = 0`. -/
theorem rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi (I : RlctInterface d K ι) :
    I.rlct (lossDLN d 0)
      = ((codimRepCanonical (fibre (k := K) d 0)).toNat : ℝ) / 2 := by
  have hmap : (0 : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ).map ι = 0 :=
    Matrix.map_zero ι ι.map_zero
  rw [I.cited_aoyagi_dln 0 0 Matrix.rank_zero (Nat.zero_le _), hmap]

/-- **The RLCT payoff at `r = 0` against the orbit-codim infimum (bridge (a)).** Combining the payoff
with bridge (a) (`codimRepCanonical_fibre_zero_eq_iInf_orbitCodim`): the rlct of `K^DLN_0` is half the
minimum geometric codimension over the corner-`0` orbit closures. The `cCodim`-form (that this infimum
*is* `C`) is `rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`, through bridge (b). -/
theorem rlct_lossDLN_zero_eq_half_iInf_orbitCodim_via_aoyagi (I : RlctInterface d K ι) :
    I.rlct (lossDLN d 0)
      = ((⨅ M ∈ {M : Tuple (k := K) d | (mult d M).rank ≤ 0},
            codimRepCanonical (orbitRankLocus M)).toNat : ℝ) / 2 := by
  rw [rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi I,
    codimRepCanonical_fibre_zero_eq_iInf_orbitCodim]

/-- **The RLCT payoff at `r = 0`: `rlct(K^DLN_0) = C/2`, through the Cited Aoyagi interface.** Given
the Cited interface `I`, the rlct of the zero-product DLN loss equals half the combinatorial
codimension `cCodim d 0 = C` (Lehalleur–Rimányi's `C`) — "DLNs are mildly singular". Combines the
Cited interface (R2, `rlct = ½·codim mult⁻¹(0)`) with bridge (b)
(`codimRepCanonical_fibre_zero_eq_cCodim`, the geometric content `codim mult⁻¹(0) = C`). The interface
`I` is an explicit hypothesis — the Cited analytic dependency is visible in the type — and
`via_aoyagi` names the source; this is **not** an unconditional `rlct = C/2`. Requires the Kostant
set nonempty (`h`); `[IsAlgClosed K] [CharZero K]` (the scope where `C` is the geometric codimension). -/
theorem rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi (I : RlctInterface d K ι)
    (h : (kostantPartitions d 0).Nonempty) :
    I.rlct (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 := by
  rw [rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi I]
  have hnat : (codimRepCanonical (fibre (k := K) d 0)).toNat = (cCodim d 0 h).toNat := by
    have := codimRepCanonical_fibre_zero_eq_cCodim (k := K) d h
    omega
  rw [hnat]

end R

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 0`

The worked example `d = (2,2,2)` (Lehalleur–Rimányi Ex 4.3): the combinatorial `C = cCodim d222 0 = 3`
(LANDED `Core.CTheta.cCodim_d222_zero`). Over the algebraically-closed char-`0` field, bridge (b)
turns this into the geometric codimension of the zero-product fibre, and the Cited interface into the
RLCT value `3/2`. The codimension side is shown over `AlgebraicClosure ℚ`; the rlct payoff over `ℂ`
(which carries the embedding `ℝ →+* ℂ` the interface needs — there is no ring hom `ℝ →+* ℚ̄`). -/

section Witness

open scoped Classical

/-- **`(2,2,2)`, `r = 0`: the geometric codimension of `mult⁻¹(0)` is `3`**, over `AlgebraicClosure ℚ`
— the geometric reading of the combinatorial `C = cCodim d222 0 = 3` (LR Ex 4.3), via bridge (b). -/
theorem codimRepCanonical_fibre_d222_zero :
    (codimRepCanonical (fibre (k := AlgebraicClosure ℚ) Core.d222 0)).toNat = 3 := by
  have h := codimRepCanonical_fibre_zero_eq_cCodim (k := AlgebraicClosure ℚ) Core.d222
    Core.kostantPartitions_d222_nonempty
  rw [Core.cCodim_d222_zero] at h
  omega

/-- **`(2,2,2)`, `r = 0`: the RLCT payoff `rlct(K^DLN_0) = 3/2`**, over `ℂ`, through the Cited Aoyagi
interface. `C = 3` (LR Ex 4.3), so `rlct = C/2 = 3/2`: the `(2,2,2)` zero-product DLN is mildly
singular. The interface `I` is the explicit Cited hypothesis. -/
theorem rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi
    (I : RlctInterface Core.d222 ℂ Complex.ofRealHom) :
    I.rlct (lossDLN Core.d222 0) = 3 / 2 := by
  rw [rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi I Core.kostantPartitions_d222_nonempty,
    Core.cCodim_d222_zero, show ((3 : ℤ).toNat : ℝ) = 3 from rfl]

end Witness

end DLNFibre.DLN
