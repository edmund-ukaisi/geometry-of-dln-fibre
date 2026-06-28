import DLNFibre.Core.Setup
import DLNFibre.Core.SigmaComponents
import DLNFibre.Core.CThetaGeometric
import DLNFibre.Core.CTheta
import DLNFibre.Core.ThetaComponentCount
import DLNFibre.Core.CCodimCornerMono
import DLNFibre.Core.RadicalCatenary
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.DLN.RlctPayoff` — the square-Frobenius loss, its zero-set, and the RLCT payoff (r = 0)

The application layer (`DLNFibre.DLN`, consuming `Core`): the deep-linear-network square-Frobenius
loss `K^DLN_B`, its zero-set (the multiplication fibre `mult⁻¹(B)`), the geometric codimension of
the zero-product fibre at corner `r = 0`, and the real-log-canonical-threshold payoff
`rlct(K^DLN_0) = ½·codim mult⁻¹(0)` through a **minimal Cited** analytic interface (two bounds) plus a
**named Cited real-vs-complex transfer** `T` (`codim_ℝ = codim_K`, reducing to the atomic real-dim =
complex-dim equality via the proved catenary — see `codimRealFibre_eq_codimRepCanonical_of_dimTransfer`).

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

* **R (Cited bounds + Cited transfer + Proved geometry, name = content).**
  `RlctRealInterface` carries the rlct as an opaque map and the **minimal Cited** analytic content as
  TWO bounds — the universal Watanabe upper bound `rlct ≤ ½·codim_ℝ` (unconditional) and the
  DLN-specific Aoyagi lower bound `½·codim_ℝ ≤ rlct` (`0 < N`, Aoyagi Thm 1 / LR Thm 8.6) — both about
  `codim_ℝ`, the codimension of the loss's **real** zero-set (`codimRealFibre`, the real fibre
  `mult⁻¹(B)`). Their `le_antisymm` gives the analytic equality `rlct = ½·codim_ℝ`
  (`rlct_lossDLN_eq_half_codimRealFibre`). The passage to the codimension `C` over the
  algebraically-closed `K` factors as: the **transfer** `T : codim_ℝ = codim_K` (a **Cited**
  real-vs-complex fact `hT`, reducing to the atomic real-dim = complex-dim equality via the proved
  catenary `codimRealFibre_eq_codimRepCanonical_of_dimTransfer`), then bridge (b) `codim_K = C`
  (Proved). So the payoff theorems (`rlct_lossDLN_…_via_aoyagi`) carry `I`, `hT` explicit in the
  type — `via_aoyagi` names the cited source, `hT` names the cited transfer; **not** an unconditional
  `rlct = C/2`. The cited boundary is honestly `{cited_watanabe_upper, cited_aoyagi_lower, T}` (three
  named atomic cited facts); everything else (catenary, `codim_K = C`) is Proved, and `#print axioms`
  on the payoffs stays `[propext, Classical.choice, Quot.sound]`.

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
is the **per-orbit** aggregate reading; identifying the infimum with `cCodim d 0` is bridge (b)
(`codimRepCanonical_fibre_zero_eq_cCodim`, the Kostant-partition encoding, Proved below). -/
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

/-! ## R — the RLCT payoff: cite only the analytic `rlct = ½·codim_ℝ`, prove the geometry

The real log-canonical threshold (rlct) is a **real-analytic** invariant of the loss; it is not in
Mathlib. We cite the **minimal** analytic content — the two bounds bracketing the rlct of a real
square-Frobenius loss between `½·codim_ℝ` of its real zero-set — and **prove** the geometry up to it.

The honest decomposition (what the monolith's single `rlct = ½·codim_K` field silently fused):
1. the **analytic** bracket `½·codim_ℝ ≤ rlct ≤ ½·codim_ℝ` (Cited: Watanabe's universal upper bound,
   Aoyagi's DLN-specific lower bound), where `codim_ℝ` is the codimension of the **real** zero-set;
2. the **connector** (`lossDLN`'s zero-set is the real fibre `mult⁻¹(B)`,
   `zeroLocus_lossDLN_eq_fibre`) — Proved above;
3. the **transfer `T`** `codim_ℝ(real fibre) = codim_K(complex fibre)` — a **Cited** real-vs-complex
   fact (a named *hypothesis*, not a global axiom): true (the smooth full-dim real points of the top
   components, e.g. the rational realizers `realizerD`, make the real points Zariski-dense so the real
   dimension equals the complex one), but not bounded-provable at this Mathlib pin. It reduces to the
   **atomic** real-dim = complex-dim equality via the proved catenary
   (`codimRealFibre_eq_codimRepCanonical_of_dimTransfer`), so the irreducible cited content is that
   dimension equality; the codim form `T` is its convenient consumer-facing shape.

So the **cited** boundary here is exactly `{cited_watanabe_upper, cited_aoyagi_lower, T}`; everything
else — the connector, the catenary reduction, and bridge (b) `codim_K = C` — is Proved. -/

section R

open MvPolynomial

universe v

variable {d : Fin (N + 1) → ℕ}

/-- **The real-locus codimension of the multiplication fibre** `codim_ℝ mult⁻¹(B)`. *Definitionally*
`codimRepCanonical (k := ℝ) (fibre ℝ d B)` — the field-parametric geometric-codimension definition
evaluated at `ℝ`, i.e. the `Ideal.height` of the vanishing ideal of the **real points** of the fibre.

**This is the BARE real-locus codimension; it carries NONE of the algebraically-closed geometry of
`codimRepCanonical` over `K`.** Over a non-algebraically-closed field the height of the real-points
vanishing ideal need not equal the complex geometric codimension; bridging the two is the transfer `T`
(the `hT` hypothesis of `rlct_lossDLN_eq_half_codimFibre_of_transfer`), a **Cited** real-algebraic-
geometry fact — NOT something `codim_ℝ` knows. (Discriminator: the real zero-set of `x² + y²` is the
point `{0}`, real codim `2`, matching `height (vanishingIdeal ℝ {0}) = height (x, y) = 2`; the
generator-ideal height `height (x² + y²) = 1` would be the *wrong* number, which is why `codim_ℝ` is
the vanishing-ideal-of-real-points height — the meaning `codimRepCanonical (k := ℝ)` already has.) The
transfer `T` reduces to the atomic real-dim = complex-dim equality via the catenary
(`codimRealFibre_eq_codimRepCanonical_of_dimTransfer`), so the cited content is just that dim equality. -/
noncomputable abbrev codimRealFibre (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) : ℕ∞ :=
  codimRepCanonical (k := ℝ) (fibre (k := ℝ) d B)

/-- **The zero-product real fibre is nonempty** (the zero tuple lands in it, for `0 < N`): for a
genuine deep network `mult d 0 = 0` (the last layer factor `A_{N−1} = 0` zeroes the product), so
`0 ∈ mult⁻¹(0)`. Used to discharge the catenary's nonemptiness for the `r = 0` transfer reduction. -/
theorem fibre_zero_nonempty (hN : 0 < N) (d : Fin (N + 1) → ℕ) :
    (fibre (k := ℝ) d (0 : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ)).Nonempty := by
  refine ⟨0, ?_⟩
  rw [mem_fibre]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  unfold mult
  rw [show (Fin.last (M + 1)) = (Fin.last M).succ from rfl, multPrefix_succ, Pi.zero_apply,
    Matrix.zero_mul]

/-- **The Cited DLN rlct interface — the minimal analytic content.** An opaque
real-log-canonical-threshold map `rlct` on ℝ-losses, together with the **two Cited bounds** bracketing
the rlct of the real square-Frobenius DLN loss between `½·codim_ℝ` of its real zero-set (the real
fibre `mult⁻¹(B)`). Both fields are carried hypotheses (NOT global `axiom`s); the Cited dependency is
visible in any type using this structure.

The two bounds carry **different status** (name = content):
* `cited_watanabe_upper` is the **universal** Watanabe inequality `rlct ≤ ½·codim_ℝ` — true for *any*
  real loss, with no network/scope guard;
* `cited_aoyagi_lower` is the **DLN-specific** matching lower bound `½·codim_ℝ ≤ rlct` (Aoyagi Thm 1 =
  Lehalleur–Rimányi Thm 8.6), guarded by `0 < N` (the genuine-deep-network scope where it holds).

The interface stops at `codim_ℝ` (the **real** codimension); the passage to the geometric codimension
over an algebraically-closed `K` is the transfer `T` (a Cited real-vs-complex fact, reducing to the
atomic real-dim = complex-dim equality), supplied as a separate hypothesis to the payoff theorems —
NOT a field of this *analytic* interface, since it is real-algebraic geometry, not real analysis. -/
structure RlctRealInterface (d : Fin (N + 1) → ℕ) where
  /-- The opaque real log-canonical threshold of a (real) loss function on `Rep_d`. -/
  rlct : (Tuple (k := ℝ) d → ℝ) → ℝ
  /-- **Cited (Watanabe, universal — no scope guard):** the rlct of any real square-Frobenius DLN loss
  is at most half the codimension of its real zero-set (the real fibre `mult⁻¹(B)`). Watanabe's
  universal log-canonical-threshold upper bound `λ ≤ codim_ℝ / 2`; assumed analytic content. -/
  cited_watanabe_upper : ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ),
    rlct (lossDLN d B) ≤ ((codimRealFibre d B).toNat : ℝ) / 2
  /-- **Cited (Aoyagi Thm 1 / LR Thm 8.6, scope `0 < N`):** for a genuine deep network, the rlct of the
  real square-Frobenius DLN loss is at least half the codimension of its real zero-set (the real fibre
  `mult⁻¹(B)`) — the DLN-specific matching lower bound. Assumed analytic content. The `0 < N` guard is
  the scope of Aoyagi's theorem (an `N ≥ 1` deep linear network); at `N = 0` the "product" `mult` is the
  empty product and the statement is outside the cited scope. -/
  cited_aoyagi_lower : ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ),
    0 < N → ((codimRealFibre d B).toNat : ℝ) / 2 ≤ rlct (lossDLN d B)

variable {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

/-- **The transfer reduces to the atomic real-dim = complex-dim equality (catenary).** Given the
**atomic** cited fact `hdim : varietyDim(real fibre) = varietyDim(complex fibre)` (the real-locus
dimension equals the complex variety dimension — the real-radical-density content, the smallest honest
cited piece) and both fibres nonempty, the codimension transfer `codim_ℝ = codim_K` is **PROVED** here:
the field-generic catenary `codimRepCanonical + varietyDim = card (RepCoord d)` holds over each field,
the ambient `card` is field-independent, and cancelling the equal `varietyDim`s gives the codimensions
equal. So the cited boundary is the atomic dim-transfer `hdim`, not the codim equality — the latter is
derived. (`x² + y²`: a rational point per component is NOT enough — `hdim` needs a *smooth full-dim*
real point per top component; cf. the `codimRealFibre` docstring's discriminator.) -/
theorem codimRealFibre_eq_codimRepCanonical_of_dimTransfer
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ)
    (hRne : (fibre (k := ℝ) d B).Nonempty)
    (hKne : (fibre (k := K) d (B.map ι)).Nonempty)
    (hdim : varietyDim (canonicalCoord d '' (fibre (k := ℝ) d B))
      = varietyDim (canonicalCoord d '' (fibre (k := K) d (B.map ι)))) :
    codimRealFibre d B = codimRepCanonical (k := K) (fibre (k := K) d (B.map ι)) := by
  have hR := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := ℝ)
    (hRne.image (canonicalCoord d))
  have hK := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := K)
    (hKne.image (canonicalCoord d))
  rw [hdim] at hR
  -- `hR : codim_ℝ + vdim_K = card`, `hK : codim_K + vdim_K = card`; cancel the finite `vdim_K`.
  have hfin : varietyDim (canonicalCoord d '' (fibre (k := K) d (B.map ι))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (hK ▸ le_add_self)
  exact WithTop.add_right_cancel hfin (hR.trans hK.symm)

/-- **`rlct = ½·codim_ℝ`, the analytic equality (from the two Cited bounds).** `le_antisymm` of the
universal Watanabe upper bound and the DLN-specific Aoyagi lower bound: the rlct of the real DLN loss
`K^DLN_B` equals half the codimension of its real zero-set (the real fibre `mult⁻¹(B)`). This is the
purely-analytic half — no transfer to `K`, no combinatorics; the geometric passage is `…_of_transfer`.
The `0 < N` guard is the Cited scope of the (DLN-specific) lower bound. -/
theorem rlct_lossDLN_eq_half_codimRealFibre (I : RlctRealInterface d) (hN : 0 < N)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) :
    I.rlct (lossDLN d B) = ((codimRealFibre d B).toNat : ℝ) / 2 :=
  le_antisymm (I.cited_watanabe_upper B) (I.cited_aoyagi_lower B hN)

/-- **The DLN RLCT payoff `rlct(K^DLN_B) = ½·codim mult⁻¹(B)` (over `K`), via the transfer `T`.**
The analytic equality `rlct = ½·codim_ℝ` (the two Cited bounds) composed with the transfer
`hT : codim_ℝ(real fibre) = codim_K(complex fibre)`. `hT` is the **Cited** real-vs-complex transfer
(real-radical density — true, but not bounded-provable at this Mathlib pin: no real-Nullstellensatz /
semialgebraic dimension), visible in the type next to the rlct claim. It is the codim-level form of the
**atomic** real-dim = complex-dim fact, from which it is DERIVED by the proved catenary reduction
`codimRealFibre_eq_codimRepCanonical_of_dimTransfer` — so the irreducible cited content is that atomic
dimension equality (caveat: a rational point per component is not enough — need a smooth full-dim real
point per top component, x²+y² style; PROOF roadmapped to a future expedition, cf. rlct-runway-target).
This recovers the monolith's old `cited_aoyagi_dln` shape as a DERIVED theorem; the cited boundary is
now `{cited_watanabe_upper, cited_aoyagi_lower, T}`. The `0 < N` guard is the Cited (lower-bound) scope. -/
theorem rlct_lossDLN_eq_half_codimFibre_of_transfer (I : RlctRealInterface d) (hN : 0 < N)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ)
    (hT : codimRealFibre d B = codimRepCanonical (k := K) (fibre (k := K) d (B.map ι))) :
    I.rlct (lossDLN d B)
      = ((codimRepCanonical (fibre (k := K) d (B.map ι))).toNat : ℝ) / 2 := by
  rw [rlct_lossDLN_eq_half_codimRealFibre I hN B, hT]

/-- **The RLCT payoff at `r = 0`, modulo the transfer `T`.** The rlct of the zero-product DLN loss
`K^DLN_0` equals half the geometric codimension of the zero-product fibre `mult⁻¹(0) = Σ̄^0` (over `K`),
given the analytic interface `I` and the transfer `hT` at `B = 0`. `via_aoyagi` names the cited source;
this is **not** an unconditional `rlct = ½·codim`. The `0 < N` guard is the Cited (lower-bound) scope. -/
theorem rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi (I : RlctRealInterface d) (hN : 0 < N)
    (hT : codimRealFibre d (0 : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ)
      = codimRepCanonical (k := K) (fibre (k := K) d 0)) :
    I.rlct (lossDLN d 0)
      = ((codimRepCanonical (fibre (k := K) d 0)).toNat : ℝ) / 2 := by
  rw [rlct_lossDLN_eq_half_codimRealFibre I hN 0, hT]

/-- **The RLCT payoff at `r = 0` against the orbit-codim infimum (bridge (a)), modulo the transfer.**
Combining the `r = 0` payoff with bridge (a) (`codimRepCanonical_fibre_zero_eq_iInf_orbitCodim`): the
rlct of `K^DLN_0` is half the minimum geometric codimension over the corner-`0` orbit closures. The
`cCodim`-form (that this infimum *is* `C`) is `rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`, through
bridge (b). The `0 < N` guard is the Cited (lower-bound) scope. -/
theorem rlct_lossDLN_zero_eq_half_iInf_orbitCodim_via_aoyagi (I : RlctRealInterface d) (hN : 0 < N)
    (hT : codimRealFibre d (0 : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ)
      = codimRepCanonical (k := K) (fibre (k := K) d 0)) :
    I.rlct (lossDLN d 0)
      = ((⨅ M ∈ {M : Tuple (k := K) d | (mult d M).rank ≤ 0},
            codimRepCanonical (orbitRankLocus M)).toNat : ℝ) / 2 := by
  rw [rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi (K := K) I hN hT,
    codimRepCanonical_fibre_zero_eq_iInf_orbitCodim]

/-- **The RLCT payoff at `r = 0`: `rlct(K^DLN_0) = C/2`, modulo the transfer.** The rlct of the
zero-product DLN loss equals half the combinatorial codimension `cCodim d 0 = C` (Lehalleur–Rimányi's
`C`) — "DLNs are mildly singular". Combines the analytic equality + transfer (`rlct = ½·codim_K`) with
bridge (b) (`codimRepCanonical_fibre_zero_eq_cCodim`, the geometric content `codim mult⁻¹(0) = C`,
Proved). `via_aoyagi` names the cited source; this is **not** an unconditional `rlct = C/2`. Requires
the Kostant set nonempty (`h`) and the `0 < N` Cited scope; `[IsAlgClosed K] [CharZero K]` (the scope
where `C` is the geometric codimension). -/
theorem rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi (I : RlctRealInterface d) (hN : 0 < N)
    (hT : codimRealFibre d (0 : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ)
      = codimRepCanonical (k := K) (fibre (k := K) d 0))
    (h : (kostantPartitions d 0).Nonempty) :
    I.rlct (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 := by
  rw [rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi (K := K) I hN hT]
  have hnat : (codimRepCanonical (fibre (k := K) d 0)).toNat = (cCodim d 0 h).toNat := by
    have := codimRepCanonical_fibre_zero_eq_cCodim (k := K) d h
    omega
  rw [hnat]

end R

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 0`

The worked example `d = (2,2,2)` (Lehalleur–Rimányi Ex 4.3): the combinatorial `C = cCodim d222 0 = 3`
(LANDED `Core.CTheta.cCodim_d222_zero`). Over the algebraically-closed char-`0` field, bridge (b)
turns this into the geometric codimension of the zero-product fibre, and the Cited interface + the
transfer `T` into the RLCT value `3/2`. The codimension side is shown over `AlgebraicClosure ℚ`; the
rlct payoff over `ℂ` (which carries the embedding `ℝ →+* ℂ` the transfer needs — there is no ring hom
`ℝ →+* ℚ̄`). -/

section Witness

/-- **`(2,2,2)`, `r = 0`: the geometric codimension of `mult⁻¹(0)` is `3`**, over `AlgebraicClosure ℚ`
— the geometric reading of the combinatorial `C = cCodim d222 0 = 3` (LR Ex 4.3), via bridge (b). -/
theorem codimRepCanonical_fibre_d222_zero :
    (codimRepCanonical (fibre (k := AlgebraicClosure ℚ) Core.d222 0)).toNat = 3 := by
  have h := codimRepCanonical_fibre_zero_eq_cCodim (k := AlgebraicClosure ℚ) Core.d222
    Core.kostantPartitions_d222_nonempty
  rw [Core.cCodim_d222_zero] at h
  omega

/-- **`(2,2,2)`, `r = 0`: the RLCT payoff `rlct(K^DLN_0) = 3/2`**, over `ℂ`, through the two Cited
analytic bounds and the Cited transfer `hT`. `C = 3` (LR Ex 4.3), so `rlct = C/2 = 3/2`: the `(2,2,2)`
zero-product DLN is mildly singular. `(2,2,2)` has `N = 2 > 0`, so the `0 < N` Cited-scope guard is
met. `I` is the explicit Cited analytic interface; `hT` is the explicit Cited transfer (`codim_ℝ =
codim_ℂ` at `(2,2,2)`, `B = 0`; for this `B = 0` the real fibre is nonempty via `fibre_zero_nonempty`,
so the catenary reduction to the atomic dim-transfer applies). -/
theorem rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi
    (I : RlctRealInterface Core.d222)
    (hT : codimRealFibre Core.d222 (0 : Matrix (Fin (Core.d222 (Fin.last 2))) (Fin (Core.d222 0)) ℝ)
      = codimRepCanonical (k := ℂ) (fibre (k := ℂ) Core.d222 0)) :
    I.rlct (lossDLN Core.d222 0) = 3 / 2 := by
  rw [rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi (K := ℂ) I (by norm_num)
      hT Core.kostantPartitions_d222_nonempty,
    Core.cCodim_d222_zero, show ((3 : ℤ).toNat : ℝ) = 3 from rfl]

end Witness

end DLNFibre.DLN
