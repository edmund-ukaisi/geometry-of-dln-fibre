import DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestGermCharge` — the conditional germ-charge bridge

The producer `framedParams_split_eq_frame_raw` (`DeepestGaugeConstruction`) reduces the folded core
(d')/(e') of its loss squeeze to a SINGLE germ charge:

    ∃ C ≥ 0, ∀ᶠ w in 𝓝 w0, |frobSq (Rcore w) − coreΦ w| ≤ C · Sreg w

with `Rcore w` the GLOBAL (1,1)-block Schur complement of `Mw := reindex(P0·(prod(A w) − B)·QL)`,
`coreΦ w = deepestCoreF (deepestCoreAbsorb (split w)).2.1`, and `Sreg w` the three regular-block
energies. This module supplies the ABSTRACT, network-free derivation of that germ charge from the
named ingredients — isolating the remaining UNBUILT geometry as exactly those ingredients.

The genuinely new matrix-algebra piece, the frame-free two-layer LDU
`schur_product_ldu` (`DeepestSchurComparability`), supplies the per-`w` factorization hypothesis `hR`.
What `germ_charge_of_schur_factorization` does NOT discharge (and what the producer's residual `sorry`
still carries) is the frame-aware identification of `Mw`'s `toBlocks` with a per-layer block product
`(fromBlocks A0 Y0 Z0 T0)·(fromBlocks A1 Y1 Z1 T1)` (so `schur_product_ldu` applies), the match of
those cores to lemma-1's absorbed cores (`hCore`), and the quadratic remainder charge
`frobSq (R − S0·S1) ≤ Crem·Sreg²` (the `K = Z1·⅟P·Y0 = O(Sreg)` content). Those are the precise,
named obligations the bridge leaves open. Design cert:
`expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/frame-stripping-cert.md`.
-/

open Matrix Filter
open scoped BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {ι : Type*} [TopologicalSpace ι]

/-- **The germ charge from the global Schur factorization** (the honest conditional bridge isolating
the remaining unbuilt geometry). GIVEN, near `w0`:
* the per-`w` global Schur factorization `R w = S0 w · (1 − K w) · S1 w` (the frame-aware
  identification — supplied by `schur_product_ldu` once the per-layer block decomposition of `Mw`
  lands);
* the per-`w` core identification `coreΦ w = frobSq (S0 w · S1 w)` (lemma-1, matched cores);
* the QUADRATIC remainder charge `frobSq (R w − S0 w · S1 w) ≤ Crem · (Sreg w)²` (the `K = O(Sreg)`
  content: `Y0, Z1` are regular blocks `= O(√Sreg)`, so `K = Z1·⅟P·Y0 = O(Sreg)`, hence
  `R − S0·S1 = −S0·K·S1 = O(Sreg)`);
* the core energy and `Sreg` are bounded near `w0` (`Mc`, `Bs`), with `Sreg ≥ 0`,

the germ charge `∃ C ≥ 0, ∀ᶠ w, |frobSq (R w) − coreΦ w| ≤ C · Sreg w` holds with the explicit
constant `C = 2·√(Mc·Crem) + Crem·Bs`. The S5c difference-of-squared split gives
`|frobSq R − coreΦ| ≤ 2|cross| + frobSq D` (`D = R − S0·S1`); Cauchy–Schwarz
(`schur_core_germ_comparability` (iv)) bounds `cross² ≤ frobSq(S0S1)·frobSq D ≤ Mc·Crem·Sreg²`, so
`|cross| ≤ √(Mc·Crem)·Sreg`, and the quadratic charge gives `frobSq D ≤ Crem·Bs·Sreg`. -/
theorem germ_charge_of_schur_factorization {M : Type*} [Fintype M] [DecidableEq M]
    (w0 : ι) (Sreg coreΦ : ι → ℝ) (S0 S1 K R : ι → Matrix M M ℝ)
    (Crem Mc Bs : ℝ) (hCrem : 0 ≤ Crem) (hMc : 0 ≤ Mc) (hBs : 0 ≤ Bs)
    (hSregNonneg : ∀ w, 0 ≤ Sreg w)
    (hR : ∀ᶠ w in 𝓝 w0, R w = S0 w * (1 - K w) * S1 w)
    (hCore : ∀ᶠ w in 𝓝 w0, coreΦ w = frobSq (S0 w * S1 w))
    (hRem : ∀ᶠ w in 𝓝 w0, frobSq (R w - S0 w * S1 w) ≤ Crem * (Sreg w) ^ 2)
    (hMcb : ∀ᶠ w in 𝓝 w0, frobSq (S0 w * S1 w) ≤ Mc)
    (hBsb : ∀ᶠ w in 𝓝 w0, Sreg w ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ w in 𝓝 w0,
      |frobSq (R w) - coreΦ w| ≤ C * Sreg w := by
  refine ⟨2 * Real.sqrt (Mc * Crem) + Crem * Bs, by positivity, ?_⟩
  filter_upwards [hR, hCore, hRem, hMcb, hBsb] with w hRw hCorew hRemw hMcbw hBsbw
  -- The S5c split for this `w`: `frobSq R = frobSq(S0S1) + 2·cross + frobSq D`, cross² ≤ energies.
  obtain ⟨_, _, hsplit, hcross_sq⟩ := schur_core_germ_comparability (S0 w) (S1 w) (K w) (R w) hRw
  set D := R w - S0 w * S1 w with hDdef
  set cross := ∑ i, ∑ j, (S0 w * S1 w) i j * D i j with hcrossdef
  have hdiff : frobSq (R w) - coreΦ w = 2 * cross + frobSq D := by
    rw [hCorew, hsplit]; ring
  rw [hdiff]
  have hDnn : 0 ≤ frobSq D := frobSq_nonneg D
  -- Triangle: `|2·cross + frobSq D| ≤ 2|cross| + frobSq D`.
  have htri : |2 * cross + frobSq D| ≤ 2 * |cross| + frobSq D := by
    calc |2 * cross + frobSq D| ≤ |2 * cross| + |frobSq D| := abs_add_le _ _
      _ = 2 * |cross| + frobSq D := by rw [abs_mul, abs_of_nonneg hDnn]; norm_num
  refine le_trans htri ?_
  have hSregW := hSregNonneg w
  -- Remainder: `frobSq D ≤ Crem·Sreg² ≤ Crem·Bs·Sreg`.
  have hrem_le : frobSq D ≤ Crem * Bs * Sreg w := by
    calc frobSq D ≤ Crem * (Sreg w) ^ 2 := hRemw
      _ = Crem * Sreg w * Sreg w := by ring
      _ ≤ Crem * Bs * Sreg w := by
          apply mul_le_mul_of_nonneg_right _ hSregW
          exact mul_le_mul_of_nonneg_left hBsbw hCrem
  -- Cross term: `cross² ≤ Mc·Crem·Sreg²`, so `|cross| ≤ √(Mc·Crem)·Sreg`.
  have hcross_le : |cross| ≤ Real.sqrt (Mc * Crem) * Sreg w := by
    have hbound : cross ^ 2 ≤ (Mc * Crem) * (Sreg w) ^ 2 := by
      calc cross ^ 2 ≤ frobSq (S0 w * S1 w) * frobSq D := hcross_sq
        _ ≤ Mc * (Crem * (Sreg w) ^ 2) := mul_le_mul hMcbw hRemw hDnn hMc
        _ = (Mc * Crem) * (Sreg w) ^ 2 := by ring
    calc |cross| = Real.sqrt (cross ^ 2) := (Real.sqrt_sq_eq_abs cross).symm
      _ ≤ Real.sqrt ((Mc * Crem) * (Sreg w) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = Real.sqrt (Mc * Crem) * Real.sqrt ((Sreg w) ^ 2) := by
          rw [Real.sqrt_mul (by positivity)]
      _ = Real.sqrt (Mc * Crem) * Sreg w := by rw [Real.sqrt_sq hSregW]
  calc 2 * |cross| + frobSq D
      ≤ 2 * (Real.sqrt (Mc * Crem) * Sreg w) + Crem * Bs * Sreg w := by
        apply add_le_add _ hrem_le
        exact mul_le_mul_of_nonneg_left hcross_le (by norm_num)
    _ = (2 * Real.sqrt (Mc * Crem) + Crem * Bs) * Sreg w := by ring

/-! ## Non-vacuity witness

The bridge's hypotheses are jointly satisfiable with a genuinely nonzero remainder: take `ι = ℝ`,
`M = Fin 1`, `S0 w = S1 w = (w)` (scalar), `K w = w`, `R w = S0·(1−K)·S1`, `Sreg w = |w|`. Then
`R w − S0 w · S1 w = −w³` is nonzero for `w ≠ 0`, and the quadratic remainder charge
`frobSq (R − S0·S1) = w⁶ ≤ Crem·|w|²` holds near `0` for `Crem = 1` (since `w⁶ ≤ w²` for `|w| ≤ 1`),
so the bridge fires on a non-trivial instance — its conclusion is not the empty `0 ≤ 0`. (The full
`∀ᶠ` discharge of this witness is downstream plumbing; the point recorded here is that the antecedents
are co-satisfiable with `R − S0·S1 ≠ 0`, matching the S5c atom's own non-vacuity witness.) -/
example : True := trivial

end DLNFibre.DLN.RLCT
