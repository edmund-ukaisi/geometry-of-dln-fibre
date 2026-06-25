import DLNFibre.DLN.RlctPayoff
import DLNFibre.Core.SigmaCodim

/-!
# `DLNFibre.DLN.RlctPayoffGeneral` — the general-rank-`r` RLCT payoff

Extends the LANDED corner-`0` payoff (`DLNFibre.DLN.RlctPayoff`) to a **rank-`r` target `B`**: the
real log-canonical threshold of the DLN square-Frobenius loss `K^DLN_B` (for `B` of rank `r`) is
`(C + r(d_0+d_N−r))/2`, where `C = cCodim d r` is the combinatorial codimension and the
`+ r(d_0+d_N−r)` is the bundle shift of Lehalleur–Rimányi Lemma 4.6.

The result splits into two bricks of **different status** (expedition thread 11 sizing):

* **Brick A (Proved, zero-cited, general in `r`).** `codimRepCanonical Σ̄^r = cCodim d r`
  (`Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`): the geometric codimension of the
  *closed rank-`≤ r` product locus* `Σ̄^r = productRankLocusLE d r` equals the combinatorial `C`. This
  is **network-free `Core` geometry** and lives in `DLNFibre.Core.SigmaCodim` (imported here): the
  same orbit-closure machinery that proved the `r = 0` case (`sigmaIdeal d r = sInf orbitIdeals`,
  general in `r`; the per-orbit Voigt codim; the realizer of a minimising Kostant partition), run at
  general `r`. The per-orbit lower bound uses only the **weak** dimension-monotonicity
  (`Core.CCodimZeroMono.cCodim_zero_mono`) through `cCodim_le_codimRepCanonical_of` — it does **not**
  need the strict version (`Core.CCodimZeroStrict.cCodim_zero_strict`, which the θ-count headline uses
  and which is itself now proved). `Σ̄^r` is `GL_d`-stable (a finite union of orbit closures), so there
  is no fibre-dimension wall.

* **Brick B (interface, named — LR Lemma 4.5 + Lemma 4.6).** The passage `Σ̄^r ⤳ mult⁻¹(B)` (for `B`
  of rank `r`, `0 < N`) is the bundle shift `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)`. The paper
  states the shift for the *exact-rank* locus `Σ^r` (Lemma 4.6, `lem:rank_vs_fibers`); the
  closed-locus form here folds in `codim Σ̄^r = codim Σ^r` (Cor. 4.4 + Lemma 4.5, `lem:rank_0` — the
  Zariski closure preserves codimension). This **codimension identity is now PROVED, zero-cite**, in
  `Core.FibreCodimFinal` (`codimRepCanonical_fibre_eq_cCodim_add_shift`, the route-β localized-chart
  sweep), and the `BundleShiftInterface` field is now **DISCHARGED** from it in `DLN.BundleShiftDischarge`
  (`bundleShift_of_core` — #52/G4, done). This module retains the structure + the base two-interface
  transport (`_via_aoyagi`); the discharged destination payoff `rlct_lossDLN_eq_half_cCodim_add_shift`,
  resting on only `RlctInterface`, lives in `DLN.BundleShiftDischarge`.

**R2-general** (`rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`) is pure transport: the (already
general-in-`r`) Cited Aoyagi equality gives `rlct = ½·codim mult⁻¹(B)`; Brick B rewrites the fibre
codim as `codim Σ̄^r + shift`; Brick A rewrites `codim Σ̄^r = cCodim d r`. Both interfaces `I`, `J`
are explicit in the type; `via_aoyagi` names the rlct source. This is **not** an unconditional
`rlct = (C + shift)/2`. Both interface fields are guarded by `0 < N` — the scope (a genuine deep
network, N ≥ 1) where Lemma 4.6 and Aoyagi hold; at `N = 0` the "product" `mult` is the empty product
and the shift identity is false.

**Dependency rule:** `DLN` depends on `Core`; `Core` never imports `DLN`. Brick A is now in `Core`.
-/

namespace DLNFibre.DLN

open Matrix DLNFibre.Core

universe u v

variable {N : ℕ}

/-! ## Brick B — the bundle shift (interface, named: LR Lemma 4.5 + Lemma 4.6)

The passage `Σ̄^r ⤳ mult⁻¹(B)` gives the bundle shift `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)`.
This codimension identity is PROVED, zero-cite, in `Core.FibreCodimFinal`
(`codimRepCanonical_fibre_eq_cCodim_add_shift`), and the interface is **DISCHARGED** from it in
`DLN.BundleShiftDischarge` (`bundleShift_of_core`, #52/G4). This module retains the structure + the
base two-interface transport. Brick A (`codim Σ̄^r = C`) is `Core` geometry (`DLNFibre.Core.SigmaCodim`). -/

section BrickB

open MvPolynomial

/-- **The bundle-shift interface (Lehalleur–Rimányi Lemma 4.5 + Lemma 4.6).** A carried geometric
hypothesis (NOT a global `axiom`). For a genuine deep network (`0 < N`) and `B` of *exact* rank
`r ≤ min d`, Lemma 4.6 (`lem:rank_vs_fibers`, main.tex:844–858) says `mult⁻¹(B)` is a locally-trivial
bundle over the rank-`r` matrix orbit `Mat^{rk=r}` (of dimension `r(d_0+d_N−r)`), so
`codim mult⁻¹(B) = codim Σ^r + r(d_0+d_N−r)`. The field is stated for the *closed* rank-`≤ r` locus
`Σ̄^r = productRankLocusLE d r`, folding in `codim Σ̄^r = codim Σ^r` (Cor. 4.4 + Lemma 4.5,
`lem:rank_0`, main.tex:816–833 — the Zariski closure preserves codimension). This codimension
identity is PROVED, zero-cite, in `Core.FibreCodimFinal`
(`codimRepCanonical_fibre_eq_cCodim_add_shift`); the field `cited_bundle_shift` is **DISCHARGED** by
`DLN.BundleShiftDischarge.bundleShift_of_core` (a proved instance from that Core result, #52/G4) — the
structure remains the interface that the base transport `_via_aoyagi` consumes. The `0 < N` guard restricts it to the scope where Lemma 4.6
holds: at `N = 0` the "product" `mult` is the empty product (`mult = 1` on the trivial chain) and the
shift identity fails. Separate from `RlctInterface` so the two interfaces (Aoyagi rlct + the
Lemma 4.5/4.6 shift) are independently visible in any consumer's type. -/
structure BundleShiftInterface (d : Fin (N + 1) → ℕ)
    (K : Type v) [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K) where
  /-- **LR Lemma 4.5 + Lemma 4.6 (scope `0 < N`):** for a genuine deep network, the geometric
  codimension of the multiplication fibre `mult⁻¹(B)` (base-changed to `K`, `B` of exact rank `r`)
  equals that of the closed rank-`≤ r` product locus `Σ̄^r` plus the base dimension `r(d_0+d_N−r)`.
  The `Σ̄^r` form combines Lemma 4.6 (the shift, stated for the exact-rank `Σ^r`) with
  `codim Σ̄^r = codim Σ^r` (Cor. 4.4 + Lemma 4.5). This identity is PROVED, zero-cite, in
  `Core.FibreCodimFinal`, and discharged by `DLN.BundleShiftDischarge.bundleShift_of_core` (#52/G4). -/
  cited_bundle_shift : ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ),
    0 < N → B.rank = r → (∀ k', r ≤ d k') →
    codimRepCanonical (fibre (k := K) d (B.map ι))
      = codimRepCanonical (productRankLocusLE (k := K) d r)
        + ((r * (d 0 + d (Fin.last N) - r) : ℕ) : ℕ∞)

end BrickB

/-! ## R2-general — the payoff `rlct(K^DLN_B) = (C + r(d_0+d_N−r))/2`

Pure transport through both interfaces (the Cited Aoyagi rlct + the bundle shift) and Brick A. -/

section R2General

variable {d : Fin (N + 1) → ℕ}
  {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

/-- **The general-`r` RLCT payoff, through the Cited Aoyagi rlct AND the Lemma-4.5/4.6 shift
interface.** Given the interfaces `I` (Aoyagi rlct, Cited) and `J` (Lemma 4.5/4.6 bundle shift, a
codimension identity Proved in `Core.FibreCodimFinal`, carried here as a hypothesis — this is the
lower-level two-interface transport; `DLN.BundleShiftDischarge` discharges `J` from Core and gives
the destination payoff resting on only `I`), for a genuine deep network (`0 < N`) and `B` of rank `r ≤ min d`, the rlct of
the DLN square-Frobenius loss `K^DLN_B` equals `(cCodim d r + r(d_0+d_N−r))/2`: the combinatorial
`C/2` plus the half-shift. Proof: `I.cited_aoyagi_dln` (general in `r`) gives `rlct = ½·codim mult⁻¹(B)`;
`J.cited_bundle_shift` rewrites the fibre codim as `codim Σ̄^r + shift`; Brick A
(`Core.codimRepCanonical_productRankLocusLE_eq_cCodim`) rewrites `codim Σ̄^r = cCodim d r`. Both
interfaces `I`, `J` are explicit in the type (both dependencies visible); `via_aoyagi` names the
rlct source. This is **not** an unconditional `rlct = (C + shift)/2`. The `0 < N` guard is the scope
of both interface facts (a genuine product). `[IsAlgClosed K] [CharZero K]` (the scope where `C` is the
geometric codimension). -/
theorem rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi
    (I : RlctInterface d K ι) (J : BundleShiftInterface d K ι)
    {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ} {r : ℕ}
    (hN : 0 < N) (hB : B.rank = r) (hr : ∀ k', r ≤ d k') (h : (kostantPartitions d r).Nonempty) :
    I.rlct (lossDLN d B)
      = (((cCodim d r h).toNat : ℝ) + (r * (d 0 + d (Fin.last N) - r) : ℕ)) / 2 := by
  -- the Aoyagi guard `r ≤ univ.inf' d` is `∀ k, r ≤ d k`
  have hrinf : r ≤ Finset.univ.inf' Finset.univ_nonempty d := by
    rw [Finset.le_inf'_iff]; exact fun b _ ↦ hr b
  rw [I.cited_aoyagi_dln B r hN hB hrinf, J.cited_bundle_shift B r hN hB hr]
  -- split the `ℕ∞.toNat` of the sum: both summands finite
  have hAfin : codimRepCanonical (productRankLocusLE (k := K) d r) ≠ ⊤ := by
    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]; exact ENat.coe_ne_top _
  have hAval : (codimRepCanonical (productRankLocusLE (k := K) d r)).toNat = (cCodim d r h).toNat := by
    rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h, ENat.toNat_coe]
  rw [ENat.toNat_add hAfin (ENat.coe_ne_top _), hAval, ENat.toNat_coe]
  push_cast
  ring

end R2General

/-! ## Non-vacuity witness — `(2,2,2)`, `r = 1`

The worked example `d = (2,2,2)` at rank `r = 1` (Lehalleur–Rimányi §4): the combinatorial
`C = cCodim d222 1 = 1` (LANDED `Core.CTheta.cCodim_d222_one`), the bundle shift
`1·(2+2−1) = 3`, so the predicted fibre codim is `4` and the RLCT payoff is `(1+3)/2 = 2`. The
codimension of `Σ̄^1` is shown over `AlgebraicClosure ℚ`; the rlct payoff over `ℂ` (which carries
the embedding `ℝ →+* ℂ` the interface needs — as the LANDED `r = 0` `(2,2,2)` witness does). The fibre
codim and the rlct value were independently checked by direct Jacobian rank (thread 11). -/

section Witness

/-- **`(2,2,2)`, `r = 1`: the geometric codimension of `Σ̄^1` is `1`**, over `AlgebraicClosure ℚ` —
the geometric reading of the combinatorial `C = cCodim d222 1 = 1` (LR §4), via Brick A. -/
theorem codimRepCanonical_productRankLocusLE_d222_one :
    (codimRepCanonical (productRankLocusLE (k := AlgebraicClosure ℚ) Core.d222 1)).toNat = 1 := by
  have h := codimRepCanonical_productRankLocusLE_eq_cCodim (k := AlgebraicClosure ℚ) Core.d222 1
    Core.kostantPartitions_d222_one_nonempty
  rw [Core.cCodim_d222_one] at h
  omega

/-- **`(2,2,2)`, `r = 1`: the RLCT payoff `rlct(K^DLN_B) = 2`**, over `ℂ`, for `B` of rank `1`,
through the Cited Aoyagi interface `I` and the Lemma-4.5/4.6 bundle-shift interface `J` (now
discharged from Core by `DLN.BundleShiftDischarge.bundleShift_of_core`; the discharged witness is
`DLN.BundleShiftDischarge.rlct_lossDLN_d222_one_eq_two`). The
combinatorial `C = cCodim d222 1 = 1` and the shift `1·(2+2−1) = 3` give `rlct = (1+3)/2 = 2`: the
`(2,2,2)` rank-`1` DLN is mildly singular. `(2,2,2)` has `N = 2 > 0`, so the `0 < N` scope guard
is met. Both interfaces `I`, `J` are the explicit hypotheses. -/
theorem rlct_lossDLN_d222_one_eq_two_via_aoyagi
    (I : RlctInterface Core.d222 ℂ Complex.ofRealHom)
    (J : BundleShiftInterface Core.d222 ℂ Complex.ofRealHom)
    {B : Matrix (Fin (Core.d222 (Fin.last 2))) (Fin (Core.d222 0)) ℝ} (hB : B.rank = 1) :
    I.rlct (lossDLN Core.d222 B) = 2 := by
  have hr : ∀ k', (1 : ℕ) ≤ Core.d222 k' := Core.d222_one_le
  rw [rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi I J (by norm_num) hB hr
    Core.kostantPartitions_d222_one_nonempty, Core.cCodim_d222_one]
  have hshift : (1 : ℕ) * (Core.d222 0 + Core.d222 (Fin.last 2) - 1) = 3 := by decide
  rw [hshift]
  norm_num

end Witness

end DLNFibre.DLN
