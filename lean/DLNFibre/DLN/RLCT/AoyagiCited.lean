import DLNFibre.DLN.RlctPayoff
import DLNFibre.Core.Meta.Cited

/-!
# `DLNFibre.DLN.RLCT.AoyagiCited` — the DLN RLCT cites, on the citation cordon

The **located cite file** for the DLN RLCT payoff (the citation cordon's first real user): the
genuinely-analytic monuments the payoff rests on, declared as `@[cited]` `axiom`s (so Lean's kernel
tracks them and `scripts/cited` accounts them), in one `…Cited.lean` file (the cordon's location
invariant). Cordon mechanism: `DLNFibre.Core.Meta.Cited`, `docs/policies/citation-cordon.md`.

The analytic content the DLN payoff needs is a **real log-canonical threshold map** `rlctReal` on
ℝ-losses, bracketed for the DLN square-Frobenius loss between `½·codim_ℝ` of its real zero-set:

* `rlctReal` — the rlct map, an external real-analytic invariant not in Mathlib (`@[cited]`);
* `cited_watanabe_upper_ax` — Watanabe's universal upper bound `rlct ≤ ½·codim_ℝ` (`@[cited]`);
* `cited_aoyagi_lower_ax` — the DLN-specific matching lower bound `½·codim_ℝ ≤ rlct` (Aoyagi Thm 1 /
  Lehalleur–Rimányi §8) (`@[cited]`).

All three carry the same inhabited-fibre scope guard `0 < N → B.rank = r → (∀ k', r ≤ d k')` as the
`RlctRealInterface` fields they discharge. From them we build the **proved instance**
`aoyagiRlctRealInterface : RlctRealInterface d`, so every generic payoff theorem specialised to it
(`DLNFibre.DLN.rlct_lossDLN_…_via_aoyagi`) transitively depends on exactly these three axioms — the
cordon classifies such a payoff as `CITED[Aoyagi/Watanabe]`, with no *unaccounted* axiom. Contrast
the in-file `rlctRealInterfaceWitness` (axiom-clean, reads `½·codim` off the zero-set): it proves
the interface type non-vacuous but is **not** the rlct.

The generic `RlctRealInterface` structure (cite visible in the *type*) stays as-is in
`DLNFibre.DLN.RlctPayoff`; this file is the complementary **cite-tracked-by-the-kernel** form the
cordon enforces. Both name the same two bounds; `name = content` throughout.
-/

open DLNFibre.Meta.Cited

-- The `@[cited "…"]` custom attribute grammar trips Mathlib's whitespace linter with a spurious
-- "extra space" at the string position (the source has a single space). Disable it here (this file
-- is only cite axioms + the instance); it affects neither the cordon nor any proof.
set_option linter.style.whitespace false

namespace DLNFibre.DLN

open Matrix DLNFibre.Core

variable {N : ℕ}

/-- **Cited (external, real-analytic).** The **real log-canonical threshold** map on ℝ-losses over
`Rep_d`. Not in Mathlib — a genuine real-analytic invariant (zeta-pole / volume-asymptotic), a cited
existence. The full zeta-pole *definition* is the RLCT-foundation build ladder (R2–R8);
until that lands, the DLN payoff uses this cited map. -/
@[cited "Watanabe/Aoyagi: the real log-canonical threshold (RLCT) invariant"]
axiom rlctReal {N : ℕ} (d : Fin (N + 1) → ℕ) : (Tuple (k := ℝ) d → ℝ) → ℝ

/-- **Cited (Watanabe's universal upper bound; scope = nonempty fibre).** For a genuine deep network
(`0 < N`) and a rank-`r` target with `r ≤ min d` (so `mult⁻¹(B)` is nonempty), the rlct of the real
square-Frobenius DLN loss is at most half the codimension of its real zero-set (the real fibre
`mult⁻¹(B)`). Watanabe's universal log-canonical-threshold bound `λ ≤ codim_ℝ / 2`. -/
@[cited "Watanabe (Alg. Geometry and Statistical Learning Theory): universal bound rlct ≤ ½·codim"]
axiom cited_watanabe_upper_ax (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ) :
    0 < N → B.rank = r → (∀ k', r ≤ d k') →
    rlctReal d (lossDLN d B) ≤ ((codimRealFibre d B).toNat : ℝ) / 2

/-- **Cited (Aoyagi Thm 1 / Lehalleur–Rimányi §8; scope = nonempty fibre).** For a genuine deep
network (`0 < N`) and a rank-`r` target with `r ≤ min d`, the rlct of the real square-Frobenius DLN
loss is at least half the codim of its real zero-set (the DLN-specific matching lower bound). -/
@[cited "Aoyagi Thm 1 (Lehalleur-Rimanyi §8, thm:aoyagi-rlct): DLN rlct = ½·codim, lower half"]
axiom cited_aoyagi_lower_ax (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ) :
    0 < N → B.rank = r → (∀ k', r ≤ d k') →
    ((codimRealFibre d B).toNat : ℝ) / 2 ≤ rlctReal d (lossDLN d B)

/-- **The Aoyagi/Watanabe `RlctRealInterface` instance, built from the three cited axioms.** Every
generic payoff theorem specialised to `aoyagiRlctRealInterface` transitively depends on
`{rlctReal, cited_watanabe_upper_ax, cited_aoyagi_lower_ax}` — the cordon classifies it `CITED`,
with no unaccounted axiom. This is the honest analytic interface (unlike the axiom-clean-but-not-the
-rlct `rlctRealInterfaceWitness`). -/
noncomputable def aoyagiRlctRealInterface (d : Fin (N + 1) → ℕ) : RlctRealInterface d where
  rlct := rlctReal d
  cited_watanabe_upper := cited_watanabe_upper_ax d
  cited_aoyagi_lower := cited_aoyagi_lower_ax d

/-! ## The cordon's first classified DLN payoff

`rlct_lossDLN_zero_eq_half_cCodim_aoyagi` is the corner-`0` payoff at the *genuine* Aoyagi/Watanabe
rlct: `rlct(K^DLN_0) = C/2`. `#audit_cited` / `scripts/cited` classify it as `CITED[rlctReal,
Watanabe, Aoyagi]` — the three located `@[cited]` axioms above, nothing unaccounted. -/

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

include ι in
/-- **DLN RLCT payoff at `r = 0`, at the cited Aoyagi/Watanabe rlct: `rlct(K^DLN_0) = C/2`.** The
corner-`0` payoff (`rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`) specialised to the cited-axiom
instance `aoyagiRlctRealInterface`. Rests on exactly the three located `@[cited]` axioms; the cordon
reports `CITED`, `UNACCOUNTED = ∅`. -/
theorem rlct_lossDLN_zero_eq_half_cCodim_aoyagi {d : Fin (N + 1) → ℕ} (hN : 0 < N)
    (h : (kostantPartitions d 0).Nonempty) :
    rlctReal d (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 :=
  rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi (K := K) (ι := ι) (aoyagiRlctRealInterface d) hN h

end DLNFibre.DLN
