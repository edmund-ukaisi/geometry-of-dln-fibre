import DLNFibre.DLN.RlctPayoff
import DLNFibre.Core.Meta.Cited

/-!
# `DLNFibre.DLN.RLCT.AoyagiCited` — the DLN RLCT cites, on the citation cordon

The **located cite file** for the DLN RLCT payoff (the citation cordon's first real user): the
genuinely-analytic monuments the payoff rests on, declared as `@[cited]` `axiom`s (so Lean's kernel
tracks them and `scripts/cited` accounts them), in one `…Cited.lean` file (the cordon's location
invariant). Cordon mechanism: `DLNFibre.Core.Meta.Cited`, `docs/policies/citation-cordon.md`.

The analytic content the DLN payoff needs is **two bounds** bracketing the **built** global RLCT
`RLCT.rlctGlobal (lossDLN d B)` (Def 8.1(i), `Core.Analysis.RLCT.Global` — a cite-free `sSup` of
globally-locally-integrable exponents, NOT an opaque map) between `½·codim_ℝ` of its real zero-set:

* `cited_watanabe_upper_ax` — Watanabe's universal upper bound `rlctGlobal ≤ ½·codim_ℝ` (`@[cited]`);
* `cited_aoyagi_lower_ax` — the DLN-specific matching lower bound `½·codim_ℝ ≤ rlctGlobal` (Aoyagi
  Thm 1 / Lehalleur–Rimányi §8) (`@[cited]`).

**The opaque `rlctReal` map axiom is RETIRED.** The rlct is now the built `rlctGlobal`; the cited
boundary is exactly these **two** analytic bounds (the cite surface dropped from 4 to 3 across the
foundation: the local zeta-pole continuation + Watanabe + Aoyagi). Both bounds carry the same
inhabited-fibre scope guard `0 < N → B.rank = r → (∀ k', r ≤ d k')` as the `RlctRealInterface` fields
they discharge. From them we build the **proved instance** `aoyagiRlctRealInterface :
RlctRealInterface d`, so every generic payoff theorem specialised to it
(`DLNFibre.DLN.rlct_lossDLN_…_via_aoyagi`) transitively depends on exactly these two axioms — the
cordon classifies such a payoff as `CITED[Aoyagi/Watanabe]`, with no *unaccounted* axiom, and the
built `rlctGlobal` contributes NO axiom (it is cite-free; the local continuation cite is off the
global-payoff path).

The generic `RlctRealInterface` structure (cite visible in the *type*) stays in
`DLNFibre.DLN.RlctPayoff`; this file is the complementary **cite-tracked-by-the-kernel** form the
cordon enforces. Both name the same two bounds on `rlctGlobal`; `name = content` throughout.
-/

open DLNFibre.Meta.Cited

-- The `@[cited "…"]` custom attribute grammar trips Mathlib's whitespace linter with a spurious
-- "extra space" at the string position (the source has a single space). Disable it here (this file
-- is only cite axioms + the instance); it affects neither the cordon nor any proof.
set_option linter.style.whitespace false

namespace DLNFibre.DLN

open Matrix DLNFibre.Core RLCT.Global

variable {N : ℕ}

/-- **Cited (Watanabe's universal upper bound; scope = nonempty fibre).** For a genuine deep network
(`0 < N`) and a rank-`r` target with `r ≤ min d` (so `mult⁻¹(B)` is nonempty), the **built** global
RLCT `rlctGlobal (lossDLN d B)` (Def 8.1(i)) of the real square-Frobenius DLN loss is at most half the
codimension of its real zero-set (the real fibre `mult⁻¹(B)`). Watanabe's universal
log-canonical-threshold bound `λ ≤ codim_ℝ / 2` — now bounding the *built* object, not an opaque
map. -/
@[cited "Watanabe (Alg. Geometry and Statistical Learning Theory): universal bound rlct ≤ ½·codim"]
axiom cited_watanabe_upper_ax (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ) :
    0 < N → B.rank = r → (∀ k', r ≤ d k') →
    rlctGlobal (lossDLN d B) ≤ ((codimRealFibre d B).toNat : ℝ) / 2

/-- **Cited (Aoyagi Thm 1 / Lehalleur–Rimányi §8; scope = nonempty fibre).** For a genuine deep
network (`0 < N`) and a rank-`r` target with `r ≤ min d`, the **built** global RLCT
`rlctGlobal (lossDLN d B)` of the real square-Frobenius DLN loss is at least half the codim of its
real zero-set (the DLN-specific matching lower bound). -/
@[cited "Aoyagi Thm 1 (Lehalleur-Rimanyi §8, thm:aoyagi-rlct): DLN rlct = ½·codim, lower half"]
axiom cited_aoyagi_lower_ax (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ) :
    0 < N → B.rank = r → (∀ k', r ≤ d k') →
    ((codimRealFibre d B).toNat : ℝ) / 2 ≤ rlctGlobal (lossDLN d B)

/-- **The Aoyagi/Watanabe `RlctRealInterface` instance, built from the two cited bounds.** Every
generic payoff theorem specialised to `aoyagiRlctRealInterface` transitively depends on exactly
`{cited_watanabe_upper_ax, cited_aoyagi_lower_ax}` — the cordon classifies it `CITED`, with no
unaccounted axiom, and the built `rlctGlobal` it bounds contributes NO axiom (it is cite-free). This
is the honest analytic interface: the two bounds are genuine external content (Watanabe / Aoyagi
bracket the built `rlctGlobal`); the retired opaque `rlctReal` map is gone. -/
noncomputable def aoyagiRlctRealInterface (d : Fin (N + 1) → ℕ) : RlctRealInterface d where
  cited_watanabe_upper := cited_watanabe_upper_ax d
  cited_aoyagi_lower := cited_aoyagi_lower_ax d

/-! ## The cordon's first classified DLN payoff

`rlct_lossDLN_zero_eq_half_cCodim_aoyagi` is the corner-`0` payoff at the **built** global RLCT:
`rlctGlobal(K^DLN_0) = C/2`. `#audit_cited` / `scripts/cited` classify it as `CITED[Watanabe,
Aoyagi]` — the two located `@[cited]` axioms above, nothing unaccounted; the built `rlctGlobal`
contributes no axiom (it is cite-free, and the local zeta-pole continuation cite is off this path). -/

variable {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}

include ι in
/-- **DLN RLCT payoff at `r = 0`, at the BUILT global RLCT: `rlctGlobal(K^DLN_0) = C/2`.** The
corner-`0` payoff (`rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`) specialised to the cited-axiom
instance `aoyagiRlctRealInterface`. Rests on exactly the two located `@[cited]` bounds; the cordon
reports `CITED[Watanabe, Aoyagi]`, `UNACCOUNTED = ∅`. `rlctGlobal` is the built Def 8.1(i) object,
not an opaque map — the opaque `rlctReal` axiom is retired. -/
theorem rlct_lossDLN_zero_eq_half_cCodim_aoyagi {d : Fin (N + 1) → ℕ} (hN : 0 < N)
    (h : (kostantPartitions d 0).Nonempty) :
    rlctGlobal (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ) / 2 :=
  rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi (K := K) (ι := ι) (aoyagiRlctRealInterface d) hN h

end DLNFibre.DLN
