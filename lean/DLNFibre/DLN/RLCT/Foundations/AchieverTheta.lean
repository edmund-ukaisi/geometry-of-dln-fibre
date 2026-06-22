import DLNFibre.DLN.RLCT.Skeleton

/-!
# `DLNFibre.DLN.RLCT.Foundations.AchieverTheta` — the achiever-bound θ arithmetic substrate

The honest **arithmetic half** of A2 (the order `θ`), gate-independent and S2-free (`monomial_rlct`
is NOT used). The *geometric* `θ` (the per-chart binding-divisor multiplicity) is R1-divisor content
delivered by the resolution (G3.6, gated on the general-`M` cover); this file builds only the
always-well-defined **achiever-arithmetic** side `aoyagiTheta (cAch M) (aTheta M)`, which the
geometric `θ` is proven equal to once the divisors exist.

The binding of `(ℓ, a)` to `M` is via the A1 **achiever** `cAch M` (the largest λ-achiever
split-length, `Nat.findGreatest`), NOT via Def-3 (ill-defined on unbalanced widths) — so `(C, θ)`
form a clean Def-3-free pair, both routed through the same always-defined minimisation.

NOTE this is NOT the false bridge `#{argmin Adm} = aoyagiTheta` (that over-counts: `(2,2,2,2,2)` has 6
admissible minimisers / 6 binding rank-strata but `θ = a(ℓ−a)+1 = 5` — design-spec §3 warning). The
true `θ` is the chart-multiplicity, equal to `aoyagiTheta (cAch M) (aTheta M)` by Aoyagi Lemmas 4-5,
which needs the R1 divisors. This file pins only the arithmetic object `aoyagiTheta (cAch M) (aTheta M)`
and its totality / non-vacuity, for that downstream `G3.6` bridge to consume.
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The achiever multiplicity `a*(M)`.** The count of "big" entries in the balanced split of the
achiever stratum: `P* mod ℓ*`, where `ℓ* = cAch M` is the achiever split-length and
`P* = Sprefix M (ℓ*+1)` is the achiever total (sum of the `ℓ*+1` smallest reduced widths). Total and
Def-3-free (built from the A1 achiever, mirroring `lambdaCore`'s minimisation route). -/
noncomputable def aTheta (M : Fin (L + 1) → ℕ) : ℕ := Sprefix M (cAch M + 1) % cAch M

/-- **The Aoyagi order is the closed form `a(ℓ−a)+1`** (the definitional value, named for downstream
rewrites). -/
theorem aoyagiTheta_eq_value (ℓ a : ℕ) : aoyagiTheta ℓ a = a * (ℓ - a) + 1 := rfl

/-- **The Aoyagi order is positive** (the `+1`; the multiplicity is never zero — there is always at
least the diagonal binding direction). -/
theorem one_le_aoyagiTheta (ℓ a : ℕ) : 1 ≤ aoyagiTheta ℓ a := by
  rw [aoyagiTheta_eq_value]; exact Nat.le_add_left 1 _

/-- **The achiever multiplicity is a strict residue** `a*(M) < ℓ*(M)` whenever the achiever
split-length is positive (`0 < cAch M`, supplied downstream from `cAch_spec` under `1 ≤ L`). This is
the well-definedness fact the `aoyagiTheta (cAch M) (aTheta M)` value rests on (`a < ℓ` so the
balanced split is genuine). -/
theorem aTheta_lt_cAch (M : Fin (L + 1) → ℕ) (hc : 0 < cAch M) : aTheta M < cAch M :=
  Nat.mod_lt _ hc

/-- **The achiever order `θ = aoyagiTheta (cAch M) (aTheta M)` is positive** (non-vacuity of the
achiever-arithmetic θ at every `M`). -/
theorem one_le_achieverTheta (M : Fin (L + 1) → ℕ) :
    1 ≤ aoyagiTheta (cAch M) (aTheta M) := one_le_aoyagiTheta _ _

end DLNFibre.DLN.RLCT
