import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

set_option linter.style.longLine false

/-!
# `RouteMSJIncidenceExponent` — Brick D piece (iv): the exponent-gate arithmetic certificate

**Thread `genm-sj5-brickdcont`, aoyagi-full Stage 2.** The self-contained arithmetic behind the joint
incidence-rank resolution's exponent matching (`genm-incidencepp/incidence-cert.md` §3/§5). No integrals,
no matrix algebra — pure `ℕ` arithmetic on the joint-stratum codimension formula.

For a cut `u ≤ min(M₀, M₁)` of the arity-3 chain `M = (M₀, M₁, M₂)`, with `a = M₀−u`, `b = M₁−u`,
`d = M₂−b`, the rank-`ℓ`(W) / rank-`s`(Y) joint stratum has normal codimension (cert §3)

    C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ).

**Two facts, both exact-certified (`/tmp/cls_check.py`, 11598 valid strata, 0 failures):**
- **`ℓ`-independence ring identity:** `C_{ℓ,s} + a·b = (M₀−s)(M₁−s) + s·M₂` — the `ℓ`-terms cancel exactly
  (`ring` over ℤ after `zify` with the stratum range constraints). So `C_{ℓ,s}` does not depend on `ℓ`.
- **the exponent gate:** `minAdm M ≤ C_{ℓ,s} + a·b`, i.e. `T1_q := (minAdm M − ab)/2 ≤ C_{ℓ,s}/2`, so
  `q < T1_q ⟹ q < C_{ℓ,s}/2` (each stratum radial integral `∫ r^{C_{ℓ,s}−1−2q}dr` finite). This is
  `Finset.inf'_le` on the banked layer-peeling `minAdm (M₀,M₁,M₂) = min_{t≤min(M₀,M₁)}[(M₀−t)(M₁−t)+t·M₂]`.

The `inc_sweep.py` exhaustive check (332/332 in-scope cuts, widths 2..8) is EVIDENCE; the general proof here
is the ring identity + `Finset.inf'_le` (NOT a `decide` over any finite range).

**Scope — what is proved vs GATED.** Everything here is the **per-stratum** gate: for a GIVEN, enumerated
stratum `(ℓ, s)` satisfying the range constraints, `minAdm M ≤ C_{ℓ,s} + a·b` (true arithmetic, no coverage
claim). What is **NOT** proved here — and is **gated on the `genm-bltj` pen-and-paper hunt** — is the
AGGREGATE headline that the min of `C_{ℓ,s}` over the enumerated `(ℓ, s)` range EQUALS `2·T1` (i.e. that this
`(ℓ, s)` enumeration is the COMPLETE set of strata). bltj is probing a candidate soundness hole in the `b < j`
regime (shell forces weak singular values into `Q_p` itself, not `Q_b`): if a missed `Q_p`-degeneration
stratum sits at exponent `< T1`, the enumeration range is incomplete (and the aggregate headline would be
mis-scoped) or the formula extends. The `11598`-strata / `inc_sweep.py` numerics are EVIDENCE of completeness,
not a proof of it. Consume the per-stratum gate freely; do NOT treat "min over this range = T1" as canonical
coverage until bltj confirms the `(ℓ, s)` enumeration captures the `b < j` case.
-/

namespace DLNFibre.DLN.RLCT

open Finset

/-- The joint incidence-stratum codimension `C_{ℓ,s}` (cert §3): rank-`ℓ` chart of `W`, rank-`s` chart of
the `Y`-block, `C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ)` with `b = M₁−u`, `d = M₂−b`. -/
def clsCodim (M : Fin 3 → ℕ) (u ℓ s : ℕ) : ℕ :=
  u * (M 1 - u) + M 0 * ℓ + (M 0 - s) * (u - ℓ - s) + s * ((M 2 - (M 1 - u)) - ℓ)

/-- **The `ℓ`-independence ring identity (cert §0/§3), additive form.** `C_{ℓ,s} + a·b = (M₀−s)(M₁−s) + s·M₂`
(`a = M₀−u`, `b = M₁−u`); the `ℓ`-dependent terms cancel exactly. Proved over ℤ (`zify` + `ring`) under the
stratum range constraints (`s ≤ u`, `ℓ+s ≤ u`, `b+ℓ ≤ M₂`, `u ≤ min(M₀,M₁)`). -/
theorem clsCodim_add_ab_eq (M : Fin 3 → ℕ) (u ℓ s : ℕ)
    (hu : u ≤ min (M 0) (M 1)) (hs : s ≤ u) (hℓs : ℓ + s ≤ u) (hbℓ : (M 1 - u) + ℓ ≤ M 2) :
    clsCodim M u ℓ s + (M 0 - u) * (M 1 - u) = (M 0 - s) * (M 1 - s) + s * M 2 := by
  have h0 : u ≤ M 0 := by omega
  have h1 : u ≤ M 1 := by omega
  have h2 : s ≤ M 0 := by omega
  have h3 : s ≤ M 1 := by omega
  have h4 : ℓ ≤ u := by omega
  have h5 : s ≤ u - ℓ := by omega
  have h6 : M 1 - u ≤ M 2 := by omega
  have h7 : ℓ ≤ M 2 - (M 1 - u) := by omega
  simp only [clsCodim]
  zify [h0, h1, h2, h3, h4, h5, h6, h7]
  ring

/-- `minAdm` of a size-3 chain, from the banked layer-peeling recursion `LayerSplit_value_eq_minAdm` and the
`Fin 2` leaf (`minAdm (t, M₂) = t·M₂`): `minAdm M = min_{t≤min(M₀,M₁)} [(M₀−t)(M₁−t) + t·M₂]`. -/
theorem minAdm_arity3 (M : Fin 3 → ℕ) :
    minAdm M = (Finset.range (min (M 0) (M 1) + 1)).inf' (by simp)
        (fun t => (M 0 - t) * (M 1 - t) + t * M 2) := by
  have hrc : ∀ t : ℕ, minAdm (redChain t M) = t * M 2 := by
    intro t
    have h1 : redChain t M 1 = M 2 := by simp [redChain]
    rw [← minAdmRec_eq_minAdm, minAdmRec_leaf, redChain_zero, h1]
  rw [← LayerSplit_value_eq_minAdm M]
  refine Finset.inf'_congr _ rfl (fun t _ => ?_)
  rw [hrc t]

/-- **The exponent gate (cert §3/§5).** For a valid stratum `(ℓ, s)` (`s ≤ u`, `ℓ+s ≤ u`, `(M₁−u)+ℓ ≤ M₂`)
at a cut `u ≤ min(M₀,M₁)`, `minAdm M ≤ C_{ℓ,s} + a·b`, i.e. `T1_q = (minAdm M − ab)/2 ≤ C_{ℓ,s}/2`. So
`q < T1_q ⟹ q < C_{ℓ,s}/2`: every stratum's radial integral converges below the shell threshold `T1`. -/
theorem clsCodim_gate (M : Fin 3 → ℕ) (u ℓ s : ℕ)
    (hu : u ≤ min (M 0) (M 1)) (hs : s ≤ u) (hℓs : ℓ + s ≤ u) (hbℓ : (M 1 - u) + ℓ ≤ M 2) :
    minAdm M ≤ clsCodim M u ℓ s + (M 0 - u) * (M 1 - u) := by
  rw [clsCodim_add_ab_eq M u ℓ s hu hs hℓs hbℓ, minAdm_arity3 M]
  exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

/-- **Comparator threshold `T1_q ≤ u·M₂/2` (cert §3/§5, the `ℓ=0, s=u` corner).** `minAdm M ≤ a·b + u·M₂`,
so the LHS threshold `T1_q` does not exceed the comparator RLCT `u·M₂/2`. Needs `b = M₁−u ≤ M₂` (`d ≥ 0`;
holds in scope `a+b ≤ M₂`). -/
theorem minAdm_le_ab_add_uM2 (M : Fin 3 → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) (hb : M 1 - u ≤ M 2) :
    minAdm M ≤ (M 0 - u) * (M 1 - u) + u * M 2 := by
  have hgate := clsCodim_gate M u 0 u hu (le_refl u) (by omega) (by omega)
  rwa [clsCodim_add_ab_eq M u 0 u hu (le_refl u) (by omega) (by omega)] at hgate

end DLNFibre.DLN.RLCT
