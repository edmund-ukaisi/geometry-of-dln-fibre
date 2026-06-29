# Statement card — Thread 11 (CAPSTONE): prove + discharge the real↔complex transfer `hT`

Branch `expedition/rlct-bridge-discharge` (from `expedition/rlct-bridge` @ `7182d0eb`). Files:
`lean/DLNFibre/DLN/{RlctPayoff,RlctPayoffGeneral,BundleShiftDischarge}.lean`,
`lean/DLNFibre/Core/RankLocusClosed.lean`, `lean/DLNFibre.lean`.

This card **supersedes thread 04's card on the transfer**: the formerly-Cited `hT` (`codim_ℝ = codim_K`)
is now a PROVED theorem. The cited boundary shrinks `3 → 2`: `{Watanabe ≤, Aoyagi ≥}`.

---

> **Claim.** The real↔complex codimension transfer for the DLN multiplication fibre,
> `codim_ℝ(fibre ℝ B) = codim_K(fibre K (B.map ι))` (for `B` of rank `r`, a genuine deep network
> `0 < N`, an injective field hom `ι : ℝ →+* K`, `K` algebraically-closed char-0), is **PROVED** — both
> sides are computed by the *same* field-independent Core codimension identity, giving the same
> combinatorial `(cCodim d r).toNat + r·(d_N + d_0 − r)`. No real-radical / semialgebraic-dimension
> input is needed. Consequently every DLN RLCT payoff drops its `hT` hypothesis and rests on the two
> Cited analytic bounds alone.
>
> - **Lean (the proved transfer).** `DLNFibre.DLN.codimRealFibre_eq_codimRepCanonical_baseChange`
>   (`RlctPayoff.lean`):
>   `(hN : 0 < N) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) {r} (hB : B.rank = r)`
>   `(h : (kostantPartitions d r).Nonempty) : codimRealFibre d B = codimRepCanonical (k:=K) (fibre K (B.map ι))`,
>   for the section `{K : Type} [Field K] [IsAlgClosed K] [CharZero K] {ι : ℝ →+* K}`.
>   Proof: `obtain ⟨M, rfl⟩ : ∃ M, N = M+1` (defeq `Fin (M+2)`); apply
>   `Core.codimRepCanonical_fibre_eq_cCodim_add_shift` over ℝ (rank `r`) and over `K`
>   (rank `(B.map ι).rank = r` by `Matrix.rank_map_eq_of_injective`); both RHS are the identical
>   field-independent `(cCodim d r h).toNat + r·(d_N+d_0−r)`; `exact hℝ.trans hK.symm`.
> - **Lean (rank base-change micro-lemma, relocated to Core).** `Matrix.rank_map_eq_of_injective`
>   (top-level `Matrix` namespace, `RankLocusClosed.lean`): an injective ring hom between fields
>   preserves `Matrix.rank`, via the in-repo determinantal-rank bridge
>   `DLNFibre.Core.rank_le_iff_forall_submatrix_det_eq_zero` + `RingHom.map_det` + injectivity.
>   (Moved from `BundleShiftDischarge`; declared outside `DLNFibre.Core` so the `Matrix.`-prefixed name
>   does not shadow the top-level `Matrix` namespace for downstream Core files.)
> - **Lean (discharged payoffs — `hT` hypothesis removed from all of them).**
>   `RlctPayoff.lean`: `rlct_lossDLN_eq_half_codimFibre_of_transfer`,
>   `rlct_lossDLN_zero_eq_half_{codimFibre,iInf_orbitCodim,cCodim}_via_aoyagi`,
>   `rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi`.
>   `RlctPayoffGeneral.lean`: `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`,
>   `rlct_lossDLN_d222_one_eq_two_via_aoyagi`.
>   `BundleShiftDischarge.lean`: `rlct_lossDLN_eq_half_cCodim_add_shift`, `rlct_lossDLN_d222_one_eq_two`.
> - **Why no real-AG is needed (the direct route).** The L7+L8 relaxation made
>   `Core.codimRepCanonical_fibre_eq_cCodim_add_shift` hold over any `[CharZero][Infinite]` field (ℝ
>   included, no `IsAlgClosed`). `CharZero ⟹ Infinite` (`CharZero.infinite`). Both fibres' codim then
>   equal the same combinatorial `C + δ`, so they are equal — the `x²+y²`-style real/complex dimension
>   gap never arises (the codim is pinned combinatorially, not by comparing point-set dimensions).
> - **Scope note (Type 0).** `Core.codimRepCanonical_fibre_eq_cCodim_add_shift` is stated at `k : Type`
>   (Type 0 — the Schur-side no-drop fixes the index type), so the proved transfer and the discharged
>   payoffs are at `K : Type` (Type 0). The RLCT witnesses land at `ℂ` / `AlgebraicClosure ℚ`, both
>   Type 0. The R/R2-general sections were narrowed `Type v → Type` to match; this is honest (the
>   geometric identity genuinely only holds at Type 0 here).
> - **Proved / Cited / Deferred.**
>   - **Proved (axiom-clean `[propext, Classical.choice, Quot.sound]`).** The transfer
>     `codimRealFibre_eq_codimRepCanonical_baseChange`; the rank base-change `Matrix.rank_map_eq_of_injective`;
>     all 8 discharged payoffs; the Core headline `codimRepCanonical_fibre_eq_cCodim_add_shift`.
>     (`#print axioms` force-checked on a deleted scratch.)
>   - **Cited (named, sourced — the permanent boundary `{watanabe_upper, aoyagi_lower}`).**
>     `RlctRealInterface.cited_watanabe_upper` (Watanabe's universal `rlct ≤ ½·codim_ℝ`);
>     `RlctRealInterface.cited_aoyagi_lower` (Aoyagi Thm 1 / Lehalleur–Rimányi §8 `thm:aoyagi-rlct`,
>     `½·codim_ℝ ≤ rlct`). Both guarded by `0 < N → B.rank = r → (∀ k', r ≤ d k')` (the inhabited-fibre
>     scope). The transfer `T` is **no longer Cited** (it is Proved).
>   - **Banked, unused.** `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` (the catenary reduction of
>     `codim_ℝ = codim_K` from a real-dim = complex-dim equality `hdim`) — superseded by the direct
>     route; kept as alternative infrastructure (its `hdim` step would itself need a smooth full-dim real
>     point per top component, so the direct route is shorter and unconditional).
> - **Status.** sorry-free; full `scripts/lb DLNFibre` green (3818 jobs); `#print axioms` on the 7
>   load-bearing decls (transfer + 4 payoffs + headline + rank base-change) = `[propext,
>   Classical.choice, Quot.sound]`. Awaiting the decorrelated fidelity + hardener re-review.

---

### Caveat next to the claim (precision)
The DLN RLCT payoff is **still not** an unconditional `rlct = ½·codim` theorem — but the only remaining
Cited input is the analytic rlct interface `RlctRealInterface` (the two bounds bracketing the rlct of
the *real* loss between `½·codim_ℝ`). The real↔complex transfer, the connector, the catenary, the
bundle shift, and `codim_K = C` are all Proved. The `_via_aoyagi` names still flag the cited analytic
source; the guard still flags the inhabited-fibre scope.
