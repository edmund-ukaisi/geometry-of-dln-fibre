# Statement card — strict `cCodim·0` monotonicity + unconditional θ-count

> **Claim (strict all-vertex dimension monotonicity).** If `e v < e' v` at *every* vertex `v`, then
> the combinatorial codimension of the corner-`0` rank locus is strictly larger for `e'`:
> `cCodim e 0 < cCodim e' 0`.
>
> - **Lean:** `DLNFibre.Core.cCodim_zero_strict`
>   (`lean/DLNFibre/Core/CCodimZeroStrict.lean` @ `9947d93`)
> - **Gloss.** For dimension vectors `e, e' : Fin (N+1) → ℕ` with `(kostantPartitions e 0).Nonempty`,
>   `(kostantPartitions e' 0).Nonempty`, and `∀ k, e k < e' k`, the minimum of the type-A `Ext`-pairing
>   quadratic form `codimForm` over the corner-`0` Kostant partitions of `e` is strictly below that of
>   `e'`.
> - **Proved.** Unconditionally (pure `CTheta`-level `ℤ`-combinatorics, no field, no geometry). Route B:
>   (i) **Lemma Y** `codimForm_extendℤ_pos_of_fullCover` — full coverage (`1 ≤ e' v` everywhere, which
>   `e k < e' k` forces) ⟹ every corner-`0` Kostant partition has `codimForm ≥ 1`, via the double sum
>   `codimForm (extendℤ m) = ∑_{A,B} m(A) m(B) · [pairBox A B]` (`codimForm_extendℤ_eq_sum_pairs`) plus
>   the extremal `[0,b]` coverage argument; (ii) **Lemma X** `reduceStep_strict` — pick the active pair
>   minimising the shorter member's length, split that member at the partner-adjacent vertex; the
>   partner sits at split-coefficient exactly `−1` and "shortest covering" (`claimA_left`/`claimA_right`)
>   kills all positive coefficients, so the step drops `codimForm` by `≥ 1`; (iii) the decremented
>   vector still dominates `e`, so the LANDED weak monotonicity `Core.CCodimZeroMono.exists_le_codimForm`
>   transports the bound. Reuses the four atomic moves `redMove`/`leftShrink`/`rightShrink`/`removeMove`
>   and their `codimForm_*_le` sign lemmas from `Core.CCodimZeroMono`, upgraded to `_lt` by the present
>   partner.
> - **Assumed.** Both Kostant families nonempty (`he`, `he'`) — the same hypotheses `cCodim` itself
>   carries (it is a `Finset.inf'`).
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free; axiom-clean (`[propext, Classical.choice, Quot.sound]`).

> **Consequence (θ-count headline, UNCONDITIONAL).** `θ = numTop d r = #{top-dimensional irreducible
> components of the rank-`r` orbit-closure stratification `Σ̄^r`}`.
>
> - **Lean:** `DLNFibre.Core.numTop_eq_ncard_topComponents`
>   (`lean/DLNFibre/Core/CCodimZeroStrict.lean` @ `9947d93`)
> - **Gloss.** For `[Field k] [IsAlgClosed k] [CharZero k]`, dimension vector `d`, rank `r`, and
>   `(kostantPartitions d r).Nonempty`, the combinatorial component count `numTop d r` equals the
>   `Set.ncard` of `topComponents d r` (the top-dimensional irreducible components of `Σ̄^r`).
> - **Proved.** Unconditionally. Discharges `numTop_eq_ncard_topComponents_of_strict`'s only remaining
>   open hypothesis `hMonoStrict` via `cCodim_zero_strict`; the weak `hMono` was already discharged by
>   `Core.CCodimZeroMono.cCodim_zero_mono` (thread 07).
> - **Cited.** none (the geometric reading `codimRepCanonical = codimForm` is `Core.CThetaGeometric`,
>   proved upstream).
> - **Deferred.** none.
> - **Status.** sorry-free; axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Route B fidelity notes (for the reviewer)

- **Where strictness genuinely enters.** Each strict move-delta lemma (`codimForm_redMove_lt`,
  `_leftShrink_lt`, `_rightShrink_lt`, `codimForm_removeMove_lt`) calls `sum_coeff_le_neg_one`, which
  bounds `∑_Y m(Y)·coeff(Y) ≤ −1` (not just `≤ 0`): the present partner `P` (`m P ≥ 1`) sits at
  `coeff P ≤ −1` and every *positive*-coefficient interval has multiplicity `0` (shortest covering).
  The `−1` is not a hidden `≤`: `splitCoeff_partner_le` etc. prove `coeff = −1` exactly by `omega` on
  the unfolded `rrInd`/`llInd` indicators.
- **The one non-mechanical step** (`claimA_left` / `claimA_right`): the minimal-shorter-member interval
  `I` is a shortest *active* covering interval of the partner-adjacent vertex `k`. Proven by the
  `y < d` vs `d ≤ y` (resp `a < x` vs `x ≤ a`) interval-arithmetic case split, each branch producing a
  shorter active pair contradicting minimality. Minimality is over `min(ilen A, ilen B)` (the shorter
  member); minimising a single distinguished member does NOT close one subcase (Codex-confirmed).
- **Numerics.** Partner-coefficient `= −1` verified exhaustively N≤5 (all four move types, both member
  sides); ClaimA + the strict-step existence verified over all full-coverage minimisers N≤2; the
  end-to-end `cCodim e 0 < cCodim e' 0` gap `≥ 1` matches the prior 800/800 certification.
