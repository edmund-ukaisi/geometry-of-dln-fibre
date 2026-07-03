# Statement card — the `¬InteriorDrop ⟹ NoInteriorBothDrop` bridge, ∀L (the hNo de-conditionalizer)

**Status:** sorry-free. New STANDALONE module `DLNFibre/DLN/RLCT/Validate/RouteMHNoBridge.lean` on
`origin/genm-hnobridge` (branched from `origin/expedition/aoyagi-full @272e49bb`). Green in isolation
(8307 jobs) and against the full aggregator; NO signature changes to any existing result. Axiom
footprint `[propext, Classical.choice, Quot.sound]` (the `tStar` argmin choice) — pure combinatorics,
NO `sorryAx`, NO `native_decide`, NO `monomial_rlct`. Aggregator import left for the controller.

This supplies the `NoInteriorBothDrop M` that the clean/smeared `minAdm` collapse
(`minAdm_eq_deepRows_mul_last`) consumes, from the `¬InteriorDrop M` that the general-`L` R1-lower
achiever's CLEAN and SMEARED branches already carry — de-conditionalizing the R1 leg's `hNo`.

## The claim

> **Claim.** For any width vector `M : Fin (L+1) → ℕ` with `0 < Wext M L`, if `M` has no interior
> rank-drop then it has no interior both-drop:  `¬ InteriorDrop M → NoInteriorBothDrop M`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.noInteriorBothDrop_of_not_interiorDrop`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMHNoBridge.lean` @ `<commit-sha>`)
> - **Gloss.** Along the achiever descent path (`tStar M`, the fixed `Mval`-argmin), write
>   `T(k) = Text M (tach M) k`, `W(k) = Wext M k`. `InteriorDrop M` = `0 < W(L)` and there is an
>   interior boundary `p ∈ [1, L−1]` with a row-drop (`T(p+1) < T(p)`) AND a col-drop on the WHOLE
>   tail (`T(b+1) < W(b)` for every `b ∈ [p, L−1]`). `NoInteriorBothDrop M` = no single interior
>   boundary `s ∈ [1, L−1]` has BOTH a row-drop and a col-drop. The theorem: given `0 < W(L)`,
>   `¬InteriorDrop` implies `NoInteriorBothDrop`.
> - **Proved.** The full statement, ∀L, unconditionally (beyond the stated `0 < Wext M L`), by the
>   contrapositive argmin-exchange: an interior both-drop at `s₀` forces `InteriorDrop` with witness
>   `p = s₀` (`tail_colDrop` shows the whole tail `[s₀, L−1]` col-drops; the first col-failure `b`
>   would let the plateau-raise `raiseTup` between the last row-drop `q ∈ [s₀, b−1]` and `b` produce
>   an admissible tuple `T'` with `Mval M T' = minAdm + (1 − r_q − c_q) ≤ minAdm − 1`, contradicting
>   `Finset.inf'_le`). `T' ∈ Adm M` is re-derived cleanly (`raiseTup_mem_Adm`: per-layer bounds from
>   the col-drop tail + the corner row-drop; weak-decrease from the row-drop at `q`; last-exponent `0`
>   since the block sits below `L−1`); the delta `1 − r_q − c_q` is exact (`Mval_raiseTup`), so
>   `r_q, c_q ≥ 1` genuinely forces `ΔMval ≤ −1`.
> - **Assumed.** `0 < Wext M L` (a hypothesis, matching the `InteriorDrop` corner: at `M[L]=0` both
>   `InteriorDrop` and any interior both-drop are vacuously governed — the hypothesis pins the leaf
>   `Wext L` positive, as the clean/smeared branches supply).
> - **Cited.** none (self-contained combinatorics over the banked residual-block API:
>   `rBlock`/`cBlock` + `_nonneg`/`_eq_Text`/`_eq_Wext`, `Mval`/`Adm`/`tPrev`, `tStar`/`tach`,
>   `Mval_tStar_eq_inf'`, `Finset.inf'_le`).
> - **Deferred.** The spine surgery that plugs this into the R1 achiever `hdiv` (dropping its `hNo`
>   hypothesis) is a SEPARATE controller step — NOT touched here (no edit to
>   `RouteMAchieverDispatch`/`Full`).
> - **Structure & ideas observed (pen-and-paper).** Forward (single both-drop ⟹ whole-tail col-drop
>   ⟹ InteriorDrop) is minimality-driven, NOT local: `row-drop@b ⟹ col-drop@b` is FALSE
>   (`M=(5,3,4,2,1)`, `tStar=(3,3,2,0)`, row-drop-no-col-drop at s=3). The load-bearing move is the
>   plateau raise `T(s) += 1` for `s ∈ [q+1, b]` (equivalently `tStar(j) += 1` for `j ∈ [q−1, b−2]`),
>   with `ΔMval = 1 − r_q − c_q`. Exact-enumerated L=2..6 on 9716 (M,argmin) pairs, 0 violations;
>   exchange verified on 11688 cases; decorrelated Codex xhigh agreeing.
> - **Route (controller).** Take `p* = s₀` (the given both-drop); prove the whole tail `[s₀,L−1]`
>   col-drops via the argmin-exchange contradiction against `Mval_tStar_eq_inf'` + `Finset.inf'_le`.
>   Off-by-one warning honoured: the `tStar`-index raise block is `[q−1, b−2]` (`tStar(j)=Text(j+2)`),
>   confirmed by an independent re-derivation and by two decorrelated Codex xhigh consults.
> - **Status.** sorry-free (awaiting reviewer fidelity check).

## Independent cross-checks (kill-condition re-derived, not trusted)

- **`T' ∈ Adm` re-derived** from the real `admPred` in `raiseTup_mem_Adm` (not asserted): the three
  legs (per-layer bound, weak-decrease, last-zero) each proved; the `q=1` corner (per-layer needs
  `tStar(0) < min(M0,M1)`, from the row-drop `rBlock⟨0⟩>0` giving `< M0` and the col-drop giving
  `< M1`) and the `q≥2` weak-decrease bottom (`tStar(q−1) < tStar(q−2)` from the row-drop) handled
  explicitly.
- **`ΔMval = 1 − r_q − c_q` re-derived** in `Mval_raiseTup` via `Finset.sum_eq_single_of_mem`: the
  per-`j` delta is `0` off `j = q−1` (interior via flatness `rBlock=0`; top via `cBlock⟨b−1⟩=0`),
  matching two independent hand derivations + Codex.
- **Numerical:** exhaustive L=2..4 (984 (M,argmin) pairs) reproduced 0 equivalence-violations and 0
  failures of the exact implication `¬InteriorDrop → NoInteriorBothDrop`, including the flagged
  `M=(5,3,4,2,1)`.

## The delivered API (RouteMHNoBridge.lean)

- `raiseTup` / `raiseTup_of_mem` / `raiseTup_of_not_mem` — the block-raise tuple + its two branches.
- `uCur` / `uPrevB` / `raiseTup_cast` / `tPrev_raiseTup` — the ℤ-valued current/predecessor bump
  indicators and the two clean bump identities (`(T' j : ℤ) = tStar j + uCur`,
  `tPrev T' j = tPrev tStar j + uPrevB`).
- `Mval_summand_tStar` / `Mval_raiseTup` — the achiever summand `= rBlock·cBlock` and the exact
  `Mval` delta of the block raise.
- `raiseTup_mem_Adm` — the raised tuple is admissible.
- `rBlock_pos_iff` / `cBlock_pos_iff` — the row/col-drop ↔ block-positivity bridges.
- `exchange_contra` — the argmin-exchange contradiction (first col-failure is impossible).
- `tail_colDrop` — a both-drop forces the whole tail to col-drop (strong induction).
- `noInteriorBothDrop_of_not_interiorDrop` — **the bridge headline.**
