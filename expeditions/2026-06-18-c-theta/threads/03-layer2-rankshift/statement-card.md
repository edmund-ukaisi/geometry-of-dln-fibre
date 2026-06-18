# Statement card — Layer 2: the rank-shift `cCodim d r = cCodim (d−r) 0`

Module `lean/DLNFibre/Core/CTheta.lean` (rank-shift section, stacked on Layer 1). Built on the
committed Cor 3.5 form and the Layer-1 `kostantPartitions` / `cCodim` / `numTop`. Work uncommitted in
the `c-theta` worktree at audit time; controller bumps the SHA on integration.

---

> **Claim (corner-blindness).** `codimForm` never reads the corner entry `m (0, N)`: updating `m`
> there to any `c` leaves `codimForm N (extendℤ m)` unchanged.
>
> - **Lean:** `DLNFibre.Core.codimForm_update_corner` (with helpers
>   `extendℤ_update_corner_of_fst_pos`, `extendℤ_update_corner_of_snd_lt`).
> - **Gloss.** `codimForm N (extendℤ (Function.update m (0, Fin.last N) c)) = codimForm N (extendℤ m)`.
>   In the form `∑ m(i-1,j-1)·m(u,v)` over `1≤i≤u≤j≤v≤N`, the second factor has first index `u ≥ 1`
>   and the first factor has second index `j-1 < N`, so neither reduces to reading `(0, N)`.
> - **Proved.** The equality, by nested `Finset.sum_congr` + the two `extendℤ` invisibility helpers.
> - **Assumed / Cited / Deferred.** none.

> **Claim (the bijection).** `kostantPartitions (d−r) 0 = (kostantPartitions d r).image dropCorner`,
> with `dropCorner m := Function.update m (0, last) 0` injective on `kostantPartitions d r`.
>
> - **Lean:** `DLNFibre.Core.kostantPartitions_dminus_eq_image`, `DLNFibre.Core.dropCorner_injOn`
>   (with `dropCorner_mem`, `addCorner_mem`, `sum_filter_dropCorner`, `bound_of_kostant`,
>   `corner_mem_filter`). `dminus d r := fun k ↦ d k - r`.
> - **Gloss.** Setting the corner to 0 sends `KP(d, r)` onto `KP(d−r, 0)`; restoring it to `r`
>   (`addCorner`) inverts. The Kostant constraint at `k` reads `d k = m(0,N) + ∑_{(i,j)≠(0,N), i≤k≤j}`
>   (the all-covering `M_{0N}` is in every vertex filter), so dropping the corner subtracts exactly
>   `r` from each vertex sum — `sum_filter_dropCorner`. Injectivity: the corner is pinned at `r` on
>   `KP(d, r)`, so it can be restored.
> - **Proved.** The set equality (both inclusions) and `Set.InjOn`. The bound clause `m p ≤ d p.1` is
>   derived from the Kostant constraint (`bound_of_kostant`, via `Finset.single_le_sum`), not assumed.
> - **Assumed.** `kostantPartitions_dminus_eq_image` takes `hr : ∀ k, r ≤ d k` (so `d k − r` is honest
>   ℕ-subtraction). `dropCorner_mem` needs NO such hypothesis (a Kostant partition has `r ≤ d k` for
>   free). `dropCorner_injOn` needs none.
> - **Cited / Deferred.** none.

> **Claim (rank-shift).** `cCodim (d−r) 0 = cCodim d r` and `numTop (d−r) 0 = numTop d r`, for
> `r ≤ d k` at every vertex (Lehalleur–Rimányi Lemma 4.5).
>
> - **Lean:** `DLNFibre.Core.cCodim_rankShift`, `DLNFibre.Core.numTop_rankShift`
>   (`lean/DLNFibre/Core/CTheta.lean`).
> - **Gloss.** `cCodim_rankShift (hr : ∀ k, r ≤ d k) h₀ hr' : cCodim (dminus d r) 0 h₀ =
>   cCodim d r hr'`; likewise `numTop_rankShift`. The corner-dropping bijection preserves `codimForm`
>   (corner-blindness), so the `inf'` (`Finset.inf'_image` + `inf'_congr`) and the minimiser `card`
>   (`Finset.filter_image` + `filter_congr` + `card_image_of_injOn`) transport.
> - **Proved.** Both equalities, unconditionally given `hr`.
> - **Assumed.** `hr : ∀ k, r ≤ d k`, plus the two nonemptiness hyps (`h₀`, `hr'`) carried by
>   `cCodim`/`numTop`.
> - **Cited.** none. (Lineage: the paper's Lemma 4.5 / the `M_{0N}` projective-injective fact Thm 3.7;
>   realised here as a pure `Finset` bijection, not via the representation theory.)
> - **Deferred (geometric reading).** As in Layer 1: `cCodim`/`numTop` are the **combinatorial**
>   `C`/`θ`; the geometric identity (with `Σ^r`) rides on the deferred `hVoigt`. The rank-shift is a
>   statement about the combinatorial optima only.

> **Claim (witness, Lemma 4.5 instance).** `(2,2,2)` at `r=1` reduces to `(1,1,1) = dminus ![2,2,2] 1`
> at `r=0`; both have `C=1, θ=2`.
>
> - **Lean:** `DLNFibre.Core.cCodim_d222_one_rankShift` (the equality via `cCodim_rankShift`),
>   `cCodim_d222_one` (`= 1`), `numTop_d222_one` (`= 2`), with `mShift_mem`,
>   `kostantPartitions_d222_one_nonempty`, `kostantPartitions_d222_dminus_nonempty`, `d222_one_le`.
> - **Proved.** `cCodim (dminus ![2,2,2] 1) 0 = cCodim ![2,2,2] 1` (rank-shift instance);
>   `cCodim ![2,2,2] 1 = 1` and `numTop ![2,2,2] 1 = 2` by axiom-clean kernel `decide`.
> - **Assumed / Cited / Deferred.** none (numerically cross-checked: `(2,2,2) r=1` and `(1,1,1) r=0`
>   both give `min 1, θ 2`).

---

## Audit

- `python3 scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `lake build DLNFibre.Core.CTheta` green (~15 s).
- `#print axioms` on `cCodim_rankShift`, `numTop_rankShift`, `kostantPartitions_dminus_eq_image`,
  and the three witnesses: only `propext`, `Classical.choice`, `Quot.sound`.
- Fidelity review (Lean statement ↔ informal claim): **PASS** (reviewer, 2026-06-18, all cases
  checked). Verified the citation against `main.tex`: the rank-shift is `lem:rank_0` (line 816) =
  **Lemma 4.5**, hypothesis `0 ≤ r ≤ min d` = `∀ k, r ≤ d k`; the `(2,2,2)` witness is Example 4.3
  (line 771). Corner-blindness coverage, `hr`-placement (and `dropCorner_mem` needing none),
  `bound_of_kostant` soundness all confirmed; witnesses re-derived independently
  (`(2,2,2) r=1` and `(1,1,1) r=0` both C=1, θ=2). No mismatch, no overclaim.
- **Status: sorry-free + reviewed.**

## Codex consult

`threads/03-layer2-rankshift/codex/assembly-{prompt,answer}.md` — the `inf'`/`card` assembly idiom
(`Finset.inf'_image` + `inf'_congr`; `Finset.filter_image` + `filter_congr` + `card_image_of_injOn`).
The diagnosis (lemma names + orientation) was used; all proofs were built locally.

## Judgement calls

- **`dropCorner_mem` carries no `r ≤ d k` hypothesis.** The bound `m p ≤ (d−r) p.1` it must supply is
  a *consequence* of the Kostant constraint (`bound_of_kostant`), and a Kostant partition with corner
  `r` automatically has `r ≤ d k`, so the truncated `d k − r` is honest without an extra hypothesis.
  The linter flagged the originally-included `hr` as unused; dropped it (only
  `kostantPartitions_dminus_eq_image` and the rank-shift conclusions take `hr`).
- **Bound derived, not assumed.** `bound_of_kostant` proves `m p ≤ e p.1` from support + the Kostant
  constraint (the entry is one summand of the vertex sum), so the membership transports cleanly
  without re-deriving the per-entry bound.
