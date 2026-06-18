# Statement card — Layer 3a: the QIP (Thm 6.1) EASY half (substitution `≤`)

Module `lean/DLNFibre/Core/CThetaQIP.lean` (new file, imports `Core.CTheta`). Built on the Layer-1
`codimForm` / `kostantPartitions` / `cCodim`. Work uncommitted in the `c-theta` worktree at audit time;
controller bumps the SHA on integration and wires the import into `DLNFibre.lean`.

**Scope (name = content).** This thread proves the **substitution direction only** — `≤`. The reverse
`cCodim ≥ qipMin` (every minimiser lies in the `e`-image, Lemma 6.4/6.7) is the HARD converse and is
**NOT** here; `cCodim = qipMin` (Thm 6.1 proper) is **NOT** asserted. Thread `04-ctheta-qip-converse`
prototypes the converse.

---

> **Claim (the substitution `mOfE`).** For a dimension vector `d`, the map `e ↦ mOfE d e` sends a QIP
> variable `e : Fin N → ℕ` to the multiplicity array of its horizontal-lace module
> `⊕_i M_{0,i-1}^{e_i} ⊕_i M_{i,N}^{e_i + d_i − d_{i-1}}`. Closed-form entry: `(0,b)↦e_{b+1}` for `b<N`;
> `(a,N)↦e_{a-1}+(d_a−d_{a-1})` for `a≥1`; else `0`. Corner `(0,N) = 0`.
>
> - **Lean:** `DLNFibre.Core.mOfE` (with value lemmas `mOfE_zero_lt`, `mOfE_top`, `mOfE_corner`,
>   `mOfE_eq_zero_of_not_le`).
> - **Gloss.** `mOfE d e p` is a sum of two mutually-exclusive `dite` branches keyed on `p.1 = 0`
>   (low column) vs `p.1 ≥ 1 ∧ p.2 = last` (top row).
> - **Proved.** The definition + the four pointwise value lemmas.
> - **Assumed / Cited / Deferred.** none.

> **Claim (the exact identity, Thm 6.1 substitution).** For **weakly-increasing** `d` (`Monotone d`),
> `codimForm N (extendℤ (mOfE d e)) = G_d(e)` — the Cor 3.5 form of the horizontal-lace module of `e`
> equals the QIP objective `G_d(e) = ∑_{1≤j≤i≤N} e_i(e_j + d_j − d_{j-1})`, exactly.
>
> - **Lean:** `DLNFibre.Core.codimForm_mOfE` (with `extendℤ_in_box`, `extendℤ_mOfE_first`,
>   `extendℤ_mOfE_second`, `sum_Icc_one_eq_fin`). `Gqip d e` is `G_d(e)` over ℤ, `i,j : Fin N` encoding
>   paper `1..N` (`d_j − d_{j-1}` = `d j.succ − d j.castSucc`).
> - **Gloss.** In `codimForm`'s 4-fold sum `∑_{1≤i≤u≤j≤v≤N} M(i-1,j-1)·M(u,v)` with `M = extendℤ(mOfE)`:
>   the first factor is nonzero only at `i=1` (low-column branch, `= e_{j-1}`), the second only at `v=N`
>   (top-row branch, `= e_{u-1}+d_u−d_{u-1}`). Collapsing `i→1`, `v→N` leaves
>   `∑_{1≤u≤j≤N} e_{j-1}(e_{u-1}+d_u−d_{u-1})`, which reindexes (`u-1, j-1 ↦ Fin N`, sum-swap) to `G_d(e)`.
> - **Proved.** The equality, unconditionally given `Monotone d`. `N=0` handled (both sides empty `= 0`).
> - **Assumed.** `Monotone d` (the paper's "weakly increasing" hypothesis; it makes `d_u − d_{u-1} ≥ 0`,
>   so the ℕ-subtraction in `mOfE`'s top-row value is honest — used in `extendℤ_mOfE_second`).
> - **Cited / Deferred.** none.

> **Claim (`mOfE` is a Kostant partition).** For `Monotone d` and feasible `e` (`∑ e = d 0`),
> `mOfE d e ∈ kostantPartitions d 0` (corner `0`).
>
> - **Lean:** `DLNFibre.Core.mOfE_mem` (with `mOfE_kostantAt`).
> - **Gloss.** The Kostant constraint at `k`: the filtered sum telescopes,
>   `∑_{k≤b<N} e_{b+1} + ∑_{1≤a≤k}(e_a+d_a−d_{a-1}) = d_0 + (d_k − d_0) = d_k`, using `∑ e = d_0`
>   (partition of `Fin N` into `b≥k` / `a<k`) and `Finset.sum_range_tsub` (monotone telescope).
>   Support/bound/corner from the value lemmas + `bound_of_kostant`.
> - **Proved.** Membership, given `Monotone d` and `∑ e = d 0`.
> - **Assumed.** `Monotone d`, `∑ i, e i = d 0`.
> - **Cited / Deferred.** none.

> **Claim (the easy `≤`, Thm 6.1 direction).** For `Monotone d`, `cCodim d 0 ≤ qipMin d`, where
> `qipMin d := inf'_{e feasible} G_d(e)` over `qipFeasible d = finAntidiagonal N (d 0)`.
>
> - **Lean:** `DLNFibre.Core.cCodim_le_qipMin` (with `qipMin`, `qipFeasible`, `cCodim_le_Gqip`).
> - **Gloss.** Each feasible `e` gives `mOfE d e ∈ kostantPartitions d 0` with `codimForm = G_d(e)`, so
>   `cCodim` (= `inf' codimForm`) `≤ G_d(e)` (`Finset.inf'_le`); taking `inf'` over `e` (`Finset.le_inf'`)
>   gives `cCodim ≤ qipMin`.
> - **Proved.** The inequality `≤`, given `Monotone d` (+ the two nonemptiness hyps carried by
>   `cCodim`/`qipMin`).
> - **Assumed.** `Monotone d`; `(kostantPartitions d 0).Nonempty`; `(qipFeasible d).Nonempty`.
> - **Cited.** none. (Lineage: the paper's Thm 6.1; only the substitution half is realised.)
> - **Deferred.** (1) The **converse** `cCodim ≥ qipMin` (Lemma 6.4) — NOT here, so `=` is not claimed.
>   (2) The **geometric** reading (`cCodim` = codim of `Σ^0`) still rides on the deferred `hVoigt`, as in
>   Layer 1; `cCodim`/`qipMin` here are min-values of ℤ-quadratic forms over finite sets.

> **Claim (witness, `(2,2,2)` / Ex 6.2).** `(2,2,2)` weakly increasing; `qipMin = 3` attained at
> `e=(1,1)`, whose `mOfE` is the `(1,1)`-orbit `mMin`; the easy `≤` is tight here (`cCodim = 3 = qipMin`).
>
> - **Lean:** `DLNFibre.Core.d222_monotone`, `qipFeasible_d222_nonempty`, `Gqip_d222_eq_three`,
>   `mOfE_d222_eq_mMin`, `qipMin_d222_eq_three`, `cCodim_le_qipMin_d222`.
> - **Proved.** `Gqip d222 (1,1) = 3`, `mOfE d222 (1,1) = mMin` (by `decide`); `qipMin d222 = 3` (by
>   kernel `decide`); the `≤` instance. Tightness here is observed (`cCodim d222 0 = 3` from
>   `Core.CTheta.cCodim_d222_zero`), not a general claim.
> - **Assumed / Cited / Deferred.** none.

---

## Audit

- `python3 scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `lake build` green (2079 jobs); `lake build DLNFibre.Core.CThetaQIP` green, no linter warnings
  (longlines / unused-simp cleaned).
- `#print axioms` on `codimForm_mOfE`, `mOfE_mem`, `cCodim_le_qipMin`, `qipMin_d222_eq_three`,
  `mOfE_d222_eq_mMin`: only `propext`, `Classical.choice`, `Quot.sound`.
- Numerics (sympy, exact): `codimForm(mOfE d e) = G_d(e)`, `mOfE d e` Kostant with corner 0, for ALL
  feasible `e` on `(2,2,2),(2,2,3),(2,3,5,7),(1,4,4,9),(8,8,11,11,11,13,13,13,15)`; `qipMin` = 3 / 55
  on `(2,2,2)` / the `N=8` example (matching Ex 6.2 / 6.3).
- Fidelity review (Lean ↔ informal claim): **PASS** (reviewer, 2026-06-18; decorrelated Codex on the
  `Gqip`/feasible-set encoding). All seven checks survived: `Gqip` ↔ paper `G_d` (no off-by-one,
  `d j.succ − d j.castSucc` correct under the `+1` shift); `qipFeasible = finAntidiagonal N (d 0)` with
  `d 0 = d'_0` under `Monotone d`; `codimForm_mOfE` exact `=` under `Monotone d`; corner 0 = rank-0;
  `cCodim_le_qipMin` is `≤` only, converse correctly Deferred (no overclaim); witnesses internally
  consistent (`qipMin d222 = 3 = cCodim d222 0`); axioms clean. Paper citations verified
  (eq:QIP 1150, Thm 6.1 1155, module M 1247–1264, Lemma 6.4 `lem:horiz_rep` 1230, Ex 6.2 1159).
  Reviewer's non-blocking lint notes (deprecated `Fin.coe_castSucc`, no-op `simp` arg) **fixed**.
- **Status: sorry-free + reviewed.**

## Codex consult

`threads/01-ctheta-design/codex/qip-easy-{prompt,answer}.md` — route for the `codimForm = G` identity
(route C: localize the two reads, collapse `i=1`/`v=N`, reindex `Icc 1 N → Fin N`). Diagnosis used; all
proofs built locally. Codex independently confirmed the math (first-factor forces `i=1`, second `v=N`).

## Judgement calls

- **`mOfE` defined by closed-form entry, not as a `multiplicityArray` of a list.** The KP framework is
  `Fin (N+1)²`-indexed, so a direct piecewise `Fin`-array is the natural carrier; the closed form was
  numerically verified against the lace-diagram sum before formalising.
- **`Gqip` is ℤ-valued.** `d_j − d_{j-1}` is `≥ 0` under `Monotone d` but ℤ avoids ℕ-truncation in the
  objective; `codimForm` is already ℤ-valued, so the identity is a clean ℤ-equality.
- **`N = 0` case split.** `finAntidiagonal 0 (d 0)` and `Icc (1:ℤ) 0` are empty; both sides `= 0`. The
  `i = 1` collapse (`sum_eq_single_of_mem 1`) needs `1 ∈ Icc 1 N`, i.e. `N ≥ 1`, so `N = 0` is peeled
  off first.
