# thread 01 — arbitrary-ctheta  (formalisation / tide)

**Type:** formalisation (tide) · `OPENED → SPECIFY → PROVE → AUDIT`.
**Goal:** an explicit closed-form `(C, θ)` for an **arbitrary** (non-monotone) dimension vector `d`,
composing the merged sort bridge with the `Monotone d`-gated `cValue`/`cTheta`.

## Target statements (new `Core` module, e.g. `CThetaArbitrary`)

For `1 ≤ N` and (general-`r`) `r ≤ d k` everywhere — nonemptiness discharged via
`kostantPartitions_nonempty_of_le`:

- **C, `r = 0`:** `cCodim d 0 _ = cValue (d ∘ Tuple.sort d)`.
- **θ, `r = 0`:** `numTop d 0 _ = cTheta (d ∘ Tuple.sort d)`.
- **general `r`** (via `cCodim_rankShift` / `numTop_rankShift`):
  `cCodim d r _ = cValue ((dminus d r) ∘ Tuple.sort (dminus d r))`, and likewise `numTop`/`cTheta`.

## Route (all ingredients landed — see synthesis.md for file:line)

`cCodim d 0` =[`cCodim_comp_sort`, symm]= `cCodim (d ∘ sort d) 0` =[`cCodim_eq_qipMin`, `Monotone`]=
`qipMin (…)` =[`qipMin_eq_cValue`]= `cValue (d ∘ sort d)`. θ via `numTop_comp_sort` +
`numTop_zero_eq_cTheta`. Discharge `Monotone (d ∘ Tuple.sort d)` with the Mathlib `Tuple.sort` lemma
(find exact name); `(qipFeasible (sorted)).Nonempty` via `kostant_nonempty_iff_qipFeasible_nonempty`.

## AUDIT gate

`scripts/sorries` clean; axiom-clean `[propext, Classical.choice, Quot.sound]`; a **non-monotone**
witness by `decide +kernel` (e.g. `(2,3,2)` or `(1,2,1)` at `r=0`): `cCodim = cValue(sorted)` and
`numTop = cTheta(sorted)` — demonstrating it fires off the monotone case. Reviewer confirms the Lean
statement = "explicit `(C,θ)` for arbitrary `d`" (name = content; no hidden `Monotone` hypothesis).

## Scope guards

`Core`-only (no `DLNFibre.DLN`); nothing named `rlct_`. `decide +kernel`, not `native_decide`.

## Notes / progress

### 2026-06-23 — tide complete, ALL FOUR targets (r=0 + general-r) green

**Module:** `lean/DLNFibre/Core/CThetaArbitrary.lean` (new, 4 main theorems + 9 witness/support lemmas).
Aggregated: appended `import DLNFibre.Core.CThetaArbitrary` at the END of `lean/DLNFibre.lean`
(controller verifies — the only aggregator edit).

**Theorems (full signatures):**
- `cCodim_zero_eq_cValue_comp_sort (hN : 1 ≤ N) (d) (h : (kostantPartitions d 0).Nonempty) :
  cCodim d 0 h = cValue (d ∘ Tuple.sort d)`
- `numTop_zero_eq_cTheta_comp_sort (hN : 1 ≤ N) (d) (h : (kostantPartitions d 0).Nonempty) :
  numTop d 0 h = cTheta (d ∘ Tuple.sort d)`
- `cCodim_eq_cValue_comp_sort (hN : 1 ≤ N) (d) (r)
  (h : (kostantPartitions d r).Nonempty) : cCodim d r h = cValue (dminus d r ∘ Tuple.sort (dminus d r))`
- `numTop_eq_cTheta_comp_sort (hN : 1 ≤ N) (d) (r)
  (h : (kostantPartitions d r).Nonempty) : numTop d r h = cTheta (dminus d r ∘ Tuple.sort (dminus d r))`

All four match the suggested shapes (general-r dropped the suggested `hr : ∀ k, r ≤ d k` — see
post-review note below). The r=0 proofs follow the brief's route verbatim
(proof-irrelevance on `h` is automatic — `rw [← cCodim_comp_sort …]` matches the LHS witness up to
defeq, no manual `Subsingleton.elim` needed). The general-r proofs are 2-line rank-shifts onto the
r=0 theorem applied to `dminus d r` (same `N`, so `hN` carries unchanged).

**Mathlib `Monotone`-sort lemma:** `Tuple.monotone_sort (f : Fin n → α) : Monotone (f ∘ Tuple.sort f)`
(`Mathlib/Data/Fin/Tuple/Sort.lean:97`). Also used `Tuple.comp_sort_eq_comp_iff_monotone` (:179) for
the concrete witness rewrite. `Mathlib.Data.Fin.Tuple.Sort` arrives transitively via
`CThetaPermInvariance`.

**Witness (non-monotone, `(2,3,2)`):** `d232 = ![2,3,2]`, `not_monotone_d232` (`d 1 = 3 > 2 = d 2`).
Kostant side by `decide +kernel`: `cCodim_d232_zero = 4`, `numTop_d232_zero = 2`. Bridge instances
`cCodim_d232_eq_cValue_comp_sort` / `numTop_d232_eq_cTheta_comp_sort` apply the arbitrary-`d`
theorems to the non-monotone vector. `Tuple.sort` does NOT kernel-reduce (routes through
`Multiset.sort`), so `d232_comp_sort` rewrites `![2,3,2] ∘ sort = ![2,2,3]` via the swap `(1 2)` +
`comp_sort_eq_comp_iff_monotone`; then `cValue_d232_comp_sort = 4`, `cTheta_d232_comp_sort = 2` by
`decide +kernel`. Both sides land on `(C, θ) = (4, 2)` — matching perm-invariance.

**AUDIT:** whole-library `lake build` green (3696 jobs); `scripts/sorries` → `0 sorry, 0 #exit,
0 native_decide, 0 axiom`; `#print axioms` on each theorem → `[propext, Classical.choice, Quot.sound]`
(`not_monotone_d232` → `[propext]`). Statement card written (`statement-card.md`).

**Deviation from route:** none of substance. Completed general-r (targets 3,4) — the suggested
`dminus d r ∘ Tuple.sort (dminus d r)` shape was clean (not awkward), so I did not stop at r=0.
The `decide +kernel`-on-sorted heaviness anticipated by the brief did materialize (sort is not
kernel-reducible), handled exactly as the brief's fallback allowed (concrete-number route through
`![2,2,3]`).

**Post-review hardening (weakest hypotheses):** the reviewer + Codex both flagged that the suggested
`hr : ∀ k, r ≤ d k` on the general-r theorems is logically redundant — `corner_le_dim_of_mem`
(`CCodimCornerMono`) derives `∀ k, r ≤ d k` from any member of `(kostantPartitions d r)`, which `h`
already provides. Dropped `hr` from both general-r signatures and recover it internally via
`fun k ↦ corner_le_dim_of_mem h.choose_spec k`. This is the strictly more applicable (weakest-
hypothesis) form. Re-audited: whole-library green, sorries 0, axioms clean. Statement card updated.
