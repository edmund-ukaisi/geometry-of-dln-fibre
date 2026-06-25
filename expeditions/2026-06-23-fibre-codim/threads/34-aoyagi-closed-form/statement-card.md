# Statement card — Aoyagi closed-form bridge (`DLN.Aoyagi.ClosedForm`)

**Status:** original 5 theorems reviewed; **`paper`-prefix def-by-def recovery (theorems 6–9) is
sorry-free + axiom-clean, AWAITING fidelity review** (does `paperEll`/`IsAoyagiEll` faithfully
realise Aoyagi's Definition 3, and is the corrected `(ℓ−1)→ℓ` reading sound?). Original fidelity
review PASS on all of A–D (reviewer: λ-defs transcribe Aoyagi Thm 2 term-by-term, confirmed by
decorrelated Codex; `hr` proven sharp by a 2842-case sweep; `k:Type` pin a non-weakening; helpers
non-vacuous; no overclaiming names).
**File:** `lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean`.
**Commit:** branch `dev` worktree `fibre-codim` (controller to pin SHA at integration).

## What is proved

Five theorems bridge Aoyagi (2023) Theorem 2's displayed RLCT closed form λ to the
Lehalleur–Rimányi `cValue` engine. All objects are over the **sorted shifted widths**
`M := shiftedSorted d r = dminus d r ∘ Tuple.sort (dminus d r)` (a monotone `ℕ`-vector), with
`ℓ = qipM M`, `S = qipS M`, `a = qipRound M`, `δ = qipDelta M`.

1. **`residueA_mul_sub_eq_qipDelta_abs_mul_sub`** (`hN : 1 ≤ N`):
   `residueA·(ℓ − residueA) = |δ|·(ℓ − |δ|)`. Both sides `= ρ·(ℓ − ρ)` for `ρ = S mod ℓ`;
   `residueA ∈ {ρ, ℓ}`, `|δ| ∈ {ρ, ℓ − ρ}`, pinned by `Int.ediv_emod_unique` + the
   landed `two_qipDelta_bounds`.

2. **`two_lambdaCore_eq_cValue`** (`hN : 1 ≤ N`): `2·lambdaCore d r = (cValue M : ℚ)`. THE
   algebraic core. Combinatorial identity `2·activePairSum = S² − Q` (proved here:
   `sq_sum_range_eq_sum_sq_add_two_pair`, `two_pairSum_Icc_eq`), the cValue prefix-sum
   expansion, evenness of the cValue numerator (`= 2·G(witness)`, via the landed
   `cValueNum_eq_two_Gqip_witness`), then clear `4ℓ` and reduce — after part (1) and `|δ|² = δ²`,
   `δ = S − ℓa` — to `S² − δ² = (ℓa)² + 2(ℓa)δ`, a ring identity.

3. **`two_lambda_eq_codimFormula`** (`hN : 1 ≤ N`, **`hr : r ≤ d 0 + d (Fin.last N)`**):
   `2·lambda d r = (codimFormula d r : ℚ)`. `2·lambdaShift = −r² + r(d₀+d_last)`; part (2); the
   `ℕ`-shift de-truncates under `hr` (`Nat.cast_sub`). **`hr` was added by the controller** — the
   no-bound statement is false for `r > d₀ + d_last`.

4. **`codimRepCanonical_fibre_eq_aoyagiCodimFormula`** (`k : Type`):
   `codimRepCanonical (fibre d B) = ((codimFormula d r).toNat : ℕ∞)`. Wiring on the landed central
   theorem `Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift` + in-file
   `codimFormula_eq_cCodim_add_shift`; `Int.toNat_add` splits the shift (`cCodim_nonneg`).

5. **`codimRepCanonical_fibre_eq_two_aoyagiLambda`** (`k : Type`):
   `((codimRepCanonical (fibre d B)).toNat : ℚ) = 2·lambda d r`. From (4) + (3); `hr` derived from
   `h` via `corner_le_dim_of_mem`.

Plus `..._eq_aoyagiCodimOfTarget` (rank filled from `B.rank`).

## Hypotheses / pins (caveats next to the claim)

- **`hr : r ≤ d 0 + d (Fin.last N)` on part (3)** — necessary (ℕ-subtraction de-truncation); supplied
  in the fibre theorems by Kostant nonemptiness (`corner_le_dim_of_mem`).
- **`k : Type` (universe 0) on the three fibre theorems** — pins `k` to match the LR engine's central
  theorem, which is stated at `Type`. Not a mathematical weakening: the result holds for any
  algebraically closed char-0 field (ℂ, ℚ̄ ∈ Type 0); it is the universe the geometric codim identity
  already lives at. Was an auto-bound universe before; pinning is required to apply the dependency.

## Fidelity gap CLOSED — definition-by-definition Aoyagi recovery (`paper`-prefix surface)

The original `ell = qipM` surface is a *value* bridge: it yields Aoyagi's λ value but `ell = qipM`
differs pointwise from Aoyagi's own Definition-3 `ℓ` (e.g. sorted widths `(1,1,2)`: `qipM = 2`,
Aoyagi `ℓ = 1`). A new `paper`-prefixed surface closes that gap, replacing value-equivalence with a
theorem and a definition-by-definition match. All objects over the monotone `M := shiftedSorted d r`;
`qipA M l = (∑_{i=0}^l M_i) − l·M_l` is the (landed `Core`) active threshold.

- **`paperEll M := Nat.findGreatest (fun l ↦ 1 ≤ qipA M l) N`** — Aoyagi's Definition-3 active-set
  size (last index where the active threshold `T_l > l·M_l` is *strict*), vs `qipM`'s `≥ 0`.
- **`coreFormula M ℓ`** — Aoyagi's displayed zero-rank core as a function of cutoff `ℓ`;
  `lambdaCore d r = coreFormula M (qipM M)` and `paperLambdaCore d r = coreFormula M (paperEll M)`
  (both `rfl`/definitional). `paperLambda := lambdaShift + paperLambdaCore` (shift is ℓ-independent,
  shared).

Certification + capstone (all `hN : 1 ≤ N`, `hM0 : 1 ≤ M 0` where the active set is non-degenerate):

6. **`isAoyagiEll_paperEll`** / **`paperEll_unique`**: `paperEll M` is the *unique* solution of
   `IsAoyagiEll M l := 1 ≤ qipA M l ∧ (l = N ∨ qipA M (l+1) ≤ 0)` — Aoyagi's Definition 3 read
   through its binding cases under sortedness (active `qipA ℓ ≥ 1`, inactive `qipA (ℓ+1) ≤ 0`), with
   the source misprint `(ℓ−1)→ℓ` corrected to match her Theorem-1 case rule. Uniqueness rides on
   `qipA_antitone` (monotone `M`).
7. **`paperLambdaCore_eq_lambdaCore`** (unconditional): the two cutoffs give the *same* core. Crux is
   **`coreFormula_step_invariant`** — `coreFormula M ℓ = coreFormula M (ℓ+1)` when `qipA M (ℓ+1) = 0`
   (`1 ≤ ℓ`): the running average `M_{ℓ+1} = T_ℓ/ℓ` is then an integer, both residue terms vanish
   (`a = ℓ`, `a' = ℓ+1`), and the quadratic-term change `−(ℓ/2)(T_ℓ/ℓ)²` cancels the `½·pairSum`
   gain `+(ℓ/2)(T_ℓ/ℓ)²`. Telescoped up the zero-run `paperEll → qipM` (length can exceed 1, e.g.
   `M=[1,1,2,2,2]`: `paperEll=1, qipM=4`). The `M 0 = 0` case: `paperEll = 0` and both cores `0`
   (via **`cValue_eq_zero_of_corner_zero`**, the singleton feasible face `{0}`).
8. **`paperLambda_eq_lambda`** (unconditional): `paperLambda d r = lambda d r`.
9. **`codimRepCanonical_fibre_eq_two_paperLambda`** (`k : Type`): **the headline** —
   `((codimRepCanonical (fibre d B)).toNat : ℚ) = 2 · paperLambda d r`, i.e. codim = 2·(Aoyagi's λ
   with her own Definition-3 ℓ). Rewrites theorem (5) by `paperLambda_eq_lambda`.

`ell = qipM` is retained as the computationally-convenient equal-valued handle.

New reusable `qipA` lemmas (local, lift to `Core` on a second use): `qipA_succ` (general successor
recurrence `qipA (l+1) = qipA l − l(M_{l+1}−M_l)`, generalising `Core.qipA_succ_qipM`),
`qipA_succ_le` / `qipA_antitone` (monotone `M`).

Lean values cross-checked by kernel `decide`: `(1,1,2) ↦ qipM=2, paperEll=1`;
`(1,1,2,2,2) ↦ paperEll=1, qipM=4`.

## New reusable lemmas (kept local; lift to Core on a second use)

- `sq_sum_range_eq_sum_sq_add_two_pair` / `two_pairSum_Icc_eq` — the standard
  `(∑ g)² = ∑ g² + 2·∑_{i<j} g_i g_j` triangular identity over `range`. Network-free; candidates for
  `Core` if reused.

## Verification

`scripts/lb` (whole library) green (3765 jobs); `scripts/sorries` = 0/0/0/0; `#print axioms` on all
theorems (5 original + `paperLambda_eq_lambda`, `codimRepCanonical_fibre_eq_two_paperLambda`,
`isAoyagiEll_paperEll`, `paperEll_unique`, `coreFormula_step_invariant`,
`cValue_eq_zero_of_corner_zero`) = `[propext, Classical.choice, Quot.sound]`. Numerical truth of every
statement pre-verified by the controller (`aoyagi_check.py`, `aoyagi_shift.py`, `paperell_check.py` —
the last checks the zero-run, `paperLambdaCore == lambdaCore` incl. M₀=0, `IsAoyagiEll` uniqueness,
and the corrected-Definition-3 match: 0 violations across 2994 monotone shifted-width vectors).
