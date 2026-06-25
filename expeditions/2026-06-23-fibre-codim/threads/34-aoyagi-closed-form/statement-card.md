# Statement card — Aoyagi closed-form bridge (`DLN.Aoyagi.ClosedForm`)

**Status:** reviewed — sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Fidelity
review PASS on all of A–D (reviewer: λ-defs transcribe Aoyagi Thm 2 term-by-term, confirmed by
decorrelated Codex; `hr` proven sharp by a 2842-case sweep; `k:Type` pin a non-weakening; surrogate
note honest, (1,1,2) and 2994-case value agreement confirmed; helpers non-vacuous; no overclaiming
names). Docstring polish applied (lambda/lambdaCore now flag the surrogate inline).
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

## Fidelity note (carried from the module docstring)

`ell = qipM`, `ceilingM`, `residueA` are the LR-engine surrogates (built from `qipM`/`qipS`/`qipRound`
on `shiftedSorted`), **not** Aoyagi's Definition 3. They yield the same λ *value* (part (1) + (2),
verified 0 mismatches on ~3000 inputs) but `ell = qipM` need not equal Aoyagi's `Card(𝓜) − 1`
pointwise (e.g. sorted widths `(1,1,2)`: `qipM = 2`, Aoyagi `ℓ = 1`; same λ). This is a *value* bridge,
not a *definition-by-definition* match — reviewer should confirm the surrogate framing is acceptable
for the intended downstream use (the RLCT payoff reads only the λ value).

## New reusable lemmas (kept local; lift to Core on a second use)

- `sq_sum_range_eq_sum_sq_add_two_pair` / `two_pairSum_Icc_eq` — the standard
  `(∑ g)² = ∑ g² + 2·∑_{i<j} g_i g_j` triangular identity over `range`. Network-free; candidates for
  `Core` if reused.

## Verification

`scripts/lb` (whole library) green; `scripts/sorries` = 0/0/0/0; `#print axioms` on all five theorems =
`[propext, Classical.choice, Quot.sound]`. Numerical truth of every statement pre-verified by the
controller (`expeditions/2026-06-23-fibre-codim/aoyagi_check.py`, `aoyagi_shift.py`).
