# Statement card — explicit-formula bridges: square completion + integer-square optimality

Module `lean/DLNFibre/Core/CThetaExplicit.lean` (new file, imports `Core.CThetaQIP`). Two **standalone
ℤ-algebra** facts toward the explicit `(C, θ)` closed form (Lehalleur–Rimányi Thm 7.10), proved
independently of the drop-to-m reduction (thread `06-drop-to-m`) and the value assembly. Import appended
to `DLNFibre.lean` (single-writer). Commit `ff0b3182dd8314354133fd642dbf5a617cda363b`.

**Scope (name = content).** These are the two *algebraic* steps of the Thm 7.10 tail in isolation: the
square completion that turns `min Gqip` into a nearest-integer-point problem, and the integer optimum of
`∑ t²` under a fixed sum. They do **not** assemble the closed-form `C`, do **not** prove drop-to-m, and
do **not** touch `cCodim`/`qipMin` — those are later tides. No geometric (Voigt) content.

---

> **Claim (square completion).** With `s i := (d 0 : ℤ) − d i.succ`, for every `e : Fin N → ℤ`
> `2·G_d(e) − (∑_i e_i)² = ∑_i (e_i − s_i)² − ∑_i s_i²`, where `G_d(e)` is the QIP objective
> `∑_{1≤j≤i≤N} e_i(e_j + d_j − d_{j-1})` (over ℤ).
>
> - **Lean:** `DLNFibre.Core.two_Gqipℤ_sub_sq` (with `Gqipℤ`, `Gqipℤ_eq_Gqip`, `qipShift`, and helpers
>   `two_tri_ee_sub_sq`, `sum_tri_diff`).
> - **Gloss.** `Gqipℤ d e` is `Gqip`'s objective with the variable `e` taken in ℤ (the committed `Gqip`
>   takes `e : Fin N → ℕ`); `Gqipℤ_eq_Gqip` shows `Gqipℤ d (↑e) = ↑(Gqip d e)` for a cast ℕ-vector.
>   `qipShift d i = d 0 − d i.succ`. The identity splits `Gqipℤ` into an `e·e` triangle and an
>   `e·(d_{j+1}−d_j)` part; the triangle gives `2∑_{j≤i}e_i e_j − (∑e)² = ∑ e_i²` (`two_tri_ee_sub_sq`,
>   by `i<j`/`j<i` symmetry collapsing to the diagonal), and the second telescopes
>   `∑_{j≤i}(d_{j+1}−d_j) = d_{i+1} − d_0` (`sum_tri_diff`) `= −s_i`, matching the cross-term `−2∑ e_i s_i`.
> - **Proved.** The ℤ-identity, unconditionally (all `e : Fin N → ℤ`, all `N` incl. `N = 0`). No
>   monotonicity or feasibility hypothesis is needed for the algebra.
> - **DEVIATION from the chart.** The brief transcribed `s_i = d'_0 − d'_i`. Unfolding the **committed**
>   `Gqip` shows the true shift in the Lean indexing is `s_i = d 0 − d i.succ` (the paper's `d'_i`,
>   `i = 1..N`, is `d i.succ` here, not `d i`). The proven statement uses the true `s`. Verified by
>   sympy against `Gqip` for `N = 1..6` (`scratch`), and the Lean `ring`/telescope reproves it.
> - **Assumed / Cited / Deferred.** none. (Feeding this into `min Gqip ⇔ min ‖e − s‖²` on the feasible
>   face `∑ e = d 0`, and thence into `cCodim`/`qipMin`, is a later tide — Deferred there, not here.)

> **Claim (integer-square optimality).** For `m : ℕ`, `δ : ℤ` with `|δ| ≤ m`, `|δ|` is the least
> attainable `∑_i t_i²` over `t : Fin m → ℤ` with `∑_i t_i = δ`; i.e. `min{∑ t² : ∑ t = δ} = |δ|`,
> attained.
>
> - **Lean:** `DLNFibre.Core.isLeast_sumSq : IsLeast (sumSqValues m δ) |δ|` (with `sumSqValues`,
>   `abs_le_sumSq`).
> - **Gloss.** `sumSqValues m δ = {v | ∃ t, ∑ t = δ ∧ ∑ t² = v}`. `IsLeast` = `|δ| ∈ sumSqValues ∧ |δ| ∈
>   lowerBounds`. Attainment: the explicit witness `t i = if (i:ℕ) < δ.natAbs then δ.sign else 0` has
>   `∑ t = δ.natAbs · δ.sign = δ` (`Int.sign_mul_natAbs`) and `∑ t² = δ.natAbs · δ.sign² = δ.natAbs =
>   |δ|`; the count `δ.natAbs` of nonzero coords needs `δ.natAbs ≤ m`. Lower bound (`abs_le_sumSq`):
>   `|δ| = |∑ t| ≤ ∑|t_i| ≤ ∑ t_i²` via `Int.natAbs_le_self_sq` and `Finset.abs_sum_le_sum_abs`.
> - **Proved.** Both halves. The **lower bound `abs_le_sumSq`** holds for every feasible `t` with **no**
>   bound on `|δ|`; the `|δ| ≤ m` hypothesis is used **only** for attainment (to fit `|δ|` nonzero
>   coords into `m` slots).
> - **Cited.** none — this **replaces** the Conway–Sloane closest-vector black box with a direct
>   integer argument (the exchange/rounding optimum), as the design flagged.
> - **Assumed.** `|δ| ≤ m` (for attainment). **Deferred.** none.

> **Claim (witnesses, non-vacuity).** Square completion at `(2,2,2)`, `e = (1,1)`: LHS `2·G_d(1,1) −
> (∑e)² = 2`; integer-square optimum at `m = 3`, `δ = 2`: least value `= 2`.
>
> - **Lean:** `DLNFibre.Core.two_Gqipℤ_sub_sq_d222` (`= 2` by `decide`), `isLeast_sumSq_3_2`
>   (`IsLeast (sumSqValues 3 2) 2`).
> - **Proved.** The LHS evaluates to `2` (and the identity's RHS `∑(e_i−s_i)² − ∑ s_i² = 2` with
>   `s = (0,0)`, checked by `decide`); the `m=3,δ=2` optimum is `2` (witness `t = (1,1,0)`).
> - **Assumed / Cited / Deferred.** none.

---

## Audit

- `lean/scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `lake build` green (2082 jobs); `lake build DLNFibre.Core.CThetaExplicit` green, no linter warnings.
- `#print axioms` on `two_Gqipℤ_sub_sq`, `isLeast_sumSq`, `abs_le_sumSq`, `Gqipℤ_eq_Gqip`, and both
  witnesses: only `propext`, `Classical.choice`, `Quot.sound`.
- Numerics (sympy, exact): square-completion identity holds for `N = 1..6` against the committed `Gqip`
  (recovers `s_i = d 0 − d i.succ`, NOT `d'_0 − d'_i`); integer-square optimum `min ∑ t² = |δ|` for all
  `m = 1..4`, `|δ| ≤ m` (brute force).
- **Status: sorry-free.** Fidelity review pending (reviewer requested).

## Judgement calls

- **`Gqipℤ` vs `Gqip`.** Stated the algebra over `e : Fin N → ℤ` (where `ring` works), with
  `Gqipℤ_eq_Gqip` as the bridge back to the committed ℕ-valued `Gqip`. The minimisation tide will use
  the cast.
- **`s_i = d 0 − d i.succ`, not the chart's `d'_0 − d'_i`.** Adjusted to what the committed `Gqip`
  actually is; name = content. The sign is chosen so the cross-term `−2∑ e_i s_i` matches.
- **Lower bound carries no `|δ| ≤ m`.** Factored `abs_le_sumSq` out as the weakest-hypothesis half; only
  attainment needs the slot count.
