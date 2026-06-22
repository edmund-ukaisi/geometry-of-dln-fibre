# Statement card — Thm 5.5 (M4) → Cor 5.10 (M6): the expedition headline

Thread 17 (perm-invariance expedition). The closed form of the corner-graded generating function and
its payoff: the combinatorial `(C, θ)` is invariant under permuting the dimension vector.

> **Claim (Cor 5.10).** For every dimension vector `d : Fin (N+1) → ℕ`, rank `r` with `r ≤ d k` at
> every vertex, and permutation `σ : Equiv.Perm (Fin (N+1))`:
> `cCodim (d ∘ σ) r = cCodim d r` and `numTop (d ∘ σ) r = numTop d r`.
>
> - **Lean:** headlines `cCodim_comp_perm`, `numTop_comp_perm` in `DLNFibre.Core.CThetaPermInvariance`
>   (`lean/DLNFibre/Core/CThetaPermInvariance.lean` @ `c534303`, branch `expedition/perm-invariance`).
> - **Proof.** `Qseries_comp_perm` (`Qseries (d ∘ σ) r = Qseries d r`) feeds the LANDED M5 bridge
>   `cCodim_eq_of_Qseries_eq` / `numTop_eq_of_Qseries_eq`. `Qseries_comp_perm` is immediate from Thm 5.5
>   (`thm55`): both sides equal `P r · ∑_s altP s · Pmult (· − r − s)`, where the corner range `min d − r`
>   is a multiset invariant (`minDim_comp_perm`) and the only `d`-dependent factor `Pmult (d − r − s)` is
>   manifestly multiset-symmetric (`Pmult_sub_comp_perm`, LANDED M6-prep, with `d i − r − s = d i − (r+s)`).
> - **Proved.** Unconditionally, axiom-clean. `#print axioms cCodim_comp_perm` /
>   `numTop_comp_perm` / `Qseries_comp_perm` = `[propext, Classical.choice, Quot.sound]`.

> **Claim (Thm 5.5, M4).** `Qseries d r = P r · ∑_{s=0}^{min d − r} altP s · Pmult (d − r − s)` for
> `r ≤ d k` everywhere, `altP s := (−1)^s · X^{s(s−1)/2} · P s`.
>
> - **Lean:** headline `thm55` in `DLNFibre.Core.QSeriesThm55` (@ `9029919`). The `r = 0` case
>   `thm55_zero`: `Qseries d 0 = ∑_{s=0}^{min d} altP s · Pmult (d − s)`.
> - **Proof chain (cert thread-17, exact-verified):**
>   - **S1' (`Qseries_corner_shift`, `QSeriesShift` @ `e0cf885`):** `Qseries d s = P s · Qseries (d − s) 0`
>     (`0 ≤ s ≤ min d`). A `Finset.sum_image` over the LANDED `dropCorner` bijection: the `codimForm`
>     exponent is corner-blind (`codimForm_update_corner`), and `Pm N m = P s · Pm N (dropCorner m)`
>     (`Pm_dropCorner`).
>   - **Range-gap (`Qseries_eq_zero_of_min_lt`):** `Qseries d r = 0` for `min d < r` (corner `r` forces
>     `d_k ≥ r`; `kostantPartitions d r = ∅`).
>   - **S2 (`Pmult_eq_sum_corner`):** `Pmult d = ∑_{s=0}^{min d} P s · Qseries (d − s) 0`, from the LANDED
>     fivegon `∑_s Qseries d s = Pmult d` + S1' + the gap.
>   - **ORTH (`orth`, `QSeriesOrth` @ `200204a`):** `∑_{k=0}^u altP k · P (u−k) = [u = 0]`. The one
>     classical q-input, with NO q-library — a single-variable induction on the LANDED
>     `P_mul_one_sub_succ` via `altP_mul_one_sub` (AA) + `orth_recurrence`
>     (`O (v+1)·(1−X^{v+1}) = (1−X^v)·O v`, the split-distribute + `sum_range_succ'` peel/reindex).
>   - **S3 (`thm55_zero`):** substitute S2 into `∑_s altP s · Pmult (d−s)`, triangle-reindex
>     `(s,t) ↦ (s+t, s)` (`sum_triangle_reindex`, a `sum_bij'` over sigmas), factor the `k`-independent
>     `Qseries (d−u) 0`, collapse by ORTH.
>   - **S4 (`thm55`):** S1' to peel `P r`, then S3 at `d − r` (`dminus_dminus`: `(d−r)−s = d−(r+s)`).
> - **Proved.** Axiom-clean (`[propext, Classical.choice, Quot.sound]`).

- **Assumed / Cited.** None new. Builds on LANDED M1 (`QSeries`), M2 (`durfee` / `P_mul_one_sub_succ`),
  fivegon S0 (`sum_Qseries_eq_Pmult`), the corner bijection (`CTheta.dropCorner` family,
  `codimForm_update_corner`), the M5 bridge, and M6-prep (`Pmult_sub_comp_perm`). q-series support is
  absent from Mathlib v4.29; this reproves the needed fragment (incl. orthogonality) from scratch.
- **Precision (controller-flagged, observed).** The headline is `cCodim`/`numTop` (combinatorial
  codimension / component count) permutation-invariance, NOT an `rlct` result — the `rlct = ½·codim`
  reading stays Cited (Aoyagi/Watanabe). Named `cCodim_comp_perm` / `numTop_comp_perm`, never `rlct_…`.
- **Status.** sorry-free, green, axiom-clean. **AUDIT (fidelity) pending** — a reviewer must confirm the
  Lean `thm55` / `cCodim_comp_perm` / `numTop_comp_perm` statements match the paper's Thm 5.5 / Cor 5.10
  (esp. that the `r ≤ d k` and nonemptiness hypotheses are the right ones, and `altP`/`minDim` faithfully
  encode `(−1)^s q^{C(s,2)} P_s` / `min d`).

## Build / hygiene
- `lake build DLNFibre` (full): green (3693 jobs). The four files: 0 sorry / 0 axiom / 0 native_decide.
- New modules `QSeriesShift`, `QSeriesOrth`, `QSeriesThm55` are pulled into the library **transitively**
  via `CThetaPermInvariance` (already in `DLNFibre.lean`). Controller may add explicit aggregator imports
  for clarity (single-writer rule — left to the controller).

## v4.29 gotchas found
- `Finset.range_subset` is `range n ⊆ s ↔ ∀ x < n, x ∈ s` here; for `range m ⊆ range n ↔ m ≤ n` use
  `Finset.range_subset_range`.
- `Finset.sum_sigma'` is `∑∑ = ∑ over sigma` (forward turns the double sum into a sigma; do NOT use `←`).
- The exponent identity `(k+1)·k/2 = k + k·(k−1)/2` (ℕ division) is cleanest via the Pascal recurrence
  `Nat.choose_succ_succ` + `Nat.choose_two_right` + `omega`, not raw `omega` on the products.
- `ℤ⟦X⟧` is an integral domain — cancel `(1−X^n)` (a non-zero-divisor, `one_sub_X_pow_ne_zero`) via
  `mul_eq_zero`, not `mul_left_cancel₀`.
- `one_sub_pow_split` already exists in `QSeriesDurfee` with a different shape — name the `k ≤ u` variant
  `one_sub_pow_split_le`.
