# Statement cards — thread 31 (pin2 germ-charge bridge), 2026-06-25

Worktree HEAD at build: `39c5c441` (merge of `origin/expedition/aoyagi-full` ~`d111fee7`);
lemmas live in the working tree on top of it (uncommitted, controller to integrate).

---

> **Claim (the genuinely new piece).** For two gauge-sliced layers
> `C0 = fromBlocks A0 Y0 Z0 T0`, `C1 = fromBlocks A1 Y1 Z1 T1` (over a CommRing, pivot dim `r`, core
> dim `M`) with `A0, A1` and the global pivot `P = A0·A1 + Y0·Z1` invertible, the GLOBAL (1,1)-block
> Schur complement of `C0·C1` over `P` equals the middle-factor form of the per-layer Schur cores:
> `(Z0Y1+T0T1) − (Z0A1+T0Z1)·⅟P·(A0Y1+Y0T1) = (T0−Z0⅟A0Y0)·(1 − Z1·⅟P·Y0)·(T1−Z1⅟A1Y1)`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schur_product_ldu`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurComparability.lean`)
> - **Gloss.** The Schur complement of a PRODUCT of two block layers, over the product pivot, factors
>   as `S0·(1−K)·S1` with `S_s = T_s − Z_s·⅟A_s·Y_s` the per-layer Schur cores and `K = Z1·⅟P·Y0` the
>   off-pivot correction. This is the `hR : R = S0·(1−K)·S1` antecedent the banked S5c atom
>   `schur_core_germ_comparability` consumes.
> - **Proved.** The exact ring/inverse-cancel identity, all `r, M` (general bidimensional blocks),
>   any CommRing. Route: per-layer block-LDU (`fromBlocks_eq_of_invertible₁₁`) → middle-factor
>   collapse (`schur_middle_ldu_blocks`) → unipotent-strip Schur-invariance (`schur_unipotent_strip`)
>   → final factoring (`factor_one_sub_middle`).
> - **Assumed.** `Invertible A0`, `Invertible A1`, `Invertible (A0·A1 + Y0·Z1)`.
> - **Cited.** Mathlib `LinearAlgebra/Matrix/SchurComplement.lean` (`fromBlocks_eq_of_invertible₁₁`)
>   + `Data/Matrix/Invertible.lean` (rectangular `invOf`-cancel). All axiom-clean.
> - **Deferred.** L = 2 only (two-layer); general-L is a separate telescoping induction, NOT needed
>   for the L = 2 headline.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

> **Claim (the conditional bridge).** The producer's germ charge
> `∃ C ≥ 0, ∀ᶠ w in 𝓝 w0, |frobSq (R w) − coreΦ w| ≤ C·Sreg w` follows from: per-`w`
> `R w = S0 w·(1−K w)·S1 w` (`hR`), `coreΦ w = frobSq (S0 w·S1 w)` (`hCore`), the QUADRATIC remainder
> charge `frobSq (R w − S0 w·S1 w) ≤ Crem·(Sreg w)²` (`hRem`), and eventual boundedness of `coreΦ`,
> `Sreg` near `w0`, with `Sreg ≥ 0`. Explicit constant `C = 2·√(Mc·Crem) + Crem·Bs`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.germ_charge_of_schur_factorization`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGermCharge.lean`)
> - **Gloss.** Given the global Schur factorization, the core identification, and a quadratic-in-Sreg
>   remainder bound, the difference of squared-Frobenius energies of `R` and the core is bounded by a
>   uniform `C·Sreg` on the germ. Built from the S5c difference-of-squared split + Cauchy–Schwarz
>   (`schur_core_germ_comparability` (iii),(iv)) + a `Real.sqrt` bound on the cross term.
> - **Proved.** The implication (abstract, network-free) — the germ charge from the three named
>   hypotheses. Non-vacuity: the antecedents are co-satisfiable with `R − S0·S1 ≠ 0` (docstring witness).
> - **Assumed.** `hR`, `hCore`, `hRem`, `hMcb`, `hBsb`, `hSregNonneg` (as stated).
> - **Cited.** Mathlib `Real.sqrt` lemmas (`sqrt_mul`, `sqrt_sq`, `sqrt_sq_eq_abs`, `sqrt_le_sqrt`).
> - **Deferred (the genuine remaining geometry — NOT done, multi-tide).** The three antecedents are
>   UNBUILT for the producer's actual `Mw, coreΦ, Sreg`:
>     1. `hR` needs the frame-aware per-layer block decomposition `Mw.toBlocks ↔ (C0·C1).toBlocks`
>        (the interior-frame telescope at the BLOCK level — the producer only has the single-matrix
>        telescope `prod F = P0·prod(A)·QL`). `schur_product_ldu` then applies.
>     2. `hCore` needs lemma-1's cores `S'_s = (symm core)_s + schurCorrection_s` matched to
>        `schur_product_ldu`'s `S_s = T_s − Z_s·⅟A_s·Y_s`.
>     3. `hRem` needs the regular-block size estimate `‖Y0‖, ‖Z1‖ ≤ √Sreg` ⟹ `K = O(Sreg)`.
>   Codex (xhigh, decorrelated) + the producer's own comments estimate ~300–1500 LoC, multi-tide.
> - **Route.** Per the frame-stripping cert (thread 31): the LDU is the new piece (DONE); the
>   bridge isolates the remaining build as exactly (1)–(3). The producer's germ-charge `sorry`
>   (`DeepestGaugeConstruction.lean` ~line 2680) is rewritten to cite this bridge + the three named
>   obligations.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## Supporting lemmas (all in `DeepestSchurComparability.lean`, sorry-free, axiom-clean)

- `schur_unipotent_strip` — the (1,1)-Schur complement is invariant under a lower-unipotent left and
  upper-unipotent right factor (`P·⅟P = 1` localizes the cancellation).
- `schur_middle_ldu_blocks` — `D0·(U0·L1)·D1 = fromBlocks P (Y0·S1) (S0·Z1) (S0·S1)`.
- `factor_one_sub_middle` — `a·c − a·k·c = a·(1−k)·c` (the clean final factoring).

## Verification

- Algebra: sympy `schur_product_ldu` identity ALL-ZERO across `(r,M) ∈ {(1,2),(2,1),(2,2),(3,2),(1,3)}`.
- `#print axioms`: `schur_product_ldu`, `germ_charge_of_schur_factorization`,
  `deepestEPivot_regSlice_fderiv` (PIN1) all `[propext, Classical.choice, Quot.sound]` — clean.
  `deepest_gauge_construction` / `deepest_loss_squeeze` still trace `sorryAx` (the 3 remaining
  producer sorries: the germ charge + the 2 L≥3-interior, vacuous at L=2).
