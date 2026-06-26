# Statement card — S5c germ atom: the Schur-core germ comparability (#44c, thread 31)

> **Claim.** For the L=2 reduced core, the GLOBAL product Schur complement `R` (written in
> middle-factor form `R = S0·(1−K)·S1`, `K = Z1·A⁻¹·Y0` the off-pivot correction) and the product of
> the per-layer Schur cores `∏S = S0·S1` are comparable **on the deepest-point germ** (NOT uniformly
> on a coordinate box): the exact remainder identity `R − ∏S = −S0·K·S1`, the Frobenius
> sub-multiplicative remainder bound, and the difference-of-squared-Frobenius split with a
> Cauchy–Schwarz-bounded cross term.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schur_core_germ_comparability`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestSchurComparability.lean`, NEW file this tide, @ `1a8dd0cf`).
>
> - **Statement (bundled, network-free; `M : Type*` `[Fintype M] [DecidableEq M]`,
>   `S0 S1 K R : Matrix M M ℝ`, `hR : R = S0 * (1 - K) * S1`):**
>   - (i) `R - S0 * S1 = - (S0 * K * S1)` — the exact remainder ring identity;
>   - (ii) `frobSq (R - S0*S1) ≤ frobSq S0 * frobSq K * frobSq S1` — the sub-multiplicative bound;
>   - (iii) `frobSq R = frobSq (S0*S1) + 2·(∑ᵢⱼ (S0*S1)ᵢⱼ·(R−S0*S1)ᵢⱼ) + frobSq (R−S0*S1)` — the
>     difference-of-squared-Frobenius split;
>   - (iv) `(∑ᵢⱼ (S0*S1)ᵢⱼ·(R−S0*S1)ᵢⱼ)² ≤ frobSq (S0*S1) · frobSq (R−S0*S1)` — Cauchy–Schwarz on
>     the cross term.
>   where `frobSq X := ∑ᵢ ∑ⱼ (X i j)²`.
>
> - **Gloss.** From the exact block-LDU middle-factor form (cert `s5c-r2-cert.md`, `s5c-cert.md`), the
>   remainder is `−S0·K·S1` with `K = Z1·A⁻¹·Y0 = O(ε²)`, so `frobSq(R−∏S) = O(ε⁶)` is strictly higher
>   order than `frobSq ∏S = O(ε⁴)`. (i)–(iv) reduce the in-sum germ bound `|frobSq R − frobSq ∏S| ≤
>   2·⟨∏S,R−∏S⟩ + frobSq(R−∏S)` to the remainder energy, which the consumer charges to the regular
>   energy `∑E²` via `‖Y0‖,‖Z1‖ ≤ √(∑E²)`.
>
> - **Proved (unconditionally).** (i)–(iv) above + supporting `frobSq_nonneg`, `frobSq_neg`,
>   `frobInner_sq_le`, `frobSq_add_eq`, `schur_core_remainder_identity`,
>   `schur_core_remainder_frobeniusSq_le`. All from `frobenius_mul_le` (DeepestGaugeBlocks) +
>   `Finset.sum_mul_sq_le_sq_mul_sq` (Mathlib Cauchy–Schwarz) + `Fintype.sum_prod_type'`. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`; zero `sorry`/`axiom`/`native_decide`.
>   Non-vacuity: an in-file `example` (scalar `M = Fin 1`, all blocks `= 1/2`) exhibits `K ≠ 0` and
>   `R − ∏S ≠ 0` (the bound is sharp — equality `t⁶ = t²·t²·t²` in the scalar full-rank case).
>
> - **Assumed.** The middle-factor identity `R = S0·(1−K)·S1` is taken as a HYPOTHESIS (`hR`), not
>   re-derived from the full block-LDU. The block-LDU derivation of this identity (and `K =
>   Z1·A⁻¹·Y0`, `A = a0a1 + Y0Z1`) is a separate, heavier obligation living in the `framedParams`
>   apparatus, NOT in this atom.
>
> - **Cited.** none external.
>
> - **Deferred (named, NOT done here).** The `∑E²` charge (`frobSq K ≤ C·∑E²`) — depends on the
>   `deepestSplit`/regular-block apparatus; lives in `hproducer` (`framedParams_split_eq_frame_raw`).
>   The atom delivers the network-free matrix-algebra core only.
>
> - **Status.** sorry-free, axiom-clean; the named S5c deliverable of thread 31.

## The kill-condition this atom's germ-scoping reflects (thread 31, 2026-06-25)

The atom is GERM-scoped (the difference bound, not a multiplicative ratio) BECAUSE the uniform
two-sided multiplicative comparability `∑‖R‖² ≍ ∑‖∏S‖²` is **FALSE for M > 1** even on a germ.
Decorrelated Codex (`xhigh`, `codex/hproducer-de-soundness-{prompt,answer}.md`) + numeric witness
(`/tmp/s5c_germ_counterex.py`, reproduced): the germ path `W = I + η·E₁₂` (tilted kernel, realized by
`Z1 = √η·e₁, Y0 = −√η·e₂ᵀ`, both `O(√η) → 0`, `A = a0a1 = I`), `S1 = ε·e₂e₁ᵀ`,
`S0 = ε·e₁(e₁ᵀ − η·e₂ᵀ)` gives `R = S0·W·S1 = 0` EXACTLY while `∏S = −ε²η·E₁₁ ≠ 0`. So
`‖R‖² = 0` but `‖∏S‖² = ε⁴η² > 0` arbitrarily close to the deepest point — no finite `γ₁` makes
`coreΦ ≤ γ₁·‖R‖²` hold. (A first random-direction numeric hunt MISSED this — the witness is the
measure-zero `S0 ⟂ W·S1` aligned direction; the empty generic hunt was not a proof.)

**Consequence (applied this tide):** the consumer `framedParams_split_eq_frame_raw`'s conjuncts (d)/(e)
were the FALSE multiplicative form; they are now RESTATED to the regular-energy-FOLDED comparability
`Sreg + ‖R‖² ≍ Sreg + coreΦ` (the `core_comparability_squeeze` shape, the absolute germ bound this atom
+ the `∑E²` charge yield). `deepest_loss_squeeze` is rewired (constants `c₁ = (γ₁·Klo)⁻¹`,
`c₂ = Kup·γ₂`); its public conclusion is unchanged; the build stays green.
