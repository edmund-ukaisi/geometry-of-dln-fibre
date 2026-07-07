# Statement card — the relative corank-step invariant (R-BLOWUP crux)

Thread `genm-rblowup` (branch `genm-rblowup`, off `genm-atombuild @6b463d3a`). The single hardest
sub-brick of the general-`(L,S,J)` single-radial blow-up chart lemma: the **relative corank-step
invariant**, at general (opaque) widths. Design source:
`expeditions/2026-06-20-aoyagi-full/threads/genm-sjjoint-design/{chart-lemma-probe,outer-construction-cert,buildability}.md`.

> **Claim.** For a corank block `Δ = fromBlocks A B C D` with invertible `t × t` pivot `A`, coupled to
> ANY downstream product `Q`, Aoyagi's Case-2 single radial blow-up `Δ ↦ u • Δ` factors the
> Frobenius loss as the radial `u²` times a `u`-free Schur-decomposed residual:
> `frobSq ((u • Δ) · Q) = u² · ( frobSq(A · Q̃) + frobSq(C · Q̃ + Γ · Q_b) )`,
> `Q̃ = Q_p + A⁻¹BQ_b`, `Γ = D − CA⁻¹B` (the corank-decremented Schur complement),
> `Q_p, Q_b` the pivot / non-pivot column rows of `Q`. With an accumulated monomial prefactor `pref`,
> the radial `u` and `pref` factor out as the single scalar `pref · u²` and the residual is `u`-free
> and `pref`-free (the sequential-independence invariant).

- **Lean:** `DLNFibre.DLN.RLCT.corankStep`, `…corankStep_prefactor`, `…corankStep_sequential`
  (+ the radial pieces `frobSq_smul`, `frobSq_smul_mul`, `frobSq_smul_fun`)
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankStep.lean` @ `<commit-sha>`)
- **Gloss.**
  - `frobSq_smul_mul (u M Q) : frobSq ((u • M) * Q) = u² * frobSq (M * Q)` — the single radial factors
    cleanly out of the coupled product, for ANY downstream `Q` and ANY (opaque `Fintype`) widths
    (Z-agnostic; step 1 of the chart-lemma probe).
  - `corankStep (u A B C D Q) [Invertible A]` — the composed step: radial factor ∘ the banked exact
    Schur block-elimination `frobSq_schur_block_split`, giving `u² · (pivot energy + corank residual)`,
    the corank residual `frobSq(C·Q̃ + Γ·Q_b)` carrying the corank-decremented Schur complement `Γ`
    genuinely cross-coupled with `C·Q̃`.
  - `corankStep_prefactor (pref u …)` — the prefactor rides out untouched as `pref · u²`.
  - `corankStep_sequential (u₁ u₂ …)` — `corankStep_prefactor` at `pref := u₁²`: two successive
    radials accumulate as the product monomial `u₁² · u₂²`, deepest residual free of both.
- **Proved.** All statements are exact pointwise matrix identities over general `Fintype` index types
  (opaque widths), sorry-free. `#print axioms = [propext, Classical.choice, Quot.sound]` for
  `frobSq_smul`, `frobSq_smul_mul`, `corankStep`, `corankStep_prefactor` — **S2-free** (no
  `monomial_rlct`, no `sorryAx`): the chart geometry is clean, as required.
- **Assumed.** `[Invertible A]` on the pivot block (Aoyagi's blow-up normalises the top-left pivot; for
  the single-corank step `t = 1`, `A = (1)` invertible). No other hypotheses — Z-agnostic in `Q`.
- **Cited.** none. Builds only on the banked exact `frobSq_schur_block_split` (RouteMSJChartAlgebra,
  itself sorry-free) and Mathlib `Matrix.smul_mul`.
- **Deferred (the remaining sub-tides of the chart lemma).**
  1. **The measure-theoretic Morse peel** of the pivot energy `frobSq(A·Q̃)` — integrating out the
     freed pivot rows/cols, contributing the charge. Banked engine: `radial_morse_residual_power_le`;
     the weld of `corankStep`'s output onto it is NOT done here (this card is the *pointwise* identity).
  2. **The recursion / advance-`(S,J)`**: re-casting the corank residual `frobSq(C·Q̃ + Γ·Q_b)` into the
     next step's `(u' • fromBlocks A' B' C' D') · Q'` form (pivot-chart cover on `Γ`,
     `pivotChartCover_matBox_le_sum` / `pivotLocus_eq_iUnion`), so `corankStep_prefactor` re-fires with
     `pref := (accumulated ∏ uⱼ²)`. The prefactor slot already accepts any prior monomial.
  3. **The DLN-loss bridge**: identifying `dlnLoss M` / `chartParamsGen` at opaque widths with the
     abstract `frobSq((u • Δ) · Q)` core (the `Wext`/`Text` dependent-width cast work).
  4. **Exponent bookkeeping** (`= Mval ≥ minAdm`, threshold-monotonicity `0/171`) — banked
     (`minAdmRec_eq_minAdm`, `sjChargeUpdate_accum`, `sjSubordination`); the base `L = 1`
     (`sjBase1_freeMatrix`) + monomial endpoint (`monomialIntegrand_integrable_of_lt`,
     `monomialThreshold_ge_of_mult`) close the terminal leaves. These wire into `sjJointResolution`'s
     open sorry, which stays untouched until the full degenerate-strata finiteness lands.
- **Structure & ideas observed (from the design certs).** The crux both p&p and decorrelated Codex
  named is exactly the sequential-independence invariant: "old exceptional coordinates are passive
  monomial prefixes on the active residual; each later downstream resolution is pulled back under a
  monomial prefix — `φ*(u²·G) = u²·φ*(G)`". `corankStep_prefactor` is the pointwise algebraic core of
  this: because the residual is `u`-free and `pref`-free, no later blow-up centre ever divides the
  earlier prefix — the resolution is sequential, not simultaneous. The corank-≥2 sharing is encoded
  natively by ONE radial `u` per block (the shared `u`, correct/lower RLCT), not recovered from a Gram
  ideal — so `corankStep` avoids the R-ATOM Gram-det principalisation B-trap: the Gram determinant
  never forms; the Schur complement `Γ` is produced by the exact unit-triangular elimination, not by
  principalising `det(Q_b Q_bᵀ)`.
- **Route.** R-BLOWUP (validated `A`; buildability + chart-lemma-probe green-lit). This card banks the
  exact pointwise identity (steps 1 + 3, and step 2's exact algebra via the banked block split). The
  measure-theoretic and recursion pieces are the subsequent sub-tides above.
- **Status.** sorry-free; axiom-clean (S2-free); reviewer fidelity check pending.
