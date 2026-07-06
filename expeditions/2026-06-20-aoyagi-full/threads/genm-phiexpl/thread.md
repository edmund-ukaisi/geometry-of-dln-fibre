# Thread `genm-phiexpl` — the L=2 D1 explicit Schur corner-elimination chart

GOAL: close `d1ge_L2_hAtV_explicit` (`D1L2ExplicitCoreProducer.lean`), the sole remaining L=2 headline
crux, making `aoyagi_learning_coefficient_L2` sorry-free.

Status at handoff: **crux still open** (correctly-stated `sorry`); two reusable foundation bricks
landed sorry-free + axiom-clean; one **soundness correction** to the crux statement landed. Below:
findings, what's banked, the full decomposition, and the honest scope read.

---

## FINDING 1 (soundness, load-bearing) — the crux statement was FALSE without `∀ s, r < H s`

`d1ge_L2_hAtV_explicit` (as originally stubbed) had hypotheses `hopt : prod H v = B`, `hB : B.rank = r`
only, and concluded
`∃ P, nRegL2 H r / 2 + rlctAtOn (dlnLoss (H−r) 0) P ≤ rlctAt H (dlnLoss H B) v`.

This is **false** whenever some `H s = r`. Concrete counterexample `H = (1,1,1)`, `r = 1`:
- `H − r = (0,0,0)`, so `dlnLoss (H−r) 0 ≡ 0` (empty product), hence
  `rlctAtOn (dlnLoss (H−r) 0) P = ⊤` (the integrand `|0|^{−c'} = 0` is integrable for every `c' > 0`).
- LHS `= nRegL2/2 + ⊤ = ⊤`.
- RHS `rlctAt H (dlnLoss H B) v = 1/2` (the loss `(ab−b0)²` vanishes transversally on a smooth curve;
  `nRegL2/2 = 1/2`).
- So the claim is `⊤ ≤ 1/2`, **false**.

The needed (and sufficient) hypothesis is `hpos : ∀ s, r < H s` — exactly the interior condition that
makes every reduced width positive so `dlnLoss (H−r) 0` is non-vacuous. This is NOT a weakening of the
headline: `aoyagi_learning_coefficient_L2` **already carries `hpos`**, and it flows down through
`d1ge_L2_deepestPoint_via_explicit_core_genL → …_core → d1ge_L2_hAtV_explicit` unused. The fix moves
`hpos` into the crux where it belongs.

**Done:** `hpos : ∀ s : Fin (2+1), r < H s` added to `d1ge_L2_hAtV_explicit`; the one call site in
`d1ge_L2_deepestPoint_via_explicit_core` updated to pass it. `HeadlineL2Assembly` rebuilds green
(EXIT 0); the only remaining sorry on the L2 path is the crux itself (line 218). (Verified by full
`scripts/lb DLNFibre.DLN.RLCT.Validate.HeadlineL2Assembly`.)

Codex xhigh independently flagged this same falseness (design consult, `codex/design-answer.md`).

## FINDING 2 (route) — the common pivot needs NO Cauchy–Binet

Codex feared the common invertible pivot (Q4) needed a rectangular Cauchy–Binet, which Mathlib v4.29
lacks (confirmed: `rg` for it is empty). It does **not**. A rank squeeze shares the row set `I`:
pick `I, J` with `(A0·A1).submatrix I J` invertible (rank `r`); then
`(A0·A1).submatrix I J = (A0.submatrix I id)·(A1.submatrix id J)`, so
`r = rank(prod) ≤ rank(A0.submatrix I id) ≤ r` forces `rank(A0.submatrix I id) = r`; the full-row-rank
`r × H1` block has an invertible `r`-column minor, and a row permutation (`det_permute`) transports its
determinant back to the SAME row set `I`. This is landed (brick B below).

## FINDING 3 (route) — invertible chart derivative WITHOUT the determinant

`rlctAtOn_eq_of_contDiff_chart` needs only `f' : E ≃L E` with `HasFDerivAt Φ (↑f') wstar`. Rather than
computing `det (DΦ) = ± det X · det(M11)³`, exhibit the explicit smooth two-sided inverse `Ψ` and read
invertibility off the two germ identities `Ψ∘Φ =ᶠ id`, `Φ∘Ψ =ᶠ id` (chain rule + derivative
uniqueness ⟹ `DΨ∘DΦ = id = DΦ∘DΨ`). This is landed (brick A below), avoiding the block-Jacobian
determinant entirely.

---

## BANKED THIS THREAD (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

### Brick A — `derivEquiv_of_eventual_inverse`
`lean/DLNFibre/DLN/RLCT/Foundations/S1InverseDerivEquiv.lean` (network-free analysis).

> **Claim.** A `ContDiff` self-map `Φ` with an explicit smooth local two-sided inverse `Ψ` has an
> invertible derivative at the base point.
> - **Lean:** `DLNFibre.DLN.RLCT.derivEquiv_of_eventual_inverse`
> - **Gloss.** `E` finite-dim real normed; `HasFDerivAt Φ A wstar`, `HasFDerivAt Ψ Bd (Φ wstar)`,
>   `Ψ∘Φ =ᶠ[𝓝 wstar] id`, `Φ∘Ψ =ᶠ[𝓝 (Φ wstar)] id` ⟹ `∃ f' : E ≃L[ℝ] E, HasFDerivAt Φ (↑f') wstar`.
> - **Proved.** Fully, unconditionally.
> - **Status.** sorry-free.

### Brick B — `exists_common_pivot_two_factor`
`lean/DLNFibre/Core/CommonPivotL2.lean` (network-free matrix algebra; Core engine).

> **Claim.** For a two-factor product of rank `r`, a single row set gives invertible minors of both the
> product and the first factor.
> - **Lean:** `DLNFibre.Core.exists_common_pivot_two_factor`
> - **Gloss.** `A0 : (Fin H0)×(Fin H1)`, `A1 : (Fin H1)×(Fin H2)` over a field, `(A0*A1).rank = r` ⟹
>   `∃ I K J` (injective, size `r`) with `((A0*A1).submatrix I J).det ≠ 0 ∧ (A0.submatrix I K).det ≠ 0`.
> - **Proved.** Fully, unconditionally (no Cauchy–Binet; rank-squeeze + `det_permute`).
> - **Also in file:** `exists_square_minor` (r=0-safe minor wrapper), `rank_eq_of_det_ne_zero`.
> - **Status.** sorry-free.

Neither file is imported by the aggregator yet (single-writer). **Controller: wire both into
`DLNFibre.lean`.** No FQN clashes (`exists_common_pivot_two_factor`, `derivEquiv_of_eventual_inverse`,
`exists_square_minor`, `rank_eq_of_det_ne_zero` are new names; `exists_square_minor` shadows nothing —
`D1HChartRank.exists_minor_of_le_rank` is a different name).

---

## THE REMAINING CRUX — decomposition (bottom-up; bricks A,B feed it)

Route: `rlctAt H (dlnLoss H B) v` →[`rlctAt_eq_rlctAtOn_lossFlatShift`] `rlctAtOn (lossFlatShift) 0`
→[explicit chart `Φ_expl` via `rlctAtOn_eq_of_contDiff_chart` + `splitHomeo` reindex] the
`∑p² + ∑qₑ²` shape → feed the BANKED consumer `d1ge_L2_hAtV_of_explicit_chart` (Option A: `e = refl`,
`u ≡ 1`, `hfact` from the Schur bricks).

Remaining pieces (all under the corrected statement; ▣ = banked/landed, ☐ = open labour):

1. ▣ common pivot at `v` — brick B (`exists_common_pivot_two_factor`), applied to `v 0`, `v 1` via the
   `prod_two_layer334`-style identity `prod H v = v0 * v1` (small bridge, ☐).
2. ☐ `blockFlatEquiv` — the flat `(Fin (flatDim H) → ℝ) ≃L` block-structured
   `Params`/matrix product, localizing all `Fin r ⊕ Fin (Hs−r)` casts in ONE block-split API
   (Codex Q3: conjugate by `LinearEquiv.toContinuousLinearEquiv` / `ContinuousLinearEquiv.prodCongr`).
   **The cost driver** (dependent-`Fin` `HMul` friction; see `lean/CLAUDE.md` gotchas).
3. ☐ `Φ_expl` forward map (block coords → `(p, A0red, A1red, X, Y, U)`): `ContDiffOn ℝ 2` on
   `{det X ≠ 0, det M11 ≠ 0}` (rational: `ContDiffOn.inv` on the pivot minors; C² of polynomial
   entries reuses `contDiff_prod_gmapAt_entry`), then bump-globalise via
   `exists_contDiff_eventuallyEq_of_contDiffOn`.
4. ▣ invertible derivative — brick A (`derivEquiv_of_eventual_inverse`), fed the two Schur two-sided
   inverse germ identities (matrix algebra, ☐: `Ψ_expl∘Φ_expl =ᶠ id` etc., from the rational inverse).
5. ☐ the germ `lossFlatShift =ᶠ (∑p² + ∑qₑ²) ∘ Φ_expl` — **highest line-count risk** (Codex Q5). Uses
   `schur_product_factor` + `schur_complement_zero_of_rank_le` (banked) to pin
   `M22 − B22 = A0red·A1red + R(p)`, `R(0) = 0`.
6. ☐ `qₑ` definition (reshaped `M22 − B22` in w-coords) + `hq : ContDiff ℝ 1 qₑ`.
7. ▣ `hfact` — Option A (`e = refl`, `u ≡ 1`): `∑ qₑ(0,·)² = ‖A0red·A1red‖² = dlnLoss (H−r) 0 (…)`,
   from the Schur bricks (medium, ☐ to write, but no analysis).
8. ▣ `hRne` — banked `dlnLoss_deepest_core_ae_ne_zero` / `ae_eval_ne_zero` under `hpos` (medium ☐).
9. ▣ measure wiring — Option A: `MeasurePreserving.id`, `MeasurableEmbedding.id`, `measurable_const`
   (trivial, per `D1L2SchurAssembly` docstring).
10. ☐ final wiring into `d1ge_L2_hAtV_of_explicit_chart`.

**Honest scope read.** This is a genuine ~600–1500-line multi-file build (the deepest-point POLYNOMIAL
analogue `dln_hchart_residual` is ~1965 lines across 8 files; the general-`v` RATIONAL Schur chart is
strictly harder). The mathematical core is de-risked (Schur bricks banked; splitwit numeric; bricks
A,B landed). The open labour is concentrated in pieces 2/3/5 — the general-width block reindexing +
the exact flat/block germ — which need the full DLN closure and many build iterations. Recommend the
controller scope this as a dedicated build (this thread can continue via SendMessage, or a follow-up
tide) rather than a single-sorry fill.

Codex design consult: `codex/design-prompt.md` + `codex/design-answer.md`.
