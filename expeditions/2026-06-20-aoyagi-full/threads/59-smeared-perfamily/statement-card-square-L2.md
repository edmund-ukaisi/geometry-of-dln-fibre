# Statement card — the FULLY-UNCONDITIONAL smeared L=2 box-divergence on the square stratum

ALL THREE per-family analytic hypotheses of `routeMCore_smearedL2` (`hcancel`, `hUpos`, `hSpre`) and the
peeled-point membership (`hmem`) discharged on a conditioned box, via strict row diagonal dominance of the
front rank block `P₁` (`det(P₁ᵀP₁) ≠ 0` everywhere on the box) + the Varah `Λ₀` bound, on the smeared L=2
stratum `r = M0` (the entire genuine smeared L=2 regime, `M0 < M1`). The headline
`routeMCore_smearedL2_square_uncond` carries NO analytic per-family hypothesis — only standard
measure-positivity / exponent / box-width inputs. The adjudication certificate is
`expeditions/2026-06-20-aoyagi-full/threads/59-smeared-perfamily/pnp-adjudicate/certificate-smeared-l2-two-facts.md`
(branch `origin/pnp/smeared-l2-adjudicate`).

---

## Brick (a) — Fact 1 (off-pole cancellation `P₁·Λ₀ = P₂`)

> **Claim.** On the square stratum `r = M 0`, if the Gram `det(P₁ᵀP₁) ≠ 0` then the chart's rational
> routing satisfies `P₁·Λ₀ = P₂`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.Lam0u_cancel_of_gram_square`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean` @ `846f0d06`)
> - **Gloss.** `r = M 0` makes `P1u` square; `det(P₁ᵀP₁) = (det P₁)² ≠ 0` ⟹ `P₁` invertible, so
>   `K := P₁⁻¹·P₂` factors `P₂ = P₁·K`, and the banked `Lam0u_cancel_of_factoring`
>   (= `proj_cancel_of_factorsThrough`) fires.
> - **Proved.** The cancellation, sorry-free, from a single Gram-det-nonzero hypothesis. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** `r = M 0` (the square slice) and `det(P₁ᵀP₁) ≠ 0` (the off-pole condition). Both are
>   discharged on the conditioned box below (`gram_det_ne_of_box`), so the cancellation is unconditional
>   on the box.
> - **Cited.** none.
> - **Deferred.** none for Fact 1.
> - **Scope (load-bearing).** Fact 1 is FALSE for a free tall front `A0u` at `r < M 0` (the cancellation
>   needs `col(P₂) ⊆ col(P₁)`, which a free tall `P₁` does not give — certificate witness `M0=3,M1=3,r=2`).
>   The square slice `r = M 0` is the ENTIRE genuine smeared L=2 stratum, so the restriction to `r = M 0`
>   is not a loss of generality within it. **Precise mechanism (corrected — reviewer NOTE 1):** the
>   stratum-forcing is the `¬InteriorDrop` clause of `BoundarySmeared` (`deepRank < deepRows = M1` together
>   with no interior drop forces `M0 ≤ r`, hence `r = M0`, square `P₁`), NOT a bare `deepRank = min(M0,M1)`
>   identity — that identity is FALSE in general at L=2 (e.g. `M=(3,4,5)` minimizes the deep-rank objective
>   at `t = 1`, giving `deepRank = 1 < min(3,4)`, an interior-drop case, hence not smeared). The certificate's
>   conclusion (`r = M0` on the stratum) is correct; only its stated reasoning was loose. The Lean takes
>   `hr0 : r = M 0` as a caller obligation and never relies on the `min` identity, so fidelity is unaffected.
> - **Status.** sorry-free + reviewed (reviewer fidelity PASS-WITH-NOTES, 2026-06-29).

## det(P₁ᵀP₁) ≠ 0 from strict row diagonal dominance, unconditional on the box

> **Claim.** On the conditioned box `condBoxWidth` (rank-block diagonal front coords in `[δ/2,δ]`, every
> other coord in `[−η,η]`), with the margin condition `(r−1)·η + γ ≤ δ/2` and `γ > 0`, `det(P₁ᵀP₁) ≠ 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.gram_det_ne_of_box` (built on `gram_det_ne_of_diagDominant` and the
>   Core brick `DLNFibre.Core.Matrix.StrictRowDominant.det_ne_zero`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean`,
>   `lean/DLNFibre/Core/Matrix/DiagDominance.lean` @ `846f0d06`)
> - **Gloss.** The diagonal entry `|P₁ i i| ≥ δ/2`; the off-diagonal row sum has `r−1` terms each `≤ η`,
>   so `≤ (r−1)·η`; margin `γ`. Strict row diagonal dominance ⟹ `det P₁ ≠ 0` (Levy–Desplanques, wraps
>   Mathlib `det_ne_zero_of_sum_row_lt_diag`), hence `det(P₁ᵀP₁) = (det P₁)² ≠ 0`. This is UNCONDITIONAL
>   on the box (everywhere, not a.e.).
> - **Proved.** The Gram det nonzero on the box, sorry-free, axiom-clean.
> - **Assumed.** the box-membership of `u` (the non-pivot rest coords); `r = M 0`; the margin condition.
> - **Cited.** Mathlib `det_ne_zero_of_sum_row_lt_diag` (Gershgorin / Levy–Desplanques).
> - **Scope catch (Codex-confirmed, honored).** The box is parameterized by a FREE width `η` and a margin
>   condition, NOT a hard-coded `δ/8`. A fixed `δ/8` is diagonally dominant only for `r ≤ 4` (the certificate
>   / Codex give a singular witness inside the `δ/8` box at `r ≥ 5`). The per-`r` choice `η = δ/(4(r−1))`,
>   `γ = δ/4` satisfies the margin for all `r ≥ 1` (and the `(r−1)·η` form is robust to `r = 1`: empty sum).
> - **Status.** sorry-free + reviewed (reviewer fidelity PASS-WITH-NOTES, 2026-06-29).

## Brick — `hUpos` (the `z`-free unit `U = ‖P₁·H̄_unit‖² > 0`)

> **Claim.** On the square stratum, if `det(P₁ᵀP₁) ≠ 0` then `Uunit > 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.Uunit_pos_of_det_ne` (and the box form `Uunit_pos_of_box`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean` @ `846f0d06`)
> - **Gloss.** `H̄_unit` has pivot entry `(⟨0⟩,⟨0⟩) = 1`, so `H̄_unit ≠ 0`; `P₁` invertible (square) and
>   left-multiplication injective ⟹ `P₁·H̄_unit ≠ 0`, so some entry is nonzero and the sum of squares is
>   positive (`frobeniusSq_pos_of_entry_ne`).
> - **Proved.** `U > 0`, sorry-free, axiom-clean. (Note: `Uunit` is `z`-free, so the `z = 0` peeled point
>   used by `routeMCore_smearedL2`'s `hUpos` is handled — the box-membership is taken on the rest coords,
>   not the pivot.)
> - **Assumed.** `r = M 0`; `det(P₁ᵀP₁) ≠ 0` (discharged on the box).
> - **Cited / Deferred.** none.
> - **Status.** sorry-free + reviewed (reviewer fidelity PASS-WITH-NOTES, 2026-06-29).

## Brick (b) — the Varah `Λ₀`-entry bound (the analytic core of field A)

> **Claim.** On the conditioned box (square stratum), `|Λ₀ a b| ≤ (1/γ)·η` (δ-free with `γ = δ/4`,
> `η = δ/(4(r−1))`: `≤ 1/(r−1)`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.Lam0u_entry_bound_of_box` (built on the Core Varah brick
>   `DLNFibre.Core.Matrix.StrictRowDominant.inv_mul_entry_bound`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean`,
>   `lean/DLNFibre/Core/Matrix/DiagDominance.lean` @ `846f0d06`)
> - **Gloss.** On the square slice `Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂` collapses to `P₁⁻¹P₂`; the residual front cols
>   are non-diagonal so `|P₂ i b| ≤ η`; the Core Varah inverse-entry bound (the elementary argmax-row
>   inequality `γ·|x i| ≤ ‖B·x‖_∞`) gives `|Λ₀ a b| ≤ (1/γ)·η`.
> - **Proved.** The entry bound, sorry-free, axiom-clean. The Core Varah bound
>   (`exists_argmax_bound`/`solution_bound`/`inv_mul_entry_bound`) is a self-contained, network-free engine
>   brick (no Mathlib operator-norm machinery).
> - **Assumed.** box membership; `r = M 0`; the margin condition.
> - **Cited / Deferred.** none for the bound itself.
> - **Status.** sorry-free + reviewed (reviewer fidelity PASS-WITH-NOTES, 2026-06-29).

---

## Brick — field A (the per-entry decode bound `≤ 2δ`, the `hSpre` discharge)

> **Claim.** On the conditioned box, `condBox ⊆ (ψ∘R)⁻¹(cubeBox 2δ)`: every decoded flat coord is `≤ 2δ`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.condBox_subset_preimage` (with `chartL2Params_entry_bound`,
>   `A0u_entry_le_of_box`, `Sbotu_entry_le_of_box`, `HbarUnit_entry_le_of_box`, `zu_abs_le_of_box`,
>   `deepTop_entry_le_of_box`, `phiL2_entry`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean` @ `a0b99639`)
> - **Gloss.** `psiMap (Rmap u) = phiL2 …`; each flat coord = a `chartL2Params` entry (`phiL2_entry`, rfl).
>   Front `A0u ≤ δ`; deep-bottom `S_bot ≤ η`; deep-top `|z·H̄ − Λ₀·S_bot| ≤ |z|·|H̄| + ∑_b|Λ₀||S_bot|
>   ≤ δ·1 + s·((1/γ)η)·η` (the Varah `Λ₀` bound bites the shear term). Under the field-A margins
>   `η ≤ δ`, `η ≤ 1`, `s·((1/γ)η)·η ≤ δ`, every entry `≤ 2δ`.
> - **Proved.** Field A on the box, sorry-free, axiom-clean. The opaque-width analogue of the `(2,3,1)`
>   `chartParams231_entry_bound` / `subBox231_subset_preimage`.
> - **Assumed.** box membership; `r = M 0`; the dominance + field-A margins.
> - **Cited / Deferred.** none.
> - **Status.** sorry-free + reviewed (initial pair; field-A landed after review — re-review welcome).

## Brick — the generic peeled-point membership (the `hmem` discharge)

> **Claim.** `box k := condBoxWidth (hN ▸ k)` ⟹ every peeled point `hN ▸ (insertNth p z y)` lies in the
> ambient `condBox (pivotCoord) (condBoxWidth) δ`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.insertNth_mem_condBox` (with `exists_succAbove_index`,
>   `succAbove_readoff_value`, `condBoxWidth_double_cast`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean` @ `a0b99639`)
> - **Gloss.** The cast bridge that walled the first pass, landed by SPLITTING the
>   `Fin (n+1)`↔`Fin (routeMAmbient M)` index decomposition (`exists_succAbove_index`, pure `Fin`) from the
>   value readoff (`succAbove_readoff_value`, via the banked `hN_cast_apply`) — keeping `condBoxWidth`
>   entirely outside the generalize/`subst`, which was the prior thrash. The opaque-width analogue of
>   `(2,3,1)`'s `insertNth6_mem_subBox231`.
> - **Proved.** The generic membership, sorry-free, axiom-clean.
> - **Status.** sorry-free.

## The FULLY-UNCONDITIONAL headline (all three analytic hypotheses discharged)

> **Claim.** For the smeared L=2 stratum `r = M 0`, the achiever box integral
> `∫⁻_{cubeBox N 2δ} |routeMCore M|^{−c'} = ⊤` — with ALL THREE per-family analytic hypotheses of
> `routeMCore_smearedL2` (`hcancel`, `hUpos`, `hSpre`) and the peeled-point membership `hmem` DISCHARGED.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_smearedL2_square_uncond`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean` @ `a0b99639`)
>   (intermediate forms: `routeMCore_smearedL2_square` takes `hSpre`+`hmem`;
>   `routeMCore_smearedL2_square_condBox` takes `hSpre` only.)
> - **Gloss.** `hcancel` ⟵ `Lam0u_cancel_of_box`, `hUpos` ⟵ `Uunit_pos_of_box`, `hmem` ⟵
>   `insertNth_mem_condBox`, `hSpre` ⟵ `condBox_subset_preimage` (at `ε = 2δ`), all on the conditioned
>   `condBoxWidth`. The chart facts (MP/embedding/radial det/peeled rate) are the banked
>   `routeMCore_smearedL2` interface.
> - **Proved.** The box-divergence with NO analytic per-family hypothesis remaining, sorry-free, axiom-clean
>   `[propext, Classical.choice, Quot.sound]` (forced recompile + `#print axioms`).
> - **Assumed (NON-analytic standard inputs only).** the conditioned box's positive measure `hboxpos`; the
>   binding-axis exponent arithmetic `hexp : (r·M2 − 1) − 2c' ≤ −1` (from `c' ≥ ½·minAdm`); and the box
>   margins (dominance `(r−1)η + γ ≤ δ/2`; field A `η ≤ δ`, `η ≤ 1`, `s·((1/γ)η)·η ≤ δ`). The chart-fact
>   interface (banked, proved in `RouteMSmearedDecodeL2`).
> - **Non-vacuity (margins jointly satisfiable ∀ r ≥ 1, s).** Pick `γ = δ/4` and
>   `η = min(δ/(4(r−1)), δ/(2√s))` (`η = δ/4` at `r = 1`): dominance `(r−1)η + γ ≤ δ/4 + δ/4 = δ/2` ✓;
>   `η ≤ δ`, `η ≤ 1` for `δ ≤ 1` ✓; field A `s·((1/γ)η)·η = 4s·η²/δ ≤ 4s·(δ²/(4s))/δ = δ` ✓. So the box
>   exists for every stratum config.
> - **Cited / Deferred.** none.
> - **Honest scope.** This IS the fully-unconditional smeared L=2 box-divergence on the square stratum
>   `r = M 0` (the entire genuine smeared L=2 regime) — no analytic per-family hypothesis assumed. The only
>   inputs are the standard measure-positivity / exponent / box-width choices.
> - **Status.** sorry-free (awaiting reviewer fidelity check on the field-A + uncond pieces).

---

## Structure & ideas observed (from the formalisation)

- **The two named analytic facts collapse to ONE condition: `det(P₁ᵀP₁) ≠ 0`** — both `hcancel` (via the
  square inverse) and `hUpos` (via left-mult injectivity) ride on it. So the whole analytic content of the
  pair is "the conditioned box keeps `P₁` invertible", which strict diagonal dominance delivers
  unconditionally (Levy–Desplanques, already in Mathlib).
- **The Varah bound is elementary** — the argmax-row inequality `γ·|x i| ≤ ‖B·x‖_∞` needs no operator-norm
  theory; it is a one-index `nlinarith` after isolating the diagonal term. The Core brick is reusable
  network-free engine API.
- **The box should be classified at the slot (FlatIdx) level, not the ambient-coord level** (Codex): this
  avoids repeated `coordOf`-injectivity work; the readoff `condBoxWidth (coordOf q) = slotBox q` is the
  single bridge.
- **The `r = 1` divide-by-zero is avoided by parameterizing** the box by a free `η` + a margin condition
  `(r−1)·η + γ ≤ δ/2`, rather than hard-coding `η = δ/(4(r−1))`. This also makes the `r ≥ 5` singular-box
  scope catch a non-issue (the caller picks `η` per `r`).
