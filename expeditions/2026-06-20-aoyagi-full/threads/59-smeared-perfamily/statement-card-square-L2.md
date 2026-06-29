# Statement card — the smeared L=2 two analytic hypotheses, discharged on the square stratum

The two genuinely-analytic NAMED hypotheses of `routeMCore_smearedL2` (`hcancel`, `hUpos`) discharged
UNCONDITIONALLY on a conditioned box, via strict row diagonal dominance of the front rank block `P₁`,
on the smeared L=2 stratum `r = M0` (the entire genuine smeared L=2 regime, `M0 < M1`). The
adjudication certificate is
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
>   The square slice `r = M 0` is the ENTIRE genuine smeared L=2 stratum (`deepRank = min(M0,M1) = M0 < M1`
>   forces `r = M0`, square `P₁`); there is no smeared L=2 config with `s > 0` and a tall `P₁`. So the
>   restriction to `r = M 0` is not a loss of generality within the stratum.
> - **Status.** sorry-free (awaiting reviewer fidelity check).

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
> - **Status.** sorry-free (awaiting reviewer fidelity check).

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
> - **Status.** sorry-free (awaiting reviewer fidelity check).

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
> - **Status.** sorry-free (awaiting reviewer fidelity check).

---

## The wired headline (the two named analytic hypotheses discharged)

> **Claim.** For the smeared L=2 stratum `r = M 0`, the achiever box integral
> `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` follows from the chart facts + field-A containment `hSpre`
> + the (cheap) peeled-point box-membership `hmem` — with the two genuinely-analytic NAMED hypotheses of
> `routeMCore_smearedL2` (`hcancel`, `hUpos`) DISCHARGED, not assumed.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_smearedL2_square`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean` @ `846f0d06`)
> - **Gloss.** Wires the banked `routeMCore_smearedL2` with the conditioned box `condBoxWidth`: `hcancel`
>   discharged by `Lam0u_cancel_of_box`, `hUpos` by `Uunit_pos_of_box` (the `z = 0` point via the
>   rest-membership transfer `hN_insertNth_agree_off_pivot`), both from `gram_det_ne_of_box`.
> - **Proved.** The reduction with `hcancel` + `hUpos` discharged unconditionally on the box, sorry-free,
>   axiom-clean `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** the chart facts (banked generic chart: MP/embedding/radial det/peeled rate — these are the
>   `routeMCore_smearedL2` interface, already proved in `RouteMSmearedDecodeL2`), the field-A containment
>   `hSpre`, and the peeled-point box-membership `hmem`. `hmem` is a readoff-level membership bridge
>   (the `subst`-clean analogue of `(2,3,1)`'s `insertNth6_mem_subBox231`).
> - **Cited.** none new.
> - **Deferred (the honest residual to a FULLY unconditional headline).**
>   1. **Field-A containment `hSpre`** — the per-slot decode case analysis bounding every decoded flat
>      coord by `2δ`. The genuinely-analytic core (the `Λ₀` bound) is DONE (`Lam0u_entry_bound_of_box`);
>      what remains is the mechanical per-entry assembly (front coords `≤ δ`; deep-bottom `S_bot ≤ η`;
>      deep-top `|z·H̄ − Λ₀·S_bot| ≤ |z|·|H̄| + ‖Λ₀‖·(M2·η)`), the opaque-width analogue of
>      `chartParams231_entry_bound` / `subBox231_subset_preimage`.
>   2. **The generic peeled-point membership `hmem`** — a `Fin (n+1)`↔`Fin (routeMAmbient M)` cast bridge
>      (the analogue of `insertNth6_mem_subBox231`), left as a hypothesis here (cast bookkeeping; cheap at
>      a concrete `M`).
> - **Honest scope (decorrelated Codex Q3).** This is the smeared L=2 box-divergence on the square stratum
>   GIVEN field-A containment — NOT yet "fully unconditional". The two genuinely-analytic facts the
>   certificate adjudicated (`hcancel`, `hUpos`) ARE unconditional on the box; the remaining `hSpre` is a
>   containment whose analytic input (the `Λ₀` bound) is landed.
> - **Status.** sorry-free (awaiting reviewer fidelity check).

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
