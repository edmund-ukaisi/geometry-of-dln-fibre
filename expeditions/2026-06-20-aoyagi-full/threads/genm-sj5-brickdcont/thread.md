# Brick D continuation — the terminal `deeperFlag_shell_le` measure-theory tail

**Seat:** lean-formaliser (tide). Branch `genm-sj5-brickdcont` off `origin/genm-sj5-brickdbuild@2c3778837`.
Source of truth: `genm-incidencepp/incidence-cert.md` (§0/§3/§3b) + `genm-brickdbuild/build-design.md`.
Consumes brickdbuild's 8 banked block-algebra lemmas in `RouteMSJIncidenceChart.lean`.

Pieces (controller ordering): (i) transverse-Schur Gram identity → (ii) chart (4)/(5) CoV →
(iii) null-overlap gluing → (iv) exponent-gate (general Nat) → (v) assembly.

## LANDED — piece (i): transverse-Schur Gram identity (sorry-free, axiom-clean)

Added to `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceChart.lean` (@ `d1bbef73`, +129 LoC),
building on the 8 banked lemmas. All four `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

- **`chartProj_Dcancel`** — `Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b = [I;Xᵀ](I+XXᵀ)⁻¹[I|X]` for `Q_b = D·[I|X]`
  (the orthogonal projection onto `row(Q_b)` is `D`-independent; `chartGram_congr` + `mul_inv_rev` + the
  `nonsing_inv`-cancel-left lemmas cancel `D`). Hypothesis `IsUnit D.det`.
- **`chartProjRed_block`** — `[I;Xᵀ](I+XXᵀ)⁻¹[I|X] + N(I+XᵀX)⁻¹Nᵀ = I` for `N = [−X;I_d]`
  (the 4-block match: top-left/bottom-right via `pushThrough`, off-diagonals via `chartSwap`).
  Hypotheses `IsUnit (I+XXᵀ)`, `IsUnit (I+XᵀX)`.
- **`chartProjComplement`** — `I − Π_b = N(NᵀN)⁻¹Nᵀ` (`Π_b = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`); the orthogonal
  projection onto `ker(Q_b) = col(N)`. Combines the two above.
- **`transverseSchurGram`** — `Q_p(I−Π_b)Q_pᵀ = W(I+XᵀX)⁻¹Wᵀ` for `Q_p = [U | U X + W]`.
  The transverse energy of `Q_p` on the complement of `row(Q_b)` is monomialised entirely by `W`.

### Statement card — transverse-Schur Gram identity (cert §3, piece i)

> **Claim.** For the minor chart `Q_b = D·[I_b | X]` (`D ∈ GL_b`, `X : b×d`) and pivot rows
> `Q_p = [U | U X + W]` (`U : u×b`, `W : u×d`), with `Π_b` the orthogonal projection onto `row(Q_b)`,
> the transverse Schur complement energy is `Q_p (I − Π_b) Q_pᵀ = W (I_d + Xᵀ X)⁻¹ Wᵀ`.
> Needs `D` invertible and `I+XXᵀ`, `I+XᵀX` invertible (all hold on the full-rank chart).
>
> - **Lean:** `DLNFibre.DLN.RLCT.transverseSchurGram`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceChart.lean` @ `d1bbef73`)
> - **Gloss.** With `Q_b = D·fromCols 1 X`, `Q_p = fromCols U (U*X+W)`, and
>   `Π_b = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`, the matrix `Q_p·(I − Π_b)·Q_pᵀ` equals `W·(1 + Xᵀ*X)⁻¹·Wᵀ`.
>   Index type of the ambient space is `Fin b ⊕ Fin d` (= `Fin n`, `n = b+d`).
> - **Proved.** The exact matrix identity, unconditionally given the three `IsUnit` hypotheses.
>   Via `chartProjComplement` (`I − Π_b = N(NᵀN)⁻¹Nᵀ`, `N = fromRows (-X) 1`), `chartNull_Qp`
>   (`Q_p N = W`), `chartNull_gram` (`NᵀN = I + XᵀX`).
> - **Assumed.** `IsUnit D.det`, `IsUnit (I+XXᵀ)`, `IsUnit (I+XᵀX)` — the hypotheses the informal
>   claim also needs (full row rank of `Q_b`; `I+XXᵀ ≻ 0`, `I+XᵀX ≻ 0` always). Not vacuous.
> - **Cited.** none (network-free matrix algebra).
> - **Deferred.** The `≍ ‖W‖²_F` bound (`I+XᵀX` a bounded unit on the chart) is a downstream estimate,
>   not part of this exact identity. The rest of Brick D (charts 4/5 CoV, gluing, exponent-gate, assembly).
> - **Route.** incidencepp cert §3/§3b (block-route projection identity, no rank/idempotent argument) →
>   the two off-diagonal + two diagonal block matches from the banked `pushThrough`/`chartSwap`.
> - **Status.** sorry-free + reviewed (fidelity OK, reviewer verdict below).

**Reviewer verdict on (i): SURVIVED / fidelity OK** (`RouteMSJIncidenceChart` @ `1c6298148`). No break, no
escalation. `Π_b = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b` faithfully the orthogonal projection onto `row(Q_b)` (full row rank on
the chart); `transverseSchurGram` matches cert §3, in fact slightly STRONGER (proves the matrix identity; the
cert's trace form follows by `I−Π_b` symmetric-idempotent). Hypotheses right + non-vacuous. Axiom-clean
confirmed by an independent forced `#print axioms`. One precision nicety applied: the docstring phrase
"monomialised by W" (which leans toward the deferred `≍‖W‖²` estimate) tightened to "factors through `W` alone
… as the `X`-weighted Gram" (the exact object).

## LANDED — piece (iv): exponent-gate arithmetic certificate (sorry-free, axiom-clean)

NEW standalone file `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceExponent.lean` (imports `RouteMLayerSplit`
for banked `minAdm`/`minAdmRec`; NO matrix algebra, NO integrals). Green under
`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceExponent`; forced `#print axioms` clean.

- **`clsCodim`** — the joint incidence-stratum codim `C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ)`
  (`b=M₁−u`, `d=M₂−b`), over `ℕ`.
- **`clsCodim_add_ab_eq`** — the `ℓ`-independence ring identity (additive form) `C_{ℓ,s} + a·b =
  (M₀−s)(M₁−s) + s·M₂`, via `zify [range hyps] ; ring` over ℤ (axioms `[propext, Quot.sound]` only).
- **`minAdm_arity3`** — `minAdm ![M₀,M₁,M₂] = min_{t≤min(M₀,M₁)} [(M₀−t)(M₁−t) + t·M₂]`, from banked
  `LayerSplit_value_eq_minAdm` + the `Fin 2` leaf.
- **`clsCodim_gate`** (headline) — the PER-STRATUM gate `minAdm M ≤ C_{ℓ,s} + a·b`, i.e. `T1_q ≤ C_{ℓ,s}/2`.
- **`minAdm_le_ab_add_uM2`** — `T1_q ≤ u·M₂/2` (the `ℓ=0,s=u` corner; needs `b ≤ M₂`).

### Statement card — exponent gate (cert §3/§5, piece iv)

> **Claim.** For the arity-3 chain `M=(M₀,M₁,M₂)`, a cut `u ≤ min(M₀,M₁)`, and a valid rank-stratum
> `(ℓ,s)` (`s ≤ u`, `ℓ+s ≤ u`, `(M₁−u)+ℓ ≤ M₂`), the joint codim `C_{ℓ,s}` satisfies `minAdm M ≤ C_{ℓ,s} + ab`
> (`ab=(M₀−u)(M₁−u)`), i.e. `T1_q = (minAdm M − ab)/2 ≤ C_{ℓ,s}/2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.clsCodim_gate` (`…/RouteMSJIncidenceExponent.lean`).
> - **Gloss.** Every enumerated rank-`ℓ`(W)/rank-`s`(Y) stratum has codimension `C_{ℓ,s} ≥ 2·T1_q`, so
>   `q < T1_q ⟹ q < C_{ℓ,s}/2` (its radial integral `∫r^{C_{ℓ,s}−1−2q}dr` converges).
> - **Proved.** The per-stratum inequality, for ANY given valid `(ℓ,s)`. Via the `ℓ`-independence ring
>   identity + `Finset.inf'_le` on the banked layer-peel `minAdm`. NOT a `decide` over any finite range.
> - **Assumed.** the stratum range constraints + `u ≤ min(M₀,M₁)` (cut in scope). Chart validity `d=M₂−b≥0`.
> - **Cited.** none.
> - **Deferred / GATED.** The AGGREGATE headline `min_{(ℓ,s) over the enumerated range} C_{ℓ,s} = 2·T1`
>   — i.e. that this `(ℓ,s)` enumeration is the COMPLETE stratum set — is NOT proved. It is **`genm-bltj`-gated**:
>   bltj is probing whether a `b<j` `Q_p`-degeneration stratum (exponent possibly `< T1`) is missed. The
>   `inc_sweep.py` (332/332) + `11598`-strata numerics are EVIDENCE of completeness, not a proof.
> - **Status.** sorry-free (per-stratum gate); aggregate completeness gated on bltj.

## LANDED — piece (ii) chart (4): H̃-fibre polar scaling (sorry-free, axiom-clean)

NEW file `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJIncidenceChart4Polar.lean` (file-disjoint from chart-5).
Green under its module target; forced `#print axioms` `[propext, Classical.choice, Quot.sound]`.
- **`chart4_polar_scaling`** — `∫_{H̃∈ℝ^N}(‖H̃‖²+τ²)^{−q} dH̃ = τ^{N−2q} · ∫(‖V‖²+1)^{−q} dV` (`τ>0`).
  The load-bearing `τ^{N−2q}` scale extraction. Via Haar scaling `Measure.map_addHaar_smul` at `r=τ⁻¹`
  (`H̃=τ·V`); integrand reformulation `(‖H‖²+τ²)^{−q}=τ^{−2q}(‖τ⁻¹•H‖²+1)^{−q}`. No polar/sphere.
- **`chart4_unit_lintegral_lt_top`** (sufficiency) — `K = ∫(‖V‖²+1)^{−q}dV < ⊤` when `2q>N`. DIRECT reuse of
  Mathlib `integrable_rpow_neg_one_add_norm_sq` (`finrank<r ⟹ (1+‖x‖²)^{−r/2}` integrable, at `r=2q`) — no
  polar/radial split needed. `N/2` is the exact fibre threshold; necessity NOT formalised (named `_lt_top`,
  not `iff`, per precision).
- **`chart4_Htilde_fibre_lt_top`** (assembly-ready) — for `τ>0`, `2q>N`: `∫(‖H̃‖²+τ²)^{−q}dH̃ < ⊤`
  (`= τ^{N−2q}·K`, product of finites). The ready "H̃-fibre finite" fact the assembly consumes.
- **CHART (4) DONE** — hole-free (scale + finiteness + combined). Import `Mathlib.Analysis.SpecialFunctions.JapaneseBracket`
  for `integrable_rpow_neg_one_add_norm_sq`; `hasFiniteIntegral_iff_enorm` + `lintegral_enorm_of_nonneg` bridge
  `HasFiniteIntegral` → `∫⁻ ofReal < ⊤`.

## Build notes / lessons (v4.29)

- **`Measure.map_addHaar_smul μ (hr:r≠0)` returns `ENNReal.ofReal (|(r^(finrank ℝ E))⁻¹|) • μ`** — the abs is
  OUTSIDE the inverse (`|(r^n)⁻¹|`, not `|r^n|⁻¹`). Do NOT ascribe the `have hmap :=` type (write
  `finrank` and you get "unknown identifier `finrank`" — it's `Module.finrank`); let it infer.
- **`lintegral_map hf hg` (the CoV) unifies `f` from `hf`'s statement** — passing
  `ENNReal.measurable_ofReal.comp hg` gives `f = ENNReal.ofReal ∘ g` (composition), and the `rw` pattern
  `(ofReal∘g)(T a)` then does NOT match an applied `ofReal (g (T a))` in the goal. Use `hg.ennreal_ofReal`
  (`Measurable.ennreal_ofReal`, the lambda form `fun a => ofReal (g a)`) so the applied pattern matches.
- **`finrank_euclideanSpace_fin`** collapses `finrank ℝ (EuclideanSpace ℝ (Fin N)) = N` (root name, no
  `Module.` prefix needed in a `rw`).

- **`Matrix.neg_neg` does NOT `rw`/`simp` a matrix double-negation `- -A`** (both as a `simp` arg — reported
  "unused" — and as `rw [neg_neg]` — "did not find pattern `- -?a`"), even in a clean standalone `example`.
  Use **`abel`** to collapse `- -A = A` for (rectangular) matrices; it works on the additive-group structure
  directly. (Bit the eT2 top-left block `(-X)Q(-Xᵀ) = XQXᵀ`.)
- **`Matrix.nonsing_inv_mul_cancel_left` / `mul_nonsing_inv_cancel_left` take `A` EXPLICITLY**
  (`variable (A : Matrix n n α)` in `NonsingularInverse.lean`): signature is `(A) (B) (h)`, not `(B) (h)`.
  Pass all three (`... D B hD`), else `A` stays a metavar and the `rw` pattern doesn't match.
- **`Matrix.fromCols 1 X` needs the `1` ascribed** `(1 : Matrix (Fin b) (Fin b) ℝ)` — else "typeclass
  instance problem is stuck" (the `One` instance can't fix the square dimension from `fromCols` alone).
- Block-matrix product lemmas used: `Matrix.fromRows_mul`, `Matrix.fromRows_mul_fromCols`,
  `Matrix.fromBlocks_add`, `Matrix.fromBlocks_one`; `Matrix.mul_inv_rev` is unconditional.

## Handoff

Piece (i) is a green boundary. Remaining pieces (ii)-(v) are the measure-theory tail (charts 4/5 CoV via
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`, null-overlap gluing, the exponent-gate, assembly).
Module `RouteMSJIncidenceChart.lean` is NOT yet wired into the aggregator `DLNFibre.lean` (single-writer);
controller to add the import.

**Exponent-gate (iv) de-risk banked** (from incidencepp via brickdbuild + controller): substituting
`b=M₁−u, d=M₂−M₁+u` into `C_{ℓ,s}=ub+M₀ℓ+(M₀−s)(u−ℓ−s)+s(M₂−b−ℓ)`, the ℓ-terms cancel exactly, leaving
`C_{ℓ,s} = (M₀−s)(M₁−s) + s·M₂ − ab` (ℓ-independent — a `ring` identity). Then (iv) = the ring identity +
`Finset.min` monotone-under-range-inclusion (min over feasible `s ≤ u` ≥ min over full range) + banked
`minAdm` codim. The ring identity IS the proof; the widths-2..10 sweep is evidence only — NOT `decide`-over-332.
