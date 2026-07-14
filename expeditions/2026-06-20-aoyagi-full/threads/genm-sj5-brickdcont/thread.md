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
> - **Status.** sorry-free (awaiting reviewer fidelity check).

## Build notes / lessons (v4.29)

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
