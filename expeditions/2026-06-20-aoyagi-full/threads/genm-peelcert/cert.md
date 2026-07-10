# The CoV-Jacobian peel certificate — the outer-descent fresh-block radial Schur factorization

**Seat:** pen-and-paper (witness, obstruction fallback). **Task #111 (T4 sub-lemma).** **Date:** 2026-07-10.
**NO Lean.** **Charge:** exhibit the load-bearing CoV that discharges `DecoratedPeelStep` — pull back BOTH
the freed loss AND the Lebesgue measure so the decorated chart integrand factors into a monomial radial
factor × the reduced decorated loss on `redChain M`, at reduced exponent `c′ − peelCharge/2`.
**Exact algebra:** `/tmp/peelcert_221.py`, `/tmp/peelcert_num.py`, `/tmp/peelcert_factored.py`,
`/tmp/peelcert_reduced.py`, `/tmp/peelcert_matrixP.py`, `/tmp/peelcert_homog_num.py` (sympy residual-0 +
MC guide). **Decorrelated:** `codex/crux-{prompt,answer}.md` (gpt-5.x, xhigh; my conclusion WITHHELD — it
independently reproduced the exact CoV, the radial exponent `α = M₁M₂−1−2c′`, the Gram-power cancellation,
the scope, and the degenerate-`Q_b` obstruction).

---

## VERDICT (headline)

**WITNESS DELIVERED, with an exact scope.** The descent is a genuine change of variables and it factors
the freed loss and measure EXACTLY as

> `(freed chart integrand)·dμ  =  (monomial radial factor u^{α} du) × smooth-positive-unit × (redChain product loss)^{−c′′}·dμ_reduced`,

with the reduced loss the **`redChain M` product loss** `frobSq(prod (redChain t M) B)` and reduced exponent
`c′′ = c′ − peelCharge/2 < ½·minAdm(redChain)`. This is an **exact local normal form on the dominant-corank
chart** — NOT a single global equality of box integrals. Two things are honestly scoped, not swept:

1. a residual **angular Gram factor** `det(Q̂_b Q̂_bᵀ)^{−a/2}` that is a **smooth positive unit only where a
   `b×b` minor of the corank tail is bounded below** (the dominant-minor chart);
2. on the complementary **degenerate-`Q_b`** locus the whole-line `Γ`-peel is unsafe — there the **bounded
   branch** (Regime B, no peel) closes it, and the deeper rank strata are already inside the reduced chain's
   own `minAdm`, so the one-shorter IH covers them.

The `(2,2,1)`, `t=1` bottleneck is computed end-to-end EXACTLY below (every identity residual-0; threshold
`c′<1 = ½·minAdm` confirmed symbolically and by MC). The general-`M` ingredients are all exact and
decorrelated-confirmed; the ONE genuinely-new general obligation is the measure-matching of the residual
(item 1/2), verified exactly at `(2,2,1)` and characterised precisely below.

**This is not a wall.** The reduced integral, on the dominant chart, is dominated by the `redChain` box
integral at `c′′`; the one-shorter IH `RouteMBoxThresholdFinite (redChain t★ M)` closes the peel.

---

## OBJECTS (from the banked freed form)

Fix a chart `(t, ρ, κ)` on `M : Fin (L+3) → ℕ`. Write `a = M₀−t`, `b = M₁−t`, `q = M_last`,
`peelCharge = a·b` (`RouteMSJDecoratedCharge.peelCharge M t`). The banked equality
`gammaPeelIntegral_schurShearFree_eq` (`RouteMSJFreedPeel`) rewrites the per-chart peeled integral to the
**freed-`Γ`** form

    gammaPeelIntegral M t ρ κ c′ = ∫_{A′∈box(tailChain)} ∫_{x=(P,B₁₂,C)∈outerDom} ∫_{Γ∈shearbox}
                                     (freedSchurLoss x Γ Q̃)^{−c′}

with `Q̃ = (prod (tailChain M) A′).submatrix (blockSplitEquiv κ) id : (Fin t ⊕ Fin b) → Fin q`,
`Q_p = Q̃|_inl` (`t×q`), `Q_b = Q̃|_inr` (`b×q`), and (`RouteMSJChartShear.freedSchurLoss`)

    freedSchurLoss x Γ Q̃ = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b),   Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b.

`P` is `t×t` invertible, `B₁₂` is `t×b`, `C` is `a×t`, `Γ` is the freed `a×b` corank block (independent
variable over a translated unit box).

---

## THE CoV (i) + JACOBIAN (ii) — exact, two steps

The tail's first matrix is `A₁ : M₁×M₂`; split its rows by the pivot cut `A₁ = (X ; Y)` with
`X : t×M₂` (pivot rows), `Y : b×M₂` (corank rows). Deeper tail `A_{≥2} := A₂···A_L` (unchanged).
Then `Q̃ = A₁·A_{≥2}` reindexed, so `Q_p = X·A_{≥2}`, `Q_b = Y·A_{≥2}`.

**Step 1 — linear "absorption" CoV (renaming A₀'s pivot block into A₁'s pivot rows).**
At fixed `(P, B₁₂)`, substitute

    (X, Y)  ↦  (B, Y),   B := P·X + B₁₂·Y   (t×M₂),   and set  C′ := C·P⁻¹.

Jacobian (per column of `M₂`): `∂B/∂X = P`, so **`d(X) = |det P|^{−M₂} d(B)`** — the pivot-gauge
Jacobian. Under it the freed loss rewrites EXACTLY (verified residual-0, scalar `/tmp/peelcert_221.py` and
matrix-`P` `/tmp/peelcert_matrixP.py`):

    freedSchurLoss = ‖B·A_{≥2}‖²_F + ‖C′·B·A_{≥2} + Γ·Y·A_{≥2}‖²_F
                   = frobSq(B₀) + frobSq(C′·B₀ + Γ·Q_b),   B₀ := B·A_{≥2} (t×q), Q_b = Y·A_{≥2}.

`B` is the **reduced leading matrix**: `A₀`'s pivot block is absorbed into `A₁`'s pivot rows, so
`(B, A₂, …, A_L)` are the matrices of `redChain t M = (t, M₂, …, M_L)` and `B₀ = prod(redChain)`.

**Step 2 — radial blow-up of `(B, Y)` (dimension `M₁·M₂ = (t+b)·M₂`).** On a local blow-up chart

    (B, Y) = u·(B̂, Ŷ),   u ≥ 0,  (B̂, Ŷ) on the unit sphere (a bounded coordinate chart),

the Lebesgue measure and loss pull back as

    d(B,Y) = u^{M₁M₂−1} du dσ,     freedSchurLoss = u²·freedSchurLoss(x, Γ, (B̂,Ŷ))   (homogeneity, residual-0).

**(ii) The radial monomial exponent** (after Step 3's `Γ`-peel folds in the Gram power — see below):

    α = M₁·M₂ − 1 − 2c′,     radial factor ∫₀^· u^{α} du  finite ⟺ c′ < M₁M₂/2.

Since `minAdm(M) ≤ M₁·M₂` (EXACT, 0/1344 chains `L=3..5`, `/tmp/peelcert_factored.py`), the radial factor
**never binds before `½·minAdm(M)`** — the reduced chain is the binding constraint. (Codex Q3, independent.)

---

## THE FACTORING (iii) + REDUCED-LOSS IDENTIFICATION (iv)

**Step 3 — the corank `Γ`-Morse peel (block split; the exponent shift + the Gram weight).** On the
full-row-rank locus of `Q_b`, integrating `Γ` over `ℝ^{ab}` (upper bound; banked
`corankBlock_morsePeel_lt_top` / `freedSchurLoss_inner_peel_lt_top`, Regime A, needs `c′ > ab/2`):

    ∫_{ℝ^{ab}} freedSchurLoss^{−c′} dΓ = K(a,b,c′) · det(Q_b Q_bᵀ)^{−a/2} · frobSq(B₀)^{−(c′ − ab/2)},

`K` a finite Beta/Gamma constant (verified residual-0 in the scalar case, and the identity
`∫_ℝ (w+ξ²)^{−c′}dξ = w^{½−c′}√π Γ(c′−½)/Γ(c′)`; `/tmp/peelcert_221.py` (4), `/tmp/peelcert_num.py`). Two
facts drop out:

- **(iv) the reduced loss is the `redChain` product loss:** `frobSq(B₀) = frobSq(prod (redChain t M) B)`
  (`B₀ = B·A_{≥2}`, `t×q`). It appears at exponent **`c′′ = c′ − ab/2 = c′ − peelCharge/2`** — the shift is
  the block Morse charge, NOT a Hölder split. In the decorated carrier this is the `SJLinGenState.loss`
  after `loss_blockSplit`; the terminal `frobSq(prod redChain)` is exactly the `trivial (redChain)`
  decoration's loss (`trivial_decLoss`, banked). The extra variables `C, Y` and the outer `P, B₁₂` enter
  only through bounded/gauge factors.

- the Gram weight `det(Q_b Q_bᵀ)^{−a/2}` with `Q_b = Y·A_{≥2}` (`b×q`). Under Step 2's blow-up
  `det(Q_b Q_bᵀ)^{−a/2} = u^{−ab}·det(Q̂_b Q̂_bᵀ)^{−a/2}`, and `frobSq(B₀)^{−c′′} = u^{−2c′′}·frobSq(B̂₀)^{−c′′}`.
  The `u`-powers combine to the radial monomial (Codex Q1, independent):

      u^{M₁M₂−1}(Jac) · u^{−ab}(Gram) · u^{−2c′′}(loss) = u^{M₁M₂−1−ab−2c′+ab} = u^{M₁M₂−1−2c′} = u^{α}.

So on the dominant-minor chart (`det(Q̂_b Q̂_bᵀ)` a smooth positive unit), by Fubini,

> `gammaPeelIntegral(chart) = (finite radial factor, c′<M₁M₂/2) × (bounded gauge factors) × ∫ frobSq(prod redChain B)^{−c′′}`,

and the last factor is dominated by the **`redChain` box integral** `routeMLayerBoxIntegral (redChain t M) c′′`.

---

## EXPONENT BOOKKEEPING (v) — the binding-cut saturation (all EXACT/banked)

- `c′′ = c′ − peelCharge/2`. Below the reduced threshold ⟺ `c′′ < ½·minAdm(redChain t M)`.
- `carrierThreshold_shift` / `half_minAdm_sub_half_peelCharge_le` (banked, 0/171):
  `½·minAdm(M) − ½·peelCharge ≤ ½·minAdm(redChain)`. So `c′ < ½·minAdm(M) ⟹ c′′ < ½·minAdm(redChain)`.
- At the **binding cut** `t★` (`exists_binding_cut`, banked): `minAdm(M) = peelCharge + minAdm(redChain t★ M)`
  (0/1344 verified as the `min`), so the implication is an ⟺ at `t★` — the residual exponent **exactly
  saturates** the reduced-chain IH threshold. This is why a black-box Hölder bound is infeasible and the
  **exact** factoring (no `p>1` split) is required: the shift is spent precisely, once.
- Radial non-binding: `c′ < M₁M₂/2` with `M₁M₂ ≥ minAdm(M)` (0/1344); `peelCharge(t★) ≤ minAdm(M)` (0/1344).

⇒ For every `c′ < ½·minAdm(M)`: the radial factor is finite AND `c′′ < ½·minAdm(redChain t★ M)`, so the
one-shorter IH `RouteMBoxThresholdFinite (redChain t★ M)` (arity `L+2`) closes the reduced factor. The peel
descends arity by one — NON-circular. This is `DecoratedPeelStep`.

---

## THE `(2,2,1)`, `t=1` BOTTLENECK — end-to-end, EXACT (`½·minAdm = 1`)

`M₀=M₁=2, M₂=1`; `t=1 ⟹ a=b=1`, `peelCharge = 1`; `redChain 1 (2,2,1) = (1,1)`, `minAdm(1,1)=1`;
`minAdm(2,2,1)=2` (binding cut `t★=1`: `2 = 1 + 1`). All blocks scalar: `p (≠0), B, C, Γ, Q_p, Q_b`.

    freedSchurLoss = (p·Q̃ₚ)² + (C·Q̃ₚ + Γ·Q_b)²,   Q̃ₚ = Q_p + p⁻¹·B·Q_b.

- **homogeneity** `freed(u·Q) = u²·freed(Q)`: residual 0.
- **CoV** `B₀ := p·Q_p + B·Q_b` (= reduced `(1,1)` matrix), Jacobian `d(Q_p) = |p|^{−1} d(B₀)` (`M₂=1`);
  freed rewrite `= B₀² + (C′B₀ + Γ Q_b)²`, `C′=C/p`: residual 0. **pivot energy `(p·Q̃ₚ)² = B₀²`:** residual 0.
- **`Γ`-peel (whole line):** `∫_ℝ freed^{−c′} dΓ = K(c′)·|Q_b|^{−1}·|B₀|^{1−2c′}` (`1−2c′ = −2c′′`, `c′′=c′−½`);
  MC ratio → 1 (`/tmp/peelcert_factored.py`). Threshold `c′ > ½ = peelCharge/2`.
- **dominant chart `Q_b = u, Q_p = u·x` (Jacobian `|u|`), `α = M₁M₂−1−2c′ = 1−2c′`:**
  `|Q_b|^{−1}·|B₀|^{1−2c′}·|u|(Jac) = u^{1−2c′}·|px+B|^{1−2c′}`. Here `|Q̂_b| = 1` (chart-`b`) — the Gram is a
  unit, absorbed. **Radial** `∫₀¹ u^{1−2c′}du` finite ⟺ `c′<1`. **Reduced** `|px+B|^{−2c′′}`, the `(1,1)`
  loss at `c′′`, finite ⟺ `c′′<½` ⟺ `c′<1`; the `|p|^{−1}` pivot factor is exactly compensated by the
  reduced-coordinate interval length (residual-0 structure, `/tmp/peelcert_reduced.py`).
- **Full `6`-dim MC** of the chart integral (guide only): finite and growing for `c′<1`, explodes at
  `c′→1⁻` — threshold `c′ = 1 = ½·minAdm(2,2,1)` (`/tmp/peelcert_num.py`).

Everything lands at `c′<1`; radial and reduced thresholds coincide because `(2,2,1)` is the minimal case
(`peelCharge = minAdm(redChain) = 1`).

---

## THE SCOPE / OBSTRUCTION, PRECISELY (the genuinely-new general obligation)

The clean factoring is a normal form **up to the smooth-positive angular Gram unit** — it is NOT a global
box-integral equality. Two scoped facts (Codex Q1/Q2, independent; matches `covdesign` §5):

- **residual angular Gram `det(Q̂_b Q̂_bᵀ)^{−a/2}`.** A unit iff a `b×b` minor of `Q̂_b` is bounded below
  (dominant-minor chart, finite cover of `{rank Q_b = b}`). For `b=1` this is just `Q̂_b ≠ 0` (the `(2,2,1)`
  chart-`b`).
- **degenerate `Q_b` (`rank < b`).** Near a rank-`(b−1)` point, in normal coordinates `z ∈ ℝ^{q−b+1}`,
  `det(Q_b Q_bᵀ) ∼ |z|²`, so `det(Q_b Q_bᵀ)^{−a/2} dQ_b ∼ r^{q−b−a} dr dθ`: a **nonneg monomial iff
  `a ≤ q−b`**, merely integrable iff `a < q−b+1`, **divergent otherwise**. So the whole-line `Γ`-peel is
  UNSAFE where `Q_b` degenerates; there use the **bounded branch** `freedSchurLoss_inner_bounded_lt_top`
  (Regime B: `0 < frobSq(P·Q̃ₚ)` bounds the integrand, any `c′≥0`, no Gram) — no peel, no Gram singularity.
  The deeper rank strata this branch leaves are exactly the lower cuts of `redChain`, already inside
  `minAdm(redChain t★ M)`, so the one-shorter IH covers them.

**This is the load-bearing general claim:** on the dominant-minor chart the reduced integral EQUALS (up to
smooth positive units and bounded gauge factors) `routeMLayerBoxIntegral (redChain t M) c′′`, so the IH
closes it; off it, Regime B + the reduced `minAdm` close it. Verified EXACTLY at `(2,2,1)`; the general
measure-matching (Gram = the redChain reparametrization Jacobian) is Aoyagi §5's resolution content — the
`~65–75%`-new part the formaliser builds, not a black-box import.

---

## LEAN-FRIENDLY WIRING (banked lemmas each step reuses)

1. **freed form** — `gammaPeelIntegral_schurShearFree_eq` (`RouteMSJFreedPeel`, EQUALITY, banked).
2. **absorption CoV** `(X,Y)↦(B=PX+B₁₂Y, Y)`, Jacobian `|det P|^{−M₂}`, freed rewrite `= frobSq(B₀)+frobSq(C′B₀+ΓQ_b)`
   — NEW (measure-preserving linear CoV per outer `x`; the algebraic identity is residual-0, transcribable).
3. **radial** — `SJDecoration.radialAttach` / `radialAttach_decLoss` (`u²` factor) / `radialAttach_integral`
   (factoring) / `radialAttachFactor_lt_top` (`c′<(j₀+1)/2`) (all banked). The radial coordinate is the
   `(B,Y)` scale; `α = M₁M₂−1−2c′` is the combined exponent (Jac − Gram − loss).
4. **`Γ`-peel / block split** — `freedSchurLoss_inner_peel_lt_top` (Regime A, `c′>ab/2`) +
   `freedSchurLoss_inner_bounded_lt_top` (Regime B, degenerate `Q_b`) (both banked). Emits `c′′=c′−peelCharge/2`
   + the Gram weight (to be absorbed, NEVER materialised as a detached det-Gram field — the atom trap).
5. **reduced loss = redChain product** — `trivial_decLoss` / `trivial_integral_eq` (banked): the terminal
   `frobSq(prod redChain)` IS the `trivial (redChain)` decoration's loss.
6. **exponent shift + charge** — `carrierThreshold_shift`, `half_minAdm_sub_half_peelCharge_le`,
   `minAdm_le_peelCharge_add_redChain`, `exists_binding_cut` (all banked, `RouteMSJDecoratedCharge`).
7. **IH** — `RouteMBoxThresholdFinite (redChain t★ M)` (the `DecoratedPeelStep` hypothesis, arity `L+2`).

The single NEW measure-theoretic obligation is (2) + the dominant-minor-chart measure-matching of the
residual Gram (item in §SCOPE). Everything else is banked.

---

## CLOSE

- **Firmest.** The CoV is exact: (a) linear absorption `B=PX+B₁₂Y` (Jacobian `|det P|^{−M₂}`) rewriting
  `freedSchurLoss = frobSq(B₀)+frobSq(C′B₀+ΓQ_b)` (residual-0, matrix-`P` verified); (b) radial blow-up of
  `(B,Y)` with exponent `α = M₁M₂−1−2c′`; (c) `Γ`-Morse peel emitting `c′′=c′−peelCharge/2` and the Gram
  weight, the `u`-powers cancelling to `α` (`u^{−ab}·u^{ab−2c′}=u^{−2c′}`); (d) reduced loss =
  `frobSq(prod redChain)`, closed by the one-shorter IH at the binding-cut-saturated `c′′`. `(2,2,1)`
  end-to-end residual-0, threshold `c′<1`. Decorrelated-confirmed term-for-term by a neutral Codex.
- **Most likely to break / watch.** The general measure-matching of the residual angular Gram
  `det(Q̂_b Q̂_bᵀ)^{−a/2}` for `b>1`: it is a smooth unit only on the dominant-minor chart; the finite-cover
  of `{rank Q_b = b}` by such charts, and the Regime-B handling of `{rank Q_b < b}` (the `a<q−b+1` boundary),
  is the genuinely-new content and the place a naive whole-line `Γ`-peel diverges. This is the same `Q_b`
  degeneracy that produced the earlier retractions — kept OUT of the clean-factoring claim by scope here.
- **Next.** (1) Formaliser: transcribe the absorption CoV (2) and the radial exponent `α`; consume the
  banked Regime-A/B + shift lemmas. (2) The dominant-minor finite cover + Regime-B assembly is the one
  new module; front-load `b=1` (covered by `(2,2,1)`) then `b=2`. (3) A reviewer should check the
  `a<q−b+1` boundary against the actual `(t,ρ,κ)` charts that arise (whether any chart forces `a≥q−b+1`
  with `Q_b` genuinely degenerate — if so, that chart MUST use Regime B, never the peel).

---

# §B=2 COVER + REGIME-B ROUTING (follow-up 1, controller task — the last scoping of the ~65-75% heart)

**Charge:** generalize the dominant-minor cover + Regime-B routing past `b=1`; front-load `b=2`;
verify the `a<q−b+1` soundness against actual charts. **Exact algebra:** `/tmp/peelcert_routing.py`,
`/tmp/peelcert_b2.py`, `/tmp/peelcert_corner.py`, `/tmp/peelcert_linchpin.py`, `/tmp/peelcert_bilinear.py`.
**Decorrelated:** `codex/degen-{prompt,answer}.md` (gpt-5.x, xhigh; conclusion withheld — it independently
derived the corner mechanism, the exact corner-codimension `= value(t+1)`, and the linchpin).

## THE ROUTING VERDICT (exact — the soundness deliverable)

For the peel at cut `t★`, with `a=M₀−t★`, `b=M₁−t★`, `q=M_last`, `Q_b` (`b×q`) the corank tail block,
there are **three** routing categories (all determined by `(a,b,q)`, exact):

| category | condition | routing |
|---|---|---|
| **(I) A-only** | `b≤q` and `a+b≤q` (`a<q−b+1`) | Regime A safe on the WHOLE chart — the whole-line `Γ`-peel's Gram `det(Q_bQ_bᵀ)^{−a/2}` is integrable even across the rank-drop locus. |
| **(II) A + corner** | `b≤q` and `a+b>q` (`a≥q−b+1`) | Regime A on `{rank Q_b=b}` (dominant-minor cover) + the **degenerate-corner** treatment on `{rank Q_b<b}` (below). |
| **(III) all-degenerate** | `b>q` | `{rank Q_b=b}` is EMPTY (`Q_b` can never have full row rank) — Regime A never applies; the whole chart is the degenerate-corner treatment. |

Scan over `L=3..5`, widths `1..5`, at the binding cut (`b>0`): **A-only `1862`, needs-corner (II)+(III)
`604`** (`≈25%`) — the corner branch is COMMON, not a rare edge. `b>q` (category III): `60/545`
(`L≤4`). So the "clean CoV closes it" story genuinely requires the corner machinery. `(2,2,1)` is
category II (`a+b=2>q=1`); `(2,3,2)` is category II (`a=1,b=2,q=2`, `a+b=3>2`).

**Exact characterization:** category II/III (needs corner) ⟺ `a≥q−b+1` ⟺ `a+b>q` ⟺ `M₀+M₁−2t★>M_last`.
The condition `a<q−b+1` I flagged in the base cert is exactly the Gram-integrability boundary (Codex Q2,
`det(Q_bQ_bᵀ)^{−a/2}dQ_b ∼ r^{q−b−a}dr` near a rank-`(b−1)` point, integrable iff `a<q−b+1`). It FAILS
for `≈25%` of charts (including `(2,2,1)`), so the corner treatment is load-bearing.

## THE b=2 DOMINANT-MINOR COVER (exact)

`{rank Q_b=b}` (`b×q`, full row rank) is covered by `(q choose b)` **dominant-`b`-minor charts**, one per
`b`-column-subset `S`, chart-`S = {|det Q_b[:,S]| ≥ |det Q_b[:,S′]| ∀S′}`. Cauchy-Binet (verified
residual-0, `b=2`, `q=2,3`): `det(Q_bQ_bᵀ) = Σ_{|S|=b} det(Q_b[:,S])²`, so on chart-`S`
`det(Q_bQ_bᵀ) ≍ det(Q_b[:,S])²` (within a factor `(q choose b)`), and the dominant minor is bounded below
by a fixed constant `δ>0` on `{|det Q_b[:,S]|≥δ}`. There the Gram is a smooth positive unit, Regime A is
the clean factoring of the base cert, and the reduced factor is `routeMLayerBoxIntegral (redChain) c′′`
(the one-shorter IH), finite for `c′<½·minAdm(M)`. **Measure-matching confirmed:** on each dominant chart
the residual Gram is a unit, so the reduced integral IS the redChain box integral at `c′′` (the base
cert's factoring, now on each chart of the cover).

## THE DEGENERATE CORNER `{rank Q_b<b}` (Codex-confirmed, exact for 3-width)

The whole-line `Γ`-peel is UNSAFE here (categories II/III): its Gram bound diverges (`a≥q−b+1`), the dyadic
`|det Q_b|`-shell sum of that lossy bound diverges (`Σ 2^{n(a−1)}`, `a≥1`), and dropping the corank term
(`freed^{−c′}≤‖B₀‖^{−2c′}`) reaches only `c′<1` — ALL three bounds are LOSSY (verified). But the TRUE
integral over the corner IS finite up to `½·minAdm(M)` (MC: the `(2,3,2)` corner `{|det Y|<0.15}` is finite
for `c′<2` and destabilizes at `c′→2`, `/tmp/peelcert_corner.py`). The correct mechanism (Codex Q1, exact
for the rank-`(b−1)` corner of a 3-width chain):

- On a chart with a rank-`(b−1)` minor of `Q_b` a unit, `Q_b ∼ diag(I_{b−1}, z)`, `z∈ℝ^{D}`, `D=q−b+1`.
- Split `Γ = (Γ_∥, γ)`, `γ∈ℝ^{a}`. **Keep `Γ` in its BOUNDED box** (do NOT extend to `ℝ^{ab}`). The
  `Γ_∥` directions are honest Morse directions — charge `a(b−1)`. (This is the `§CONCESSION` "box keeps the
  collapsing direction `O(1)`" mechanism, now inside the tail.)
- The residual is the **bounded-box bilinear** `‖B₀‖² + ‖C′B₀ + γ·z‖²`. The outer product `γ·z`
  (`γ∈ℝ^a`, `z∈ℝ^D`) is EXACTLY the **2-layer chain `(a,1,D)`**: `minAdm(a,1,D)=min(a,D)` (verified
  `0/25`), so its zeta threshold is `½·min(a,D)`. (MC confirms threshold `½·min(a,D)`,
  `/tmp/peelcert_bilinear.py`.) **This is the `(S,J)` rank-flag recursion in action** — the corner of one
  peel is itself a smaller zero-product/DLN problem.

**The corner codimension is EXACT:**

> `corner-codim = t★·q + a(b−1) + min(a, q−b+1) = value(t★+1)`  (the neighbouring admissible cut).

Verified `0 violations`: (a) `corner-codim = value(t★+1)` when `a≥D` (`/tmp/peelcert_linchpin.py`, 546
3-width charts, all cuts); (b) the **linchpin `minAdm(M) ≤ corner-codim`** (`0/546`); (c) at the binding
cut `corner-codim ≥ minAdm(M)` (`0/146`) — **the corner NEVER binds before the full-rank region**; (d) in
the safe regime `a<q−b+1`, `corner-codim = t★q+ab = value(t★) = minAdm(M)` (`0/151`). So the corner is
integrable up to `½·minAdm(M)` (with equality iff safe), the full-rank Regime-A region is what binds.

**"Deeper strata inside minAdm(redChain)" — confirmed, sharpened:** the corner `{rank Q_b=b−1}` has codim
`= value(t★+1) ≥ minAdm(M)` (since `minAdm = min_t value(t)`). So each deeper corank stratum corresponds to
the neighbouring cut `t★+1`, whose admissible value dominates `minAdm(M)` — the deeper strata are strictly
non-binding. `tq = minAdm(redChain t★ M)` for 3-width (the leaf), so the corner budget is
`minAdm(redChain) + a(b−1) + min(a,D)` — the redChain IH plus the corner's own Morse+bilinear charge.

## Q3 — the corner is genuinely part of the SAME peel (a correction to "offload to other charts")

Rank loss of `Q_b` is a **tail condition** (`Q_b = Y·A_{≥2}`), NOT an `A₀`-minor condition. Points with
`Γ=0` and `rank Q_b<b` **need not lie in any `t★+1` `A₀`-pivot chart** (Codex Q3). So a single `t★`-peel
CANNOT prove only the full-rank locus and offload the complement to other charts of the `A₀`-cover — it
MUST close the corner itself, via the bounded-box + bilinear-recursion above. What IS true is that the
corner's EXPONENT is governed by the neighbouring cut `t★+1`'s value (the linchpin), so it is non-binding.

## GENERAL-`M` (past 3-width): the corner RECURSES

For `L>0` (deeper tail) the corner treatment is recursive (Codex Q1 tail): the residual singular block is
not `det(Q_bQ_bᵀ)^{−a/2}` but a **smaller zero-product problem** in the flat `Γ`-block + the deeper-tail
normal variables — i.e. the corner spawns a sub-peel on `(a, 1, deeper)`, closed by the same machinery
recursively. The 3-width case is the base (bilinear `(a,1,D)` leaf); the general case is the rank-flag
recursion the `(S,J)` build already descends. The linchpin `minAdm(M) ≤ value(t★+1)` is the general
non-binding guarantee (trivially, `minAdm=min_t value(t)`); the exact per-level corner-codim generalizes
`t★q+a(b−1)+min(a,D)` layer by layer.

## UPDATED LEAN WIRING (the corner adds to the base cert's list)

8. **dominant-minor cover** — Cauchy-Binet `det(Q_bQ_bᵀ)=Σ_S det(Q_b[:,S])²` + the finite `(q choose b)`
   dominant-chart partition of `{rank Q_b=b}`. NEW (measurable, `det` continuous).
9. **corner (categories II/III)** — bounded-box `Γ_∥` Morse (banked corank-atom shape, restricted to the
   box = Regime B `freedSchurLoss_inner_bounded_lt_top`) + the residual `(a,1,D)` bilinear closed by the
   `minAdm(a,1,D)=min(a,D)` leaf (banked base `sjBase1_freeMatrix` / the free-matrix Morse). The linchpin
   `minAdm(M) ≤ t★q+a(b−1)+min(a,q−b+1)` is a NEW ℕ-lemma (0/546, 3-width; general = the rank-flag
   sub-additivity generalizing banked `minAdm_rrp_subadd`).
10. **`b>q` charts (category III)** — no full-rank locus; the whole chart is the corner treatment (9).

## CLOSE (follow-up 1)

- **Firmest.** Routing is exact and three-way: A-only (`a+b≤q`), A+corner (`b≤q<a+b`), all-degenerate
  (`b>q`); `≈25%` need the corner. The `b=2` dominant-minor cover is exact (Cauchy-Binet residual-0). The
  degenerate corner is closed WITHIN the peel by bounded-box `Γ_∥` Morse + the residual `(a,1,D)` bilinear
  recursion; its codim `= value(t★+1) ≥ minAdm(M)` (linchpin `0/546`), so the corner is non-binding and the
  full-rank Regime-A region binds. All decorrelated-confirmed (Codex derived the corner mechanism + the
  `value(t+1)` identity independently).
- **Most likely to break / watch.** (i) The general-`M` (deeper-tail) corner recursion — I certified the
  3-width base exactly; the recursive step (corner spawns a sub-peel) is the rank-flag recursion, verified
  only via the linchpin `minAdm≤value(t+1)` (which is general and trivial from the `min`), not the full
  per-level exponent count. (ii) The `b>q` charts are entirely degenerate — confirm the banked driver's
  cover actually produces such charts and that Regime B closes them (no full-rank locus to lean on).
- **Next.** (1) Formaliser: the corner ℕ-linchpin `minAdm(M) ≤ t★q+a(b−1)+min(a,q−b+1)` (new, 0/546) +
  the `minAdm(a,1,D)=min(a,D)` leaf. (2) The bounded-box `Γ_∥`-Morse + bilinear-`(a,1,D)` corner module,
  front-load `(2,3,2)` (`b=2`, category II). (3) A reviewer on the general-`M` recursive corner (past
  3-width) — the one piece verified only via the trivial `min` linchpin, not a full exponent count.
