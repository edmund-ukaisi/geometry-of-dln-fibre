# obl2-form-cert — the correct minimal form of obligation 2 (the non-submersive product-corank wall)

**Seat:** pen-and-paper (design, `obstruction`), aoyagi-full `genm-obl2form`. **Date:** 2026-07-17.
**NO Lean edits, NO build.** Exact algebra + power-counting + decorrelated numerics (`scratch/obl2_verify.py`,
`scratch/inner_verify.py`, `scratch/const_width.py`) + decorrelated `local-codex-consult` (gpt-5.x xhigh, my
conclusion WITHHELD; `scratch/codex/{prompt,answer}.md`). Two decorrelated lines converge on the same verdict.

---

## ★ VERDICT (firm, three questions, one mechanism)

**(a) Is the clean-det-power obligation 2 FALSE?  → YES, FALSE.**
The engine's `nonsubmersive_Ar_principalization` — `∫_{A'} det(Q_b(A')·Q_b(A')ᵀ)^{−t/2} < ⊤` — and the
NEW l2engine Gram-collapse form — `∫_{A'} det(Q(A')·Q(A')ᵀ)^{−a/2} < ⊤` over the deeper tail PRODUCT
`Q = prod(tailChain M) A'` — are BOTH **FALSE** (divergent) on a positive-measure family of legal
min-corank≥2 cuts, including the engine's OWN canonical example `M=(4,4,4,4) @ t=2`. A `sorry` on either
makes the socket conditional on a false hypothesis (the precision.md trap: a sufficient condition that is
never satisfiable proves nothing).

**(b) Does the Schur-complement Gram-identity collapse DISSOLVE the wall?  → NO. WALL STANDS.**
The identity `det(Q̃ₚQ̃ₚᵀ)·det((Q_bΠ)(Q_bΠ)ᵀ) = det(QQᵀ)` is TRUE (algebraic; reproduced, 200 samples).
But it does NOT make `∫_{A'} det(QQᵀ)^{−a/2}` a "tractable classical Wishart integral." The collapse
rests on replacing the true inner Morse integral `I(S)` by its overestimate `det(SSᵀ)^{−a/2}` — the exact
overestimate l2morse just refuted — so it re-commits the lossy factorization at the level of the FULL Gram.
`Q` is a multi-layer product (≥2 free factors for L≥1); the product acquires the factor divisor `{det L=0}`
that lowers the convergence threshold from the free `a < q−n+1` to `a < 1`, so it DIVERGES for every
`a ≥ 1` (and `a = M₀−t ≥ 2` always under min-corank≥2). This is the SAME `GAP-IN-RELATIVE-JACOBIAN`
prodcorank / decstep / l2svd §9 identified — the collapse relocates it to `Q`, it does not remove it.

**(c) The correct minimal obligation 2.** NOT any isolated det-power factor (all three variants are the same
lossy factorization and all are FALSE). The correct minimal obligation is the **coupled / iterated**
finiteness of the freed-Γ triple integral against the rank-drop boundary — exactly `corankStratum_lt_top`'s
iterated statement on the generic-rank (top) stratum, resolved by BLOWING UP the rank-drop boundary of the
product `Q` while KEEPING the inner Morse decay coupled to the outer Jacobian. Its truth is a sub-case of
the Aoyagi-finite socket (TRUE); it is MINIMAL (the transcription pieces — the Morse family `corankSVD…`,
the full-rank-interior pivot-Gram disposal — are separate and done/routed); and it is the right target for
a stratification/blow-up reduction. The genuinely-OPEN content is the non-submersive principalization of
that coupled object (all exponents `> −1`, no smaller-ratio divisor) — the wall, Aoyagi's stated future work.

---

## 1. Objects (recall, from RouteMSJProductCorankEngine.lean @ origin/genm-l2engine)

For a min-corank≥2 pivot cut `t` (`a := M₀−t ≥ 2`, `b := M₁−t ≥ 2`), the socket
(`productCorankBoxFinite` = `cited_aoyagi_product_corank`) is the freed-Γ triple integral
`T = ∫_{A'} ∫_x ∫_Γ freedSchurLoss(x,Γ,Q)^{−c'}`, `Q = (prod(tailChain M) A').submatrix(blockSplitEquiv κ) id`
a `(t+b)×q` matrix (rows `Fin t ⊕ Fin b` = pivot block `Q_p` over corank block `Q_b`), `c' < minAdm M / 2`.
`T < ⊤` is TRUE (Aoyagi, below threshold) — that is the theorem to be proved.

The engine's reduction: (2) integrate `C` → pivot Gram `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` × residual; (4) integrate `Γ`
via the Morse family with `S = Q_bΠ`; (8) dispose the pivot Gram via a CoV to a free Wishart, producing the
CoV Jacobian `det(Q_bQ_bᵀ)^{−t/2}`; (9) integrate `A'`. Obligation 2 is the `A'`-integral of the isolated
CoV Jacobian. The NEW collapse uses the Gram identity to fold the two det-powers into `det(QQᵀ)^{−a/2}`.

---

## 2. Finding 1 — the TRUE inner `I(S)` is MILD near the rank-drop (CONFIRM l2morse, exact asymptotic)

With `S` fixed, `frobSq(ΓS) = Σ_{i,j} λ_j Γ̃_{ij}²` (`λ_j` = eigenvalues of `SSᵀ`, `Γ̃ = ΓV`, unit Jacobian;
Morse). Let one eigenvalue drop: `λ_b = ε → 0`, others `Θ(1)`. Split the active columns: `p := a(b−1)`
(surviving), full `ab`. Exact 1-D radial reduction gives, over a bounded box:

- **Regime 1** `2c' < p = a(b−1)`: `I(ε) → I(0) < ∞` (the dropping column integrates to a finite volume
  factor). **BOUNDED** — no blow-up.
- **Regime 2** `p ≤ 2c' < ab`: `I(ε) ~ K·ε^{−(2c'−p)/2}`, i.e. exponent `e_true = c' − a(b−1)/2 ∈ [0, a/2)`.

In BOTH regimes `e_true = max(0, c' − a(b−1)/2) < a/2`, while the clean det-power
`det(SSᵀ)^{−a/2} ~ ε^{−a/2}`. So the clean det-power **overestimates by `ε^{−(a/2 − e_true)}`**,
`a/2 − e_true = min(a/2, ab/2 − c') > 0` — a strictly-positive lost power at EACH rank-drop.

**Numeric (a=b=2, box `[-1,1]^{2×2}`, decorrelated re-implementation, `inner_verify.py`):**
Regime 1 (`c'=0.7`, `2c'=1.4<p=2`): `I(ε)` = 15.79, 23.48, 36.11, 41.18, 42.14 as `ε=σ²`: 1, 0.25, 0.01,
4e-4, 1e-5 → converges to a finite `≈ 43`, while `det^{−1}=ε^{−1}` = 1, 4, 100, 2500, 1e5.
**This reproduces l2morse's exact sequence (15.8→23.5→36.3→41.2).** Regime 2 (`c'=1.2`): `I·ε^{0.2} ≈ const`
(exponent `e_true=0.2 < a/2=1`). CONFIRMED.

---

## 3. Finding 2 — the isolated det-power obligation 2 is FALSE (both the `Q_b` form and the collapsed `Q` form)

The isolated `∫_{A'} det(·)^{−power/2}` is a FACTORIZATION: it treats the CoV Jacobian as an outer factor
decoupled from the inner integral, and (finding 1) the inner integral's compensating decay is exactly what
gets discarded. Two independent failure modes, both giving `= +∞`:

### 2a. Structural bottleneck (integrand ≡ +∞)
If a tail width `< t+b`, the product `Q` is structurally rank-deficient, `det(QQᵀ) ≡ 0`, so
`∫ det(QQᵀ)^{−a/2} = +∞` on ALL of the `A'`-box.
**Witness `M=(3,3,2,4) @ t=1`** (a=b=2, min-corank = min(2,2) = 2 ✓, legal): tail `(3,2,4)`, `Q` is `3×q`
through width 2, generic rank 2 < t+b=3 (verified `max|det(QQᵀ)| ≈ 5e-13`). `∫ det(QQᵀ)^{−1} = +∞`.

### 2b. Non-submersive threshold lowering (the L·R factor divisor) — the generic case
For a two-factor product `Q = L·R` with `L` an `n×n` SQUARE factor (`n = t+b`):
`det(QQᵀ) = det(L)²·det(RRᵀ)` (EXACT), so `det(QQᵀ)^{−a/2} = |det L|^{−a}·det(RRᵀ)^{−a/2}` and by Tonelli
`J = (∫|det L|^{−a})·(∫ det(RRᵀ)^{−a/2})`. The divisor `{det L=0}` is codim 1, `det L` vanishes
transversely to order 1 (`det QQᵀ` to order 2), so `∫|det L|^{−a}` is finite **iff `a < 1`** — STRICTLY
below the free baseline `a < q−n+1` when `q > n`. Under min-corank≥2, `a = M₀−t ≥ 2 > 1` **always** →
**DIVERGENT**.

**Witness `M=(4,4,4,4) @ t=2` — the engine's OWN canonical example** (a=b=2, min-corank=2, no bottleneck,
`Q` generically full rank): tail `(4,4,4)` → `Q = A₁·A₂`, both `4×4` square, `det(QQᵀ)=det(A₁)²det(A₂)²`
(verified exact). `∫ det(QQᵀ)^{−1} = (∫|det A₁|^{−2})·(∫|det A₂|^{−2}) = ∞·∞`. Constant-width nets — the
canonical DLN — have ALL-square tail factors, so the collapsed obligation is `∞^{(L+1)}` on every one of
them. The true socket `T` is FINITE here (the engine's own budget `A_r=[0,1,4]→11=minAdm` presumes it).

**Numeric (`obl2_verify.py` Part C, `n=2, q=4, a=2`; free baseline `a<3` CONVERGES):** `∫_{|det|>δ}` with
`δ → 0`: FREE `Q` estimate flat (≈ 587, converges); PRODUCT `Q=L·R` estimate 5.3e4 → 8.9e5 → 9.5e6 → 9.9e7
(grows `~δ^{−1/2}`, diverges). The product diverges where the free integral converges. WALL.

### Equality-at-binding-cell
The `{det L=0}` divisor binds at `a = 1` (`∫|det L|^{−1}` = the log-divergent boundary — the exact
marginal). The free baseline binds at `a = q−n+1`. Every min-corank≥2 cut has `a ≥ 2 > 1`, so it is strictly
past the product-binding cell.

---

## 4. Finding 3 — the correct minimal obligation 2 (coupled / iterated, not factorized)

Because every isolated det-power factor is FALSE (§3), obligation 2 must carry the FULL coupled integrand.
The correct minimal statement:

> **Obligation 2 (correct).** For a min-corank≥2 cut `t` below threshold, given the one-shorter plain IH,
> the freed-Γ triple integral is finite over (a tubular neighborhood of) the rank-drop boundary of the
> product `Q`, with the inner Morse integral `I(Q_bΠ)` computed honestly and kept COUPLED to the outer
> CoV Jacobian — established by BLOWING UP the rank-drop boundary of `Q = prod(tailChain M) A'` and showing
> every exponent of the coupled integrand (inner-Morse decay × pivot-Gram × transverse `A_r`) exceeds `−1`.

This is exactly `corankStratum_lt_top`'s iterated statement on the generic (top) stratum. (The deeper
exact-rank strata are Lebesgue-null — `∫ = 0` trivially — so ALL content is the top stratum's outer
integrability against the null rank-drop boundary; l2svd §9 subtlety.)

- **(i) TRUE.** A sub-integral of the Aoyagi-finite socket `T`. Below threshold `c' < minAdm/2` it is finite.
- **(ii) MINIMAL.** The transcription pieces are removed: the Morse family `corankSVD_chartFamily_lt_top`
  (fixed-S, DONE) and the pivot-Gram disposal on the full-rank interior (obligation 1, routed) are
  separate. What remains is the boundary behavior — the non-submersive principalization — with no
  transcription padding.
- **(iii) RIGHT TARGET.** A stratification/blow-up reduction that keeps inner and outer coupled is the
  correct shape; the clean-`C(S)` factorization is precisely what fails.

**What the engine must change.** DELETE `nonsubmersive_Ar_principalization` (the isolated `det(Q_bQ_bᵀ)^{−t/2}`
form) and do NOT restate it as the collapsed `∫ det(QQᵀ)^{−a/2}`; restate obligation 2 as the coupled
iterated finiteness above. The Gram identity is a valid algebraic tool but must be used inside a coupled
estimate, never to license the isolated `∫ det(QQᵀ)^{−a/2}`.

---

## 5. Finding 4 — stratification (sound) vs the clean-C(S)/collapse factorization (unsound)

- **FAILED factorization** (both the `Q_b` CoV-Jacobian form and the Gram-collapse `Q` form):
  `T ≤ const · ∫_{A'} det(·)^{−power/2}` decouples the CoV Jacobian from the inner integral; the outer
  factor diverges (§3) while `T` converges → the bound is `T ≤ ∞`, vacuous. UNSOUND as a reduction.
- **SOUND stratification.** Split the `A'`-box into (i) the full-rank interior `{dist to rank-drop > δ}`,
  where `det(QQᵀ)` is bounded below and the CoV is valid → transcription (obligation 1 + Morse family)
  closes it; and (ii) a tubular neighborhood of the rank-drop boundary, resolved by a BLOW-UP that keeps
  the inner Morse decay coupled to the outer Jacobian. The soundness is exactly that on the boundary tube
  the coupling is never discarded — the compensating inner decay (finding 1) is what carries convergence,
  and factorization is exactly what throws it away.

---

## 6. Codex (decorrelated, conclusion withheld) — `scratch/codex/answer.md`

Fired with the frame + facts (Gram identity true; free Wishart baseline `a<q−n+1`), my conclusion withheld.
Codex LED with **THRESHOLD-LOWERED** and, [EXACT] throughout: square-`L` gives `det(QQᵀ)=det(L)²det(RRᵀ)`,
divisor `{det L=0}` codim 1, `det QQᵀ` order 2, `∫|det L|^{−a}` finite iff `a<1`; `J` finite iff `a<1` (past
the free `a<q−n+1` for `q>n`); the multiplication map `A ↦ ∏Aᵢ` is NOT submersive along the rank-drop
(cokernel dim `corank(L)(q−rank R) > 0` for `q>n`), so the pushforward density blows up relative to
free-matrix measure; one-factor peel does NOT reduce to a classical free Wishart (residual `∫|det L|^{−a}`
already forces `a<1` — "a valid induction would have to track these degenerating prefix/suffix factors");
intermediate width `< n` → `det QQᵀ ≡ 0` → `J=∞`. Independent, same verdict, same mechanism.

---

## Close

- **Firmest result.** The clean-det-power obligation 2 is **FALSE** in every isolated form
  (`det(Q_bQ_bᵀ)^{−t/2}`, and the collapsed `det(QQᵀ)^{−a/2}`): divergent on legal min-corank≥2 cuts,
  including `(4,4,4,4)@t=2`. The Gram identity is true but the convergence claim built on it is not — it
  re-commits the l2morse-refuted overestimate at the full-Gram level. The WALL STANDS (native `(□)` is not
  reachable via the collapse; the non-submersive principalization is Aoyagi's future work). The correct
  minimal obligation 2 is the COUPLED / iterated finiteness on the top stratum, resolved by a boundary
  blow-up that keeps inner decay coupled to the outer Jacobian.
- **Most likely to break it.** A width regime where the tail product is generically full rank AND all
  intermediate factors are strictly fat/tall (no square factor, no bottleneck) — there the exact
  threshold-lowering amount is width-dependent and MIGHT (for some `a`) still clear `a`. But: (i)
  constant-width and any-square-factor tails (the canonical DLN, incl. the engine's own examples) already
  falsify the ∀-statement, so the obligation as written is dead regardless; (ii) the coupled minimal form
  (§4) is what must be proved, and its convergence is not in doubt (Aoyagi) — only its native
  principalization is open.
- **Next.** l2engine: restate obligation 2 as the coupled iterated form (§4), NOT the isolated det-power;
  delete `nonsubmersive_Ar_principalization` / do not mint the collapse. The native-vs-cite decision
  (LATE-102) is unchanged by the Gram identity — the wall is intact; consolidating at the box-level cite
  `cited_aoyagi_product_corank` remains the honest default unless a full non-submersive blow-up resolution
  is built.
