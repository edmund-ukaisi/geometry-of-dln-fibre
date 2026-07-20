# Hunt cert — the exhaustiveness KILL-SEARCH (run, adversarial) (hunt-t03)

**Seat:** pen-and-paper, **direction: witness / counterexample hunter.** **Date:** 2026-07-17.
**Target (map node `coverage-theorem`, the expedition-level kill-condition):** exhibit a divisorial
valuation `v` of the DLN core ideal `I = ⟨(∏_s C^{(s)})_{ij}⟩` with ratio `ρ(v) = (h+1)/(2k) < ½·minAdm(M)`
— i.e. `rlct(I) < ½ minAdm`, which would refute the paper's value and reopen the engine at the design level.
**Verdict: SURVIVE.** No such valuation found across all tiers and instances; the value `rlct = ½ minAdm`
is corroborated on every instance searched. An empty hunt is scoped evidence, NOT a proof (§5).

Scripts (all exact unless marked float): `threads/03-hunt/scripts/h1..h10`. Every load-bearing number is
exact rational (`Fraction`/sympy/Singular Gröbner); Monte-Carlo (h4) is a decorrelated GUIDE only.

---

## 0. The pinned convention (kill test)

For a divisorial valuation `v` centered at 0 of `I`, `ρ(v) = A_v/(2·v(I))`, `A_v` = log discrepancy over
the smooth ambient, `v(I) = min_g v(g)`. For a birational chart `φ:(new y)→(old entries x)` and a monomial
weight `w`, the induced valuation has (change-of-variables / relative-canonical rule)

    2ρ = ( Σ_i w_i + w(det ∂φ/∂y) ) / ( min over generator-monomials of w·exponent ),

with `w(·)` the min weighted degree over the sympy-EXPANDED (cancellation-corrected) support. **KILL iff**
`2ρ < minAdm` for some genuine chart+weight. (The proto's `R(w)` is this `2ρ`; the proto compared it to
`½minAdm` — a factor-2 scale slip that happened to be harmless because `R(w)` sat above both.)

## 1. Tier A — original-coordinate monomial valuations (pre-filter; VACUOUS as designed) — `h1`

Exhaustive `{0..2}` for ≤12 vars, structured+random above. **No undershoot on any instance:**

| M | minAdm | min 2ρ (orig-monomial) | ρ | ½minAdm | undershoot |
|---|---|---|---|---|---|
| (2,2,2) | 3 | 4 | 2 | 3/2 | no |
| (2,2,1) | 2 | 2 | 1 | 1 | no (reaches) |
| (2,2,3) | 4 | 4 | 2 | 2 | no (reaches) |
| (3,3,4) | 8 | 9 | 9/2 | 4 | no |
| (2,2,2,2) | 3 | 4 | 2 | 3/2 | no |
| (2,3,2,2) | 3 | 4 | 2 | 3/2 | no |
| (4,4,4,4) | 11 | 16 | 8 | 11/2 | no |

Confirms §1 of the spec: the lct-achieving valuation is NON-monomial in original coordinates (min 2ρ sits
*above* minAdm for (2,2,2),(3,3,4),(2,2,2,2),(2,3,2,2),(4,4,4,4)); (2,2,1),(2,2,3) already reach it.

## 2. Independent codimension — TWO decorrelated methods — `h2` + Singular

`codim V(I) = minAdm` is the hinge: it makes Watanabe's universal `rlct ≤ ½·codim` target *exactly*
`½minAdm`, and the component-order valuations `ord_{S(t)}` realize `codim S(t)/2 = Mval(t)/2 ≥ minAdm/2`
(the achiever family). Confirmed two independent ways:

- **Exact Jacobian rank** at a genuinely-generic stratum point (nested-subspace builder), all 6 instances:
  `min_t codim = minAdm` EXACTLY — (2,2,2)=3, (2,2,3)=4, (3,3,4)=8, (2,2,2,2)=3, (2,3,2,2)=3, (4,4,4,4)=11.
  (Per-stratum: every top/minimal stratum matches `Mval`; a few NON-maximal profiles for (2,3,2,2) sit
  *below* their `Mval` because they are absorbed into a bigger component's closure — e.g. `{C1=0}` (codim 6)
  lies inside the codim-4 component — which never lowers the minimum. Expected, not a defect.)
- **Singular Gröbner dimension** (totally different method): (2,2,2) codim 3, (2,2,2,2) codim 3, (3,3,4)
  codim 8 — all = minAdm.

## 3. Monte-Carlo rlct estimate — decorrelated GUIDE (float) — `h4`

Sublevel-volume local slope `d log V/d log t → rlct`. On the well-sampled instances (2,2,2),(2,2,3),
(2,3,2,2),(2,2,2,2) the slope RISES toward `½minAdm` as `t→0` (the `(−log t)^{θ−1}` factor biases it
downward at finite scale); the "below" flags all sit at large `t` and vanish as `t` shrinks — the signature
of consistency, not a kill. (3,3,4),(4,4,4,4) are undersampled by uniform MC (codim 8, 11); (3,3,4) is an
`L=2` RRR core = Aoyagi–Watanabe 2005 prior work, its codim exactly confirmed above.

## 4. Tier B — composed incidence charts + EXACT all-weights min ratio (THE GATE) — `h5..h10`

The genuine untracked-divisor family. Each chart = incidence peel `C^{(s)}=α[[1,a],[b,ab+Δ]]` (rank-1
pivot) **composed with a shear** exposing the product-vanishing conditions `g=[1,a]·(rest)` as coordinates
(without the shear, Tier B is as vacuous as Tier A — `h3` on raw incidence coords gives 4). sympy computes
the exact Jacobian (a single monomial `α^{mn−1}`, so the numerator is LINEAR) and the transformed
generators; the min `2ρ` over the **entire continuous weight space** is then exact rational **vertex
enumeration** (small charts) or an **LP** — not a grid.

| M | chart | Jacobian | min 2ρ | ρ | ½minAdm | verdict |
|---|---|---|---|---|---|---|
| (2,2,2) | incid C1 + shear | α³ | **3** (vertex-enum, exact) | 3/2 | 3/2 | achiever, 0 undershoot |
| (2,2,3) | incid C1 + shear | α³ | **4** (LP) | 2 | 2 | achiever, 0 undershoot |
| (3,3,4) corank-2 | incid C1(3×3) + shear | α⁸ | **8** (LP) | 4 | 4 | achiever, 0 undershoot |
| (2,2,2,2) | double incid C1,C2 + shear | α1³α2³ | **3** (LP + grid) | 3/2 | 3/2 | achiever, 0 undershoot |
| (2,3,2,2) | double incid C1,C2 | α1⁵α2⁵ | **4** (LP) | 2 | 3/2 | 0 undershoot (non-min branch) |

- **(3,3,4) is the flagged corank-2 sharing case.** A single rank-1 peel of the 3×3 `C1` leaves a 2×2
  `Δ`-block — the exact regime where D3's kill-condition lives. The GENUINE chart (which carries the shared
  `Δ` correctly via its incidence coordinates) gives `ρ=4`, **not** the spurious `3`. The "3" the D3 cert
  found from *independentising* the sharing is an artifact of wrong ideal bookkeeping — it is NOT realised by
  any genuine weight in the real chart (the real product ideal, computed by sympy, gives 4). Decorrelated
  confirmation that the diag(b) support is load-bearing for the ≥-leg, and that mis-tracking it is a proof
  risk, not a real sub-threshold divisor.
- **Tier B2 (alternative pivots):** (3,3,4) at pivots (0,0),(1,1),(2,2) all give `2ρ=8` — pivot-independent
  (permutation invariance of the divisor ratio).
- **Tier B3 (weighted centers):** subsumed — the LP/vertex-enum minimises over ALL weights (uniform AND
  non-uniform), so every weighted blow-up of the chart is searched; the min is the lowest such divisor.
- **Second blow-up of the non-NC binomial leaf (`h10`, self-red-team of Q1b/Q4):** the (2,2,2) leaf ideal
  keeps binomials `α(b·g0+δ·c210)`; blowing up `{b=δ=0}` (both standard charts) gives `2ρ ∈ {3,4} ≥ 3`. No
  sub-threshold divisor hides one blow-up below the leaf (the mediant / no-new-smaller-ratio behaviour holds
  here). With generic ±1 coefficients a binomial never vanishes above `min` of its two monomials, so the
  LP's min-of-monomials is the true valuation.

## 4″. The ANGULAR family — closing the Codex-identified gap (`h11`) — the sharpest extension

Decorrelated Codex red-team (`codex/hunt-redteam-{prompt,answer}.md`, gpt-5.6-sol xhigh, my conclusion
withheld) correctly isolated the one family the toroidal LP does NOT reach: **non-coordinate "angular"
centers** where coefficient residues satisfy a relation — for (2,2,2,2), `h = 1 + a1·b2 = 0` (the rank-1 row
direction selected in `C^{(1)}` annihilating the rank-1 column direction in `C^{(2)}`). It exhibited a
concrete missed divisor `E_Z` (center `(α1,α2,d1,d2,p,q,r,s,h)=0`, `a1,b2` units) with `2ρ = 15/4` — not an
undershoot, but proof the family is genuinely outside the toroidal LP.

I ran Codex's exact test: on `a1≠0` introduce `h` as a coordinate (`b2 = (h-1)/a1`), recompute the product
and the now-RATIONAL Jacobian `det = α1³α2³/a1` (sympy), and search. The engine **reproduces Codex's `E_Z`
= 15/4 exactly** (independent validation), and both an exhaustive `{0,1,2}^12` search AND an LP over the FULL
continuous weight space give **min 2ρ = 3 = minAdm — zero undershoot.** So the angular divisors of
(2,2,2,2) do not undershoot either; Codex's gap is closed for (2,2,2,2).

Codex also (Q4) confirmed the (2,2,2) leaf ideal is genuinely monomial:
`α⟨g0,g1,bg0+δc210,bg1+δc211⟩ = α⟨g0,g1,δc210,δc211⟩` (the binomials reduce mod `g0,g1`), so no
valuation-theoretic cancellation can raise `v(I)` there — the (2,2,2) LP result is airtight. (Q4 does note
generic binomials CAN cancel to higher order along a non-toroidal center in general — real, but moot for this
leaf.) Q2: the NC-folklore holds only after full principalization (locally-principal monomial), not from an
SNC zero-set alone — respected here (the searched leaves are monomial or LP-certified).

## 4′. Tier C — tracked-leaf completeness (`d2_reduction_census`, re-run) — CONFIRMS the tracked family

The block-eliminated monomial ideal at each rank-`t1` stratum has Newton-LP rlct **==** closed form
`½[nReg + minAdm(M_res)]`, and every stratum ratio `≥ ½minAdm`, on (2,2,2),(2,2,3),(3,3,4),(3,2,3). So
`min over tracked leaves = ½minAdm` exactly, and no tracked leaf undershoots.

## 5. VERDICT, scope, and what an empty hunt does / does not license

**SURVIVE — no genuine divisorial valuation below `½minAdm` on any instance searched.**

**Scope statement (in the form the `coverage-theorem` node can cite):**
> On M ∈ {(2,2,2),(2,2,3),(3,3,4),(2,2,2,2),(2,3,2,2)} [and (2,2,1),(4,4,4,4) at Tier A + codim only], an
> exact decorrelated kill-search over — (A) all small-weight monomial valuations in original coordinates;
> (B) the FULL continuous space of monomial weights (TOROIDAL divisors) in the incidence+shear resolution
> charts of the minimizing rank-1 (and the corank-2 for (3,3,4)) branch, with Jacobian-corrected log
> discrepancy; (B2) alternative pivots; (B3, subsumed) weighted centers; (B-angular) for (2,2,2,2), the
> non-toroidal angular relation `h = 1 + a1·b2 = 0` as a coordinate, over the full weight space; and (C) the
> tracked-leaf Newton-LP values — found NO divisorial valuation with ratio `(h+1)/(2k) < ½minAdm`.
> `codim V(I) = minAdm` was independently confirmed by two methods (exact Jacobian rank + Singular Gröbner
> dimension), so Watanabe's `rlct ≤ ½minAdm` is tightly targeted and the achiever divisors `ord_{S(t)}`
> realise `½minAdm` exactly. This is scoped corroboration of the coverage ≥-leg, NOT a proof.

Precisely (per the Codex red-team): the certified statement is *"min over the toroidal divisors of the
searched charts at generic centers — plus, for (2,2,2,2), the `h=1+a1b2` angular divisors — is `≥ minAdm`"*,
not a statement about ALL divisors over those charts.

**NOT reached (residual scope, honestly stated):**
- (i) angular / non-coordinate centers for instances OTHER than (2,2,2,2) — Codex's `h=1+a11 b21+a12 b22=0`
  for (2,3,2,2), and the general adjacent-layer incidence relations; (2,2,2,2)'s angular family IS searched;
- (ii) 3rd+ nested blow-ups inside not-yet-NC charts for instances other than (2,2,2) (checked only there);
  Q4's non-toroidal binomial-cancellation centers (real in general; moot for the (2,2,2) monomial leaf);
- (iii) the (2,3,2,2) and (4,4,4,4) MINIMIZING-branch weighted searches (codim confirmed, but the incidence
  chart for the exact minimizer was not built — for (2,3,2,2) the chart I built binds at `ρ=2`, not the
  minimizer `3/2`);
- (iv) (4,4,4,4) exact chart (48 variables, compute-heavy) — covered only by Tier A + the exact codim check.

**Sharpest complete check for the open part (Codex Q5):** compute the local log-canonical threshold `lct_0(I)`
of the four-entry IDEAL (NOT `Σ P_ij²`) via a D-module / multiplier-ideal engine (Macaulay2
`MultiplierIdeals`, or Singular `dmod.lib`) and compare to `minAdm` (= 2·½minAdm; recall my `2ρ = A/v(I)`).
This is complete and fully independent of the incidence resolution; a lower complex threshold whose center has
a real smooth point would be a genuine kill. (M2 is not installed here; Singular's `dmod.lib` route is the
next tool to try — deferred.)

## 6. Firmest / most likely to break / next

- **Firmest:** the value `rlct = ½minAdm` is corroborated by FIVE decorrelated legs (Tier A vacuity, two
  independent codim methods, MC guide, exact per-chart LP reaching the achiever with zero undershoot, Tier C
  leaf census). The corank-2 (3,3,4) genuine chart giving 4 (not the spurious 3) directly answers the
  sharpest D3 concern.
- **Most likely to break it (if anything):** an `L≥3` **angular / non-toroidal** divisor — a center combining
  an adjacent-layer incidence relation (`h=1+a1b2=0` type) with residual `D`-block conditions — that the
  layerwise toroidal peel does not expose. For (2,2,2,2) this exact family was searched and did NOT undershoot
  (§4″); for (2,3,2,2) the analogous `h=1+a11 b21+a12 b22=0` family is the top residual (scope (i)). This is
  the coupled-sharing regime the engine is built for, so also where a transcription error would bite.
- **Next construction to settle the open part:** (1) run the (2,3,2,2) angular family `h=1+a11 b21+a12 b22`
  (same `h11` recipe); (2) the D-module `lct_0(I)` check (Codex Q5, Singular `dmod.lib`) for (2,2,2,2)/(2,3,2,2)
  — the single most decorrelated COMPLETE test; (3) the exact minimizing-branch chart for (2,3,2,2) `t=(2,1,0)`
  and a truncated (4,4,4,4) `t=(2,1,0)`. The exhaustiveness ARGUMENT (every exceptional prime created at a
  definite `(S,J)` stage — Codex-Q3 in cert-d3) remains the proof; this hunt is its decorrelated stress-test
  and it did not break it.

## 7. What the spec missed / I added (adversary's notes)
- **The shear is load-bearing for Tier B.** The spec's Tier B says "search coordinate-changed valuations"
  but a search on the RAW incidence coordinates (`h3`) is as vacuous as Tier A (min 2ρ = 4). The chart must
  ALSO shear-expose the product-vanishing conditions `g` as coordinates before any deep divisor becomes
  monomial. Without this, Tier B "passes" for the wrong reason.
- **Exact fractional-program over the CONTINUOUS weight space** (vertex-enum/LP) replaces the spec's
  "small-integer w" grid — this makes each chart's "no undershoot" a real per-chart certificate (captures
  non-integer optimal vertices), not a sampled one. Enabled by the incidence Jacobian being a single
  monomial ⇒ linear numerator.
- **Two-method codim confirmation** (Jacobian rank + Gröbner) is a decorrelated leg the spec did not list;
  it is what pins Watanabe's bound to the right value.
