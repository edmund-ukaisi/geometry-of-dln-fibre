# Design certificate — R1 threshold-only recursion (LIGHT vs HEAVY diag(b))

**Seat:** `pen-and-paper` (`witness`→flipped to `obstruction`). **Date:** 2026-06-23.
**Gates:** the R1 Lean shape — does `resolution_charts` get a *light* (threshold-only) recursion, or
must it carry Aoyagi's full per-divisor `diag(b)` data?
**Method:** exact monomial-ideal RLCT (Newton-polytope LP, validated against Codex's hand
computations to the rational), the validated peel identities (sympy, exact), MC volume-scaling as a
*guide only*, + one decorrelated `local-codex-consult` at `xhigh` (frame-in / facts-in /
hypothesis-out — my tentative conclusion withheld).
Artefacts: `/tmp/r1light_*.py` (peel identities, the monomial-RLCT machine, the obstruction pairs,
the cascade rule + its calibration); Codex prompt+answer in
`expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/light-recursion-{prompt,answer}.md`.

---

## VERDICT: **BREAKS** (for `corank ≥ 2` peels; HOLDS only for `corank ≤ 1`)

A **threshold-only** recursion — inductive invariant = (residual reduced widths) + (a *per-output-row
weight multiplicity*: an integer per row counting accumulated divisor scalars), **without** the
symbolic `diag(b)` matrix support — **does not** compute the core RLCT in general. It is provably
insufficient the moment a peel along the binding branch has **corank ≥ 2 in both layer-1 dimensions**
(i.e. the residual block `Δ` is a genuine `≥2×2` matrix, not a scalar). For those branches the value
`½·min Mval` is **not reachable by any threshold-only branch**, and the naive cascade *undercounts*.

It **HOLDS** (the light route is sound and is the real win) exactly for branches whose every peel is
**clean**: layer-1 residual codim `c₁ = 0` (full rank in the smaller dimension) **or** `corank ≤ 1`
(`Δ` a single scalar `δ`, one weighted row, no sharing ambiguity). The rank-1 chains and all the
controller-named partial-rank witnesses except `(4,4,2,2)`-type land here.

The split is the **same boundary** the existing `verify-r1-shortcut.md` found ("sub-case A `c₁=0` /
rank-1 = clean; sub-case B `c₁>0` = coupled `diag(b)`"), now sharpened with the *exact mechanism of
failure* and the *minimal sufficient invariant*.

---

## The candidate recursion (stated precisely, then refuted)

**Objects.** Core `F = ‖C¹C²⋯Cᴸ‖²` on reduced widths `M=(M¹,…,M^{L+1})`, `Cˢ` free `Mˢ×M^{s+1}`,
resolved at the origin. Established (not re-litigated): `rlctAt(F) = ½·min_t Mval(t)`,
`Mval(t) = (M¹−t₁)(M²−t₁) + Σ_{j≥2}(t_{j−1}−t_j)(M^{j+1}−t_j)`, `t` weakly-decreasing, `t_L=0`.

**Candidate LIGHT invariant.** A *weighted core* `WC = (M, rweight)` where `rweight : Fin M¹ → ℕ`
gives, per output row, the number of accumulated divisor scalars weighting it (`rweight ≡ 0` = clean).
The function is `F = Σ_i (∏ rweight[i] scalars)² · ‖rowᵢ(C¹⋯C^{Lp})‖²`.

**Candidate accounting.** Peel layer 1 at rank `t₁` (block-elim, a unit transform — Aoyagi Lemma 1,
ideal/RLCT-preserving). EXACT peel identity (verified `/tmp/r1light_peel.py`, `r1light_L4peel.py`,
`r1light_4422.py`):

    F  ~  ‖ diag(E_{t₁}, Δ)·C2'·C³⋯Cᴸ ‖²
       =  ‖ T·(C³⋯Cᴸ) ‖²  +  ‖ Δ·S·(C³⋯Cᴸ) ‖²

`T` = top `t₁` (clean) output rows; the bottom `M¹−t₁` rows are weighted by the residual block `Δ`
(an `(M¹−t₁)×(M²−t₁)` matrix of fresh scalars), `c₁ = (M¹−t₁)(M²−t₁)`. The two terms **share the deep
tail** `C³⋯Cᴸ`. The candidate's bet: track only `rweight` and the residual widths; accumulate a scalar
threshold per blow-up; `RLCT = min over the branch tree`. **Base case** `Lp=1`: a nondegenerate
weighted quadratic.

**Why it breaks.** When `Δ` is a scalar `δ` (corank 1) the candidate is faithful — one weighted row,
its monomial support is *forced* by `(widths, branch, the single weight)`. When `Δ` is a genuine
matrix (corank ≥ 2) the bottom rows are weighted by a **matrix product `Δ·S`**, not by independent
per-row scalars, and the per-row multiplicity *cannot encode which rows share which divisor variable*.
That sharing pattern changes the Newton polytope, hence the RLCT.

---

## The exact obstruction (decorrelated-confirmed, two reads agree to the rational)

The RLCT of a resolved monomial sum-of-squares `Σ_k (z^{α_k})²` is the Newton LP
`min Σ_i u_i s.t. u ≥ 0, ⟨u, α_k⟩ ≥ ½ ∀k` (my machine `/tmp/r1light_obstruction.py`; reproduces every
Codex hand value to the rational — `(3,3,2,2)`→2, clean→3/2, `(2,2,2)`→3/2).

**Smallest obstruction — divisor-variable identity (verified both ways):**

| ideal | LIGHT data | exact RLCT |
|---|---|---|
| `I_shared = (δx, δy)` | 2 rows, 1 weight each | **½** |
| `I_indep = (δ₁x, δ₂y)` | 2 rows, 1 weight each | **1** |

Same `(widths, row-weight-multiset, branch)`; RLCT differs (½ vs 1) because the *identity* of the
weight variable (one shared `δ`, or two independent) is lost by multiplicities.

**Matrix-block obstruction (the corank-2 crux), verified both ways:**

| ideal | LIGHT data | exact RLCT |
|---|---|---|
| `I_diag = ⟨diag(δ₁,δ₂)·R⟩` (per-row scalar model) | widths `(2,2,2)`, 2 rows wt 1, branch `t=(1,0)` | **1** |
| `I_Δ = ⟨Δ·R⟩`, `Δ` free `2×2` (the true block) | *identical* LIGHT data | **3/2** (`min(2,2,3/2)` after the radial `{R=0}` divisor) |

A genuine `Δ`-block produces clean pivots `Aᵢ` and *common* `ε·Bᵢ` generators that a per-row multiset
cannot predict.

**Direct DLN witness — `(4,4,2,2)`, `t=(2,1,0)`, `Mval=7`, target `rlct=7/2`.** Unique minimizer;
layer-1 corank `(M¹−t₁, M²−t₁) = (2,2)` — `Δ` is a genuine `2×2` block. Peel (verified
`/tmp/r1light_4422.py`): `F ~ ‖T C³‖² + ‖Δ S C³‖²`, all `2×2` free, sharing `C³`; the deep "weight"
`Δ·S` is itself a `(2,2,2)`-product layer, not a scalar. My *naive threshold-only cascade* on this
gives `2`, **not** `7/2` (`/tmp/r1light_coupled_resolve.py`) — i.e. the light route **undercounts the
true value by 3/2**. No `corank ≤ 1` peel reaches the (unique) minimizer, so threshold-only cannot
even recover the *value* by a clean branch. **Hard break.**

(The discrepancy `2 ≠ 7/2` also shows a hand-rolled cascade is unsafe in general — it silently drops
generators. The certified value `7/2 = ½·min Mval` is the established input; MC at `rlct=3.5` is a poor
guide (slope plateaus ~2.0 even at 6×10⁷ samples, while it tracks `(2,2,2)→1.5` and `(3,3,2,2)→2.0`
cleanly at the same budget — `/tmp/r1light_value_audit.py`). MC is a guide only; here it is near-useless
at high RLCT and is **not** the basis of any verdict.)

---

## Where threshold-only HOLDS (the partial win — exact)

`corank ≤ 1` peels have **one** weighted row (or none); its monomial support is *forced* by
`(widths, branch, the single weight)`, so the LIGHT invariant equals the full one there. Verified:

- **rank-1 chains** `(2,2,2)`, `(2,2,2,2)`, … (corank 0): clean disjoint divisor + fresh lower core,
  value `3/2` (`/tmp/r1light_chainresolve.py`, all depths).
- **`(3,2,2,2)`** `t₁=2=M²` (`c₁=0`, full-column-rank): unit reduction to a fresh `(2,2,2)` core,
  value `3/2`.
- **`(3,3,2,2)`** `t=(2,1,0)` (corank-1, `Δ=δ` scalar): residual ideal `(A₁,A₂,εB₁,εB₂,δE,δεF)`,
  RLCT `2 = ½·Mval` — **Codex-certified** (`partial-answer.md`) and reproduced by my machine.
- **`(3,3,2,2,2)`** `t=(2,1,0,0)` (genuine L=4, corank-1, `Δ=δ` scalar, **two** shared deep layers
  `C³,C⁴`): the single weighted row's support stays forced; the clean sub-chain cross-checks to
  `(2,2,2,2)→3/2` (`/tmp/r1light_L4_3322_2.py`). *(The L=4 value `2` here is consistent but I label it
  inferred, not certified — it leans on my cascade rule, which I caught undercounting at corank-2; the
  corank-1 single-row support is the certified part, anchored by the `(3,3,2,2)` Codex computation.)*

---

## What the Lean R1 must carry (the minimal sufficient invariant)

The Newton LP depends **only** on the *multiset of monomial support vectors* `{α_k}` of the resolved
generators. So the irreducible data is, per recursion level:

1. residual reduced widths `M'`, and the branch rank profile `t`;
2. **the symbolic support of the accumulated weight on each generator** — i.e. *which* divisor
   variables (with multiplicity) multiply *which* generator, including the **identity / sharing
   relations** among them. This is exactly Aoyagi's `diag(b)` invariant (each `bᵢ` a *product* of
   divisor scalars `u_{s,k}`), up to unit equivalence (numeric coefficients and analytic row/col unit
   changes need **not** be carried — they preserve the ideal).

A per-row *degree/multiplicity* is a strict coarsening of (2): it forgets sharing (`I_shared` vs
`I_indep`) and matrix-block structure (`I_Δ` vs `I_diag`). **Decorrelated Codex reached the identical
verdict and the identical minimal invariant**, constructing the obstruction pairs itself from the
setup (its conclusion was withheld in the prompt); no rubber stamp.

---

## Recommendation for the R1 Lean shape

Two sound options, the value-match holds under both:

- **(i) Hybrid (lighter where it can be).** Build the **clean disjoint divisor+core recursion** for
  `c₁=0` / corank-`≤1` peels (where threshold-only is faithful — covers `(2,2,2)`, `(2,2,2,2)`,
  `(3,2,2,2)`, `(3,3,2,2)`, `(3,3,2,2,2)`, …), and handle `corank ≥ 2` branches by the **value
  directly** (codim + the cited `½·codim` cap), not by a chart recursion. Viable **iff** a clean peel
  reaches *some* minimizer for every width vector — **`(4,4,2,2)` shows this FAILS**: its unique
  minimizer needs a corank-2 peel. So (i) is **not** general-`L`/all-widths on its own; it covers a
  scoped family (no corank-2 binding branch).
- **(ii) Commit to the coupled `diag(b)` recursion** (Aoyagi's actual structure — the symbolic support
  carried per generator). This is the **only route that is faithful general-`L`, all branch types**.
  Heavier than threshold-only, but it is the honest mechanism; the existing
  `GeneralR1Recursion.lean` SOUNDNESS NOTE already records that the dimension-conserving *clean*
  recursion is **false** (telescopes to ambient/2 = 4 for `(2,2,2)` ≠ 3/2), which is the same lesson.

**Bottom line for the gate:** the LIGHT threshold-only recursion is **not** a sound general R1 design.
It is sound only on the corank-`≤1` sub-family. For the headline (general widths) the R1 Lean build
must carry the symbolic `diag(b)` support (option ii), or restrict its *chart* recursion to the
corank-`≤1` family and take the corank-`≥2` branches by the value (option i, scoped).

---

## Scope, caveats, separation of levels

- **Levels kept separate.** This certificate is about the **resolution mechanism / chart family**
  `(ι,d,k,h)` that R1 must produce. The **value** `½·min Mval` is the established input (not
  re-derived; `(4,4,2,2)`'s `7/2` is taken as given). The `rlct = ½·codim` *reading* still rides on
  the cited analytic bound — unchanged here.
- **Proved vs inferred vs verified-by-enumeration.** *Verified exact:* the four obstruction RLCTs
  (½, 1, 1, 3/2) — two independent computations (my Newton-LP machine + Codex) agree to the rational;
  the peel identities (sympy); the clean-chain `3/2` at all depths; the `(3,3,2,2)` corank-1 value `2`.
  *Inferred (structural):* threshold-only HOLDS ⟺ every binding-branch peel is corank-`≤1` (forced by
  the support-determinacy argument + the obstruction pairs); the `(3,3,2,2,2)` L=4 corank-1 value.
  *Established input (not re-checked here):* `½·min Mval` is the true core RLCT.
- **The one thing most likely to break this:** if a clean (corank-`≤1`) peel provably reaches *some*
  minimizer for *every* width vector, then option (i) would be general after all and the "BREAKS"
  would soften to "BREAKS only for the chart-recursion, not the value." `(4,4,2,2)` already refutes
  that (unique minimizer needs corank-2), so as stated the break stands — but a *weaker* clean-reach
  claim (clean peel reaches the minimizer whenever one exists at corank `≤1`) is the right follow-up
  to pin the exact scope of option (i).
- **Next construction that would settle the open part:** a certified (not cascade-rule) exact RLCT for
  one corank-2 DLN core — e.g. resolve `(4,4,2,2)` `t=(2,1,0)` fully via the `diag(b)` recursion and
  confirm `7/2` — would both close the value-input for the witness and exhibit the minimal `diag(b)`
  data the Lean build needs, in one worked example.
