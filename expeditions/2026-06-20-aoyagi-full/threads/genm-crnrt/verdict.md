# genm-crnrt — is the Cat II/III corner / Regime-B route Lean-buildable, or a hidden wall?

**Seat:** pen-and-paper (obstruction — adjudicating one truth-value, adversarially). **Task:** does the
Cat II/III (`a+b>q`) corner / Regime-B route close the good-stratum discharge on the BUILDABLE side of
the operator-gated deeper-strata atom, or does it hide a wall / fold into the atom? **NO Lean.**
**Exact algebra:** `/tmp/crnrt_minadm.py`, `/tmp/crnrt_rlct{,2,3}.py`, `/tmp/crnrt_232.py`,
`/tmp/crnrt_deeper.py`, `/tmp/crnrt_scan{,2}.py` (RLCT via mean-excess tail-rate estimator, validated
exact on `‖w‖²`/products). **Decorrelated:** `codex/crnrt-{prompt,answer}.md` (gpt-5.x, xhigh; my
conclusion WITHHELD — open-ended integrability questions only. It independently produced the same
answers AND the sharp unified formula + the twist-lowering).

---

## VERDICT: **SPLIT — buildable ONLY at the 3-width descent base; the general corner IS the atom.**

The corner mechanism is **sound and does NOT over-claim** (unlike Cat I, which `catint` caught). But the
"buildable above the atom" part is **small**: only the **3-width base** — `b=1` charts (no deeper strata)
and the top stratum `{rank Q_b = b−1}` of a 3-width chart — closes elementarily. **86% of corner charts
(252/294, all deeper-tail) fold into the operator-gated `(S,J)` product-rank-flag atom**, because the
`(a,1,D)` leaf **REGENERATES** as a smaller (twisted) DLN whenever `Q_b = Y·A_{≥2}` is a genuine product
(any parent width ≥ 4), and `b≥2` charts additionally carry a deeper stratum `{rank≤b−2}` that recurses.
This is not a NEW wall — the cert's own post-corrections (§B=2 COVER ⚠️ + §TWIST-LEMMA) scope it honestly —
but the "the corner closes it" headline is **over-optimistic**, and there are **two concrete build traps**.

The controller's crux (Q4) resolves cleanly:
> **The `(a,1,D)` leaf closes by a clean bilinear ONLY at the 3-width base; in general it REGENERATES
> (twisted product = smaller DLN) → Cat II/III folds into the operator-gated atom.**

---

## The four adversarial checks

### Q1 — Does Regime-B AVOID the divergent `det(Q_bQ_bᵀ)^{−a/2}` weight? **YES, genuinely.**

The det weight is an **artifact of integrating `Γ` over the whole plane `ℝ^{ab}`** (Regime A). The
bounded-box route never creates it and is finite up to the **true** RLCT. Exact mechanism, decorrelated-
confirmed (Codex Q4, verbatim):

> "The determinant singularity is not a genuine obstruction below the true RLCT; it is **created** by
> integrating `Γ` over all of `ℝ^{ab}`."

Certifying computation (`a=2,b=1,q=2,t=1` = `(3,2,2)` corner, Cat II, `a≥q−b+1`):
- **Regime A** peels all `Γ` ⟹ emits `‖z‖^{−2}` on `ℝ²`, `∫‖z‖^{−2}dz` **log-divergent** (`wtint`'s WALL, reproduced).
- **Bounded box**: `f = ‖B₀‖² + ‖C'B₀ + γY‖²` with `Γ=γ` kept in the box is **finite for all `c'<2 = ½·minAdm`.**
  The singular `γ`-direction (multiplying the rank-deficient `Q_b`) is **never peeled over `ℝ^a`** — it is
  kept in the box and handed to the leaf, so the divergent Gram is declined, not absorbed. The finiteness
  comes from the `(a,1,D)` bilinear `‖γ‖²‖z‖²` contributing a **finite** RLCT `½·min(a,D)`, not from a
  det-weight bound.

### Q2 — Does the corner need the absent full Cauchy–Binet? **NO — it sidesteps it.**

The corner needs only a **rank-`(b−1)` normal form** on a dominant-`(b−1)`-minor cover (one
`(b−1)×(b−1)` minor bounded below ⟹ the `(b−1)`-block is a unit; Gaussian elimination / Schur, elementary).
For `b=1` even that is vacuous (`Q_b` is a row vector; "rank `b−1=0`" is `Q_b=0`, no minor). It does **not**
need the `det = Σ_S minor_S²` identity nor the two-sided upper bound `det ≤ N·m_S²`. (The `§B=2 COVER`
Cauchy–Binet use is for the **Regime-A good stratum** `{rank=b}` — a different part, the Cat-I side, which
DOES need the two-sided bound per `catint`. The corner does not.)

### Q3 — Does the corner hit an `a<1`-style insufficiency like Cat I? **NO.**

The corner integrability is computed **directly**: the `(a,1,D)` leaf RLCT `½·min(a,D)` via factoring
`∫‖γ‖^{−2s}·∫‖z‖^{−2s}` (exact, product rule), and the `Γ_∥` peel over a **full-rank `(b−1)`-block whose
Gram is bounded below (a unit, for ANY `a`)**. Neither is a lossy single-minor bound. Cat I's `a<1` gap was
specific to bounding `det^{−a/2} ≤ |minor|^{−a}` over the good stratum; the corner uses no such bound.

### Q4 (the crux) — Does the `(a,1,D)` leaf close by IH, or REGENERATE? **Base: closes. General: regenerates.**

- **3-width base (`L=0`), `b=1` or the top stratum `{rank=b−1}` (`Q_b` free ⟹ `z` free):** the leaf
  `f = ‖B₀‖² + ‖C'B₀ + γz‖²` closes **exactly**. The `C'B₀` coupling is **removable by comparability**
  (`C'` bounded on the box ⟹ `f ≍ ‖B₀‖² + ‖γz‖²`, RLCT-preserving), then the **direct-sum** (Thom–
  Sebastiani, disjoint variables) gives `RLCT = ½·tq + ½·min(a,D) = ½·minAdm` at the binding cut. The leaf
  contributes its OWN charge `½·min(a,D)` — it does **not** "close by the reduced-chain IH" alone; it is a
  SEPARATE bankable bilinear composed with the redChain IH via the direct-sum. Verified: `(3,2,2)` corner
  RLCT → 2 (full `= decoupled`, coupling irrelevant); `(2,3,2)` full corner → 2; standalone `(2,1,2)`
  bilinear → 1. (MC trends confirm; the exact resolution is the proof.)

- **General case (`Q_b = Y·A_{≥2}` a product — any parent width ≥ 4, i.e. `L≥1`):** the leaf is **TWISTED**.
  `z` is a coordinate of the PRODUCT `Y·A_{≥2}`, so `‖γ·(Y·A_{≥2})‖²` is a **longer chain**, and the free-`z`
  reduction **OVERESTIMATES** the threshold. Decorrelated (Codex Q5, independent):
  > "`λ_twisted = ½·min(a,m,D)` … the product structure lowers the threshold exactly when `m < min(a,D)`
  > … the bilinear free-row reduction **overestimates** the threshold in the twisted product case."
  (Example `a=2,b=1,q=2,m=1`: free leaf → `2`, twisted → `3/2`.) So the leaf does **not** close by a naive
  free bilinear; it **regenerates** as a smaller DLN → the `(S,J)` product-rank-flag recursion = the atom.

- **`b≥2` deeper strata `{rank Q_b ≤ b−2}`:** even 3-width. E.g. `(2,3,2)`'s `{Q_b=0}`: the deepest corner is
  `frobSq(Γ·Q_b)`, which is itself the `(1,2,2)` **sub-DLN — Cat II again** (verified: `Φ(1,2,2)` minimised at
  `r=1`). It **recurses**. Non-binding (`½·minAdm` is not lowered — the deep stratum has RLCT `2`, from the
  direct sum `1+1`), but **proving** it non-binding requires resolving the sub-bilinear = the recursion =
  the atom. The elementary drop-corank bound caps at `c'<1` there.

**Unified formula (Codex Q1, decorrelated).** The full bilinear `‖Γ Q_b‖²` has
`RLCT = ½·Φ(a,b,q)`, `Φ(a,b,q) = min_{0≤r≤min(b,q)} { a·r + (b−r)(q−r) }` (min over ALL rank strata).
The top stratum `r=b−1` gives `a(b−1)+D`; the elementary corner leaf proves only that term. The MIN over
`r` (hence the deeper strata) is what makes it `= ½·minAdm`, and reading that min is the resolution.

---

## Chart census (`L=3..5` widths, ranks `1..5`, binding cuts, `a≥1`)

| bucket | count | status |
|---|---|---|
| Cat III (`b>q`) | **0 nontrivial** (`a=0` at every binding cut) | no corner — trivial peel (confirms cert §10) |
| Cat II, 3-width, `b=1` | 15 | **fully elementary** (free-`z` leaf, no deeper strata) |
| Cat II, 3-width, `b≥2` | 27 | top stratum elementary; **deeper `{rank≤b−2}` = atom** |
| Cat II, deeper-tail (`L≥1`) | **252** | **twisted leaf = atom** (Codex Q5 lowering) |

So the elementary "above-the-atom" part is the **3-width descent BASE** (~15 clean + 27 top-only);
**86% of corner charts are the atom.** This matches the cert's framing that 3-width is the base/template
and the general case is "the rank-flag recursion the `(S,J)` build already descends" (= task #111).

---

## The Lean-friendly route (what IS buildable) + the two build traps

**Buildable (3-width base), elementary pieces:**
1. rank-`(b−1)` normal-form cover (dominant-`(b−1)`-minor charts) — NEW module, Gaussian/Schur, bounded labor.
2. the `(a,1,D)` free bilinear leaf `‖γ‖²‖z‖²` → RLCT `½·min(a,D)` (factoring), + comparability removal of the
   `C'B₀` coupling (`Real.rpow` monotone + two-sided bound, cf. the banked bounded lemma's shape), + the
   direct-sum composition with the redChain IH.
3. (`b≥2` top stratum only) the `Γ_∥` peel.

**TRAP W1 — the banked `freedSchurLoss_inner_bounded_lt_top` is LOSSY for the corner.** Dropping the whole
corank term (`freed ≥ ‖B₀‖²`) reaches only `c' < ½·minAdm(redChain)` (`=1` for `(2,2,1)/(3,2,2)/(2,3,2)`),
**NOT** `½·minAdm(M)` (verified exactly: the `‖B₀‖²` bound estimator returns `1.00`, the true corner `→2`).
The corner MUST use the corank term. **The cert's identification (line 342) of the `Γ_∥` Morse with the
Regime-B bounded lemma is WRONG:** the `Γ_∥` peel is the corank **ATOM** (`corankBlock_morsePeel_lt_top`,
Regime-A shape) applied to the **full-rank `(b−1)×q` sub-block with a UNIT Gram** — and the banked atom's
`hG : (Q_b Q_bᵀ).PosDef` FAILS on the corner (`Q_b` has rank `b−1 < b`). So the `Γ_∥` peel needs a **NEW
sub-block variant** of the atom (peel `a×(b−1)` of `Γ` against the full-rank `(b−1)`-block), not the banked
full-`Q_b` atom and not the bounded lemma.

**TRAP W2 — the free-`z` `(a,1,D)` leaf OVERESTIMATES for deeper tails.** Do not use it for `L≥1` (Codex Q5:
the twist lowers `min(a,D) → min(a,m,D)`). Deeper-tail corners need the twist-aware `(S,J)` resolution.

---

## Codex decorrelated read (my conclusion withheld — quoted)

> **Q4:** "Regime A emits the divergent weight `‖z‖^{−2}`, but the original bounded integral is still finite
> for every `c'<2`. … The determinant singularity is not a genuine obstruction below the true RLCT; it is
> created by integrating `Γ` over all of `ℝ^{ab}`. … A single leaf proves only its chart; the global base
> threshold is still the minimum over all ranks."
>
> **Q1:** `λ(f) = tq/2 + ½·Φ(a,b,q)`, `Φ = min_r{ar+(b−r)(q−r)}`; "`λ(f) = ½·codim{f=0}` … proven by the
> resolution above; it is **not** a general codimension principle."
>
> **Q5:** "`λ_twisted = ½·min(a,m,D)` … the product structure lowers the threshold exactly when
> `m < min(a,D)` … the bilinear free-row reduction **overestimates** the threshold in the twisted product case."

Fully decorrelated agreement on: the det weight being a whole-plane artifact (Regime B avoids it, finite to
the true RLCT); the coupling removed by comparability; the leaf RLCT `½·min(a,D)`; the `Φ`-min-over-ranks
structure (deeper strata); and the twist lowering the free-leaf estimate (regeneration).

---

## CLOSE

- **Firmest.** The corner does NOT over-claim (contra Cat I): it genuinely avoids the `det^{−a/2}` weight,
  needs no full Cauchy–Binet, has no `a<1` gap. The `(a,1,D)` leaf **closes elementarily ONLY at the 3-width
  base** (`b=1` + the top stratum, `Q_b`/`z` free) — coupling removed by comparability, RLCT `= ½·minAdm` by
  direct-sum. Exact + decorrelated-confirmed.
- **The wall (folds into the atom).** In general the leaf **REGENERATES**: (i) `Q_b = Y·A_{≥2}` a product ⟹
  the twisted leaf `min(a,m,D)` < free `min(a,D)` (Codex Q5) — 252/294 (86%) of corner charts; (ii) `b≥2`
  deeper strata `{rank≤b−2}` recurse (`frobSq(ΓQ_b)` is itself a Cat-II sub-DLN). Both = the `(S,J)`
  product-rank-flag atom (task #111), NOT a naive arity-IH. This is the cert's own honestly-scoped Aoyagi §5
  import; my finding is that it is the **majority** of the corner, not a rare tail.
- **Most likely to break / watch.** Trap W1 (the lossy bounded lemma + the missing unit-Gram sub-block atom
  variant) and trap W2 (the free-leaf overestimate for deeper tails). A formaliser that closes the corner
  via `freedSchurLoss_inner_bounded_lt_top` caps at `c'<½·minAdm(redChain)` and the `½·minAdm(M)` headline
  silently fails.
- **Next.** (1) Cat II/III formaliser: build ONLY the 3-width base (the `b=1` free-`z` leaf + the `b≥2` top
  stratum) as the descent's BASE, with the two traps front-and-centre; the unit-Gram sub-block atom variant
  is the one new analytic module. (2) Everything deeper-tail routes to the operator-gated `(S,J)` atom —
  gate the Cat II/III general corner behind task #111, do not attempt it as "elementary above the atom."
