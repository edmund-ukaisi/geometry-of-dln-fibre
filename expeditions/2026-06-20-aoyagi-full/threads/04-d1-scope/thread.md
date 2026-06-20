# Thread 04 — D1 scope: deepest-singular-point reduction (pp, read-only)

- **Seat:** `pp`. **Read-only + /tmp scratch** (`/tmp/d1_*.py`, `/tmp/codex-d1-*.md`); controller integrates.
- **Status:** scoped. D1 is a **light** rung. Reports a citation correction + an ordering constraint.

## CITATION CORRECTION (precision-critical)

The 2023 paper's "Theorem 4 [22]" = **Aoyagi 2013 (Entropy 15:3714), Theorem 2** ("Method for finding a
deepest singular point") — verbatim statement match (both page images confirmed). The 2013 paper's *own*
"Theorem 4 [11]" is a DIFFERENT result (holomorphic hyperplane-restriction `λ_{g=0}(g) ≤ λ_{f=0}(f)`,
explicitly flagged **not true over the reals**). **Cite Aoyagi 2013 Theorem 2, never "their Theorem 4."**
(Under our prove-all-but-S2 rule D1 is *proven*, not cited — this fixes which source statement we mirror.)

## Statement (Aoyagi 2013 Thm 2)

For `F₁,…,Fₘ` homogeneous in `w₁,…,wⱼ` (degrees `nᵢ`; `w_{j+1..d}` spectators) and a `C^∞` `φ` with
`φ(0,…,0,w*_{j+1},…) ≥ φ(w*)`, `φ_w` homogeneous near the deepest point:
`λ_{(0,…,0,w*_{j+1},…)}(⟨F⟩,φ) ≤ λ_{(w*₁,…,w*_d)}(⟨F⟩,φ)`.
Proof (elementary, self-contained): blow up along `{v=0, wᵢ=0}`, set `wᵢ = v·wᵢ'`; homogeneity gives
`Fᵢ(w) = v^{nᵢ}Fᵢ(w')`, so `Σ v^{2nᵢ}Fᵢ'² ≤ Σ Fᵢ'²` for `|v|<1`, then the monotonicity lemma
(`g²≤f² ⇒ λ(g²)≤λ(f²)`, our S1) gives the result.

## Lean target

```
theorem deepest_point_reduction (H r B) (hB : B.rank = r) :
  (⨅ w ∈ optimalSet H B, rlctAt (dlnLoss B) w) = rlctAt (dlnLoss B) w_deepest
```
`w_deepest` = most-degenerate fibre tuple (all partial products at minimal rank r; after the L2 split,
all reduced core blocks `C^(s)=0` at the core origin). The global learning coefficient = MIN over the
fibre of local RLCT (Watanabe/Lin); Thm 2 ⇒ deepest ≤ every other point ⇒ inf attained there.
On (2,1,2) r=0: deepest local RLCT = λ_core = 1 = ground truth ✓.

## Hypothesis fit — the REAL caveat (Codex-sharpened) + the forced ordering

The **singular-core** generators `(∏C^(s))_{ij}` ARE homogeneous (degree L, multilinear) — verified
symbolically. So Thm 2 applies to the CORE. BUT the **raw loss** `‖∏A−B‖²` with `B≠0` is NOT
homogeneous (mixed-degree generators). ⇒ **D1 must be applied to the homogeneous core, DOWNSTREAM of
L2/Thm-3 — never to the raw loss. D1 depends on L2.**
D1's genuine own obligation (state explicitly, don't gloss): the homogeneous normal form must (a) cover
all optimal strata of the fibre, and (b) place the deepest point in the specialization closure of each.
Both hold for DLN (the fibre's strata = the nested-rank strata from thread 03; the all-zero core point
is in every stratum's closure) — but PROVE it, don't assume.

## Difficulty (prove-all-but-S2)

- TRIVIAL: the scaling `Fᵢ(vw')=v^{nᵢ}Fᵢ(w')` + the `|v|<1` inequality `Σv^{2nᵢ}Fᵢ'² ≤ ΣFᵢ'²`.
- MODERATE: positive-bump/unit RLCT-invariance (φ-monotonicity is COSMETIC under a positive bump);
  dummy-variable trick (adding `v` is RLCT-neutral, via Fubini); the explicit Jacobian of `(v,w')↦(v,vw')`.
- HEAVY (shared, NOT new): the blow-up change-of-variables for `|F|^z` integrals — **this is S1**. D1 is
  NOT a resolution; it's ONE substitution + a comparison, much lighter than R1, and reuses S1's
  change-of-variables. The monotonicity lemma `g²≤f²⇒λ≤λ` is also S1 (Codex flags Lin arXiv:1003.5338
  as the clean reference for ideal-RLCT basics; under prove-all-but-S2 it's an S1 obligation, not a cite).

## Net

D1 = light rung: homogeneous scaling + monotonicity, applied to the core downstream of L2, **no new
citation beyond S2** (reuses S1's change-of-variables). Build change-of-variables invariance ONCE in S1
⇒ D1 is a short corollary. The one thing not to gloss: the (a)/(b) "covers all strata + deepest in
closure" obligation (uses thread-03's stratification). Codex (xhigh, decorrelated): STANDARD, proof
correct after the dummy-`v` Jacobian bookkeeping; the `B≠0` non-homogeneity caveat is the real check.
