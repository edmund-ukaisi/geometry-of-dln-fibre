# Cert D4 — the exhaustiveness hunt (SPEC; the gate before coverage is established) (covdesign-t02)

**Seat:** pen-and-paper. **Date:** 2026-07-17. **Status:** DESIGN SPEC — the full hunt is specified, NOT run
(per the commission). One tier prototyped (`scripts/d4_valuation_hunt_proto.py`) to validate well-posedness.
**Target:** the coverage `≥`-leg claim "no untracked exceptional divisor has ratio `< ½ minAdm(M)`", i.e.
`lct(⟨prod C⟩) ≥ ½ minAdm(M)` (the finiteness / `hbox` direction). NO `rlct=c*`.

---

## 0. What the hunt is, and why it is a real gate (not a rubber stamp)

The tracked family gives `lct ≤ ½ minAdm` (a specific log resolution's min divisor ratio). Finiteness needs
the reverse: NO divisor — tracked or not — has ratio below `½ minAdm`. A single untracked divisor with ratio
`< ½ minAdm` REFUTES coverage (the box integral would diverge on `[ratio, ½ minAdm)`). The hunt is a
**decorrelated kill-search** for such a divisor; surviving it is the GATE the architect/formaliser must clear
before "coverage established." (The closing ARGUMENT is Codex Q3: every exceptional prime of a composite
blow-up is the strict transform of one created at a definite `(S,J)` stage, so the ledger tracks them all —
the hunt checks that argument has no gap.)

## 1. The load-bearing finding: original-coordinate monomial valuations are VACUOUS

Prototype (`scripts/d4_valuation_hunt_proto.py`, EXACT rational): the minimum over monomial valuations `w`
of the ORIGINAL entries of `R(w) = (Σw)/ord_w(⟨prod C⟩)` is **`4`** for both `(2,2,2)` and `(2,2,3)` —
far ABOVE `½ minAdm = 3/2, 2`. So no original-coordinate monomial valuation undershoots, but **the
lct-achieving valuation is NON-MONOMIAL** in the original coordinates: it lives in Aoyagi's incidence chart
(`A = α[[1,a],[b, ab+δ]]` etc. — variables MIXED by a coordinate change). **Consequence for the hunt design:
a hunt restricted to original-coordinate monomial valuations passes vacuously and probes nothing** — the
danger lives after the incidence coordinate changes. The hunt MUST search coordinate-changed valuations.
(This is the classic "check the setup, not just the pass" — a green original-monomial hunt is meaningless.)

## 2. The candidate divisor family (three tiers)

**Tier A — original-coordinate monomial valuations (cheap PRE-FILTER, NOT the gate).** Enumerate small
integer weight vectors `w` on the entries; compute `R(w)`; confirm `≥ ½ minAdm`. Fast, exact. Documented as
vacuous (§1) — kept only to catch a gross error, never as evidence.

**Tier B — alternative-resolution search (THE GATE).** The genuine untracked-divisor family = exceptional
divisors of resolutions using centers OTHER than the rank-profile strata. For each instance, take a bounded
family of ALTERNATIVE first centers:
  (B1) coordinate-subspace centers `{c^{(s)}_{ij} = 0 : (s,ij) ∈ S}` for subsets `S` (blowing up individual
       entries / sub-blocks that are NOT the rank strata);
  (B2) incidence loci with ALTERNATIVE pivot choices (different `(i,k)` normalised first) — tests that the
       ratio is pivot-independent, i.e. permutation-invariance of the divisor ratios (`MinAdmPermInvariance`
       is the banked shadow);
  (B3) WEIGHTED-homogeneous centers: blow up with weight vector `a ∈ ℕ^n` (`x_i ↦ x_i^{a_i}·(chart)`), for a
       bounded set of `a` (the most likely source of an untracked smaller ratio — a non-uniform weight can
       create a divisor the uniform tree misses);
  (B4) alternative 1(1) exponent-MERGE orders (different orders of absorbing `u`-factors in the corank-2
       inner recursion).
For each candidate: perform the EXACT coordinate change (symbolic, sympy / hand-derived per the Cases),
recurse to normal crossings, read every leaf divisor's ratio `(ord Jac + 1)/ord F` by the Newton-LP, and
confirm `min over leaves ≥ ½ minAdm`. A candidate whose min is `< ½ minAdm` KILLS coverage.

**Tier C — tracked-leaf completeness (CONFIRM the tracked family is a genuine log resolution).** For each
tracked leaf (rank profile `t`), verify its ideal is a monomial NC complete intersection in the chart
coordinates and its Newton-LP lct `= ½ Mval(t)`, so `min over tracked leaves = ½ minAdm` EXACTLY. (The
first-layer strata are already done — `scripts/d2_reduction_census.py`, Newton-LP == closed form on
`(2,2,2)/(2,2,3)/(3,3,4)/(3,2,3)`; extend to the full `(S,J)` tree.) If a "leaf" is NOT NC (residual
singularity), an untracked divisor lurks below it — a Tier-B target.

## 3. Instances (in priority order) and the exact computation

- `(2,2,2)` — full tree, the base case; 3 tracked leaves, ratios `{3/2, 2}`.
- `(2,2,1)` — corank-2 conflation kill (the sharp sharing witness, cert-d3 Check 2A); `½minAdm = 1`.
- `(3,3,4)` — the binding corank-2 `Δ`-block (`t=(1,0)`, `½minAdm = 4`); the independentise kill (Check 2B).
- `(2,2,3)` — non-square middle, `½minAdm = 2`.
- `(2,2,2,2)` — `L=3`, the FIRST deep-factor SHARING (top and coupled residual share `C^{(3)}`); the hunt
  must exercise coordinate-changed valuations on a shared deep factor (verify-r1-light-recursion's open leg).
- `(2,3,2,2)` — `L=3` non-square, cross-check.

Exact computation throughout: Newton-polytope LP over the (coordinate-changed) leaf-ideal exponent vectors
(`battery-drafts/_rlct.py`, rational vertex enum ≤ 9 vars, scipy-`highs` float cross-check above that — the
LP optimum is rational, so the float value is confirmed against the closed form). Coordinate changes:
symbolic (sympy) or the hand-derived incidence charts; NO floating rank, NO Monte-Carlo verdict.

## 4. What a hit means / what surviving means

- **HIT** (some candidate divisor ratio `< ½ minAdm`): coverage is FALSE as stated — either the tracked
  family misses a chart (cover incomplete) or the exponent ledger is wrong. Kills the `coverage-theorem`
  node; forces a re-scope (the paper's assertion would be wrong, or our transcription of the Cases is).
- **SURVIVE** (all candidates `≥ ½ minAdm`, tracked leaves NC with `min = ½ minAdm`): coverage's `≥`-leg is
  corroborated on the instances — necessary evidence, and combined with Codex-Q3's "every exceptional is
  created at a definite stage" argument, the gate is cleared for the formaliser to build the atlas.

## 5. Firmest / most likely to break / next

- **Firmest:** the hunt is well-posed and its cheap tier is vacuous (documented) — the gate is Tier B
  (coordinate-changed / weighted-center valuations), not the naive monomial hunt.
- **Most likely to surface a problem:** Tier B3 (weighted blow-ups) on `(3,3,4)`/`(2,2,2,2)` — a non-uniform
  weight vector interacting with the shared deep factor is where an untracked smaller-ratio divisor, if any
  exists, would appear. This is exactly the corank-≥2 sharing regime the whole engine is built to handle, so
  it is also where a transcription error would bite.
- **Next (to run the gate):** implement Tier C over the full `(2,2,2)` tree (extend the first-layer census),
  then Tier B3 weighted-center search on `(2,2,1)`/`(3,3,4)`; hand the survive/hit verdict to the controller
  BEFORE the coverage tide starts. The exhaustiveness ARGUMENT (Codex Q3, per-blow-up ledger induction) is
  the proof; the hunt is its decorrelated stress-test.
