# R1 cover-inequality (lower bound) + the complete Lean-target decomposition

- **Seat:** `pp` (design). **Read-only; /tmp scratch; no Lean.** Task #11 (R1 lower bound + full decomp).
- **Purpose:** nail the LAST residual R1 piece — the cover-inequality / lower bound
  `rlctAt ≥ ½·min_t Mval` — and lay out R1 end-to-end so it's execution-ready when S1.1 + Fubini land.

## The upper/lower asymmetry (the structural key)

- **UPPER bound** `rlctAt ≤ ½·min_t Mval` needs only ONE chart: the binding divisor over the
  minimizing stratum (established, §8 of the design doc; L1-reuse). One chart that achieves a ratio
  bounds the RLCT above.
- **LOWER bound** `rlctAt ≥ ½·min_t Mval` needs the FULL COVER: no chart/direction of a COMPLETE
  resolution may beat the minimal stratum ratio. An *incomplete* chart family gives only an upper
  bound (fewer divisors ⇒ larger min ⇒ overestimate). So the lower bound is where completeness bites.

## SUBTLETY FLAGGED NOW (before execution) — the naive codim bound is FALSE

A tempting shortcut — "`rlctAt(sum of squares) ≥ ½·codim{F=0}` directly" — is **FALSE**
(`/tmp/r1_direct_lower.py`). Counterexample: `f = xᵏ`, `k ≥ 2`: `Z = {x=0}` codim 1, `½·codim = 1/2`,
but `rlctAt(x^{2k}) = 1/(2k) < 1/2`. High-multiplicity singularities have `rlct ≪ ½·codim`. So the
lower bound does **NOT** follow from a generic codimension bound — it needs the **regular-sequence**
structure of the strata.

**Why ours holds (the real mechanism):** each stratum `S(t)` is cut by a REGULAR SEQUENCE of
`Mval(t)` equations (the nested Schur-blocks `R_1,…,R_L`, each **multiplicity 1** — NOT `xᵏ`). For a
sum of squares of a regular sequence `g_1,…,g_c` (independent, smooth complete intersection),
`rlctAt(Σg_i²) = c/2` EXACTLY (each `g_i` contributes `1/2`, like `Σx_i²`; this is `k=1`, multiplicity
1). So the per-stratum contribution is `½·codim S(t) = ½·Mval(t)` — and the `k=1` (regular sequence,
not high multiplicity) is precisely why `rlct = ½·codim` here rather than `<`. The lower bound MUST use
this; it cannot be shortcut.

## SUBTLETY FLAGGED — `S(t)` are the components; local codim at origin = min_t Mval

(`/tmp/r1_components.py`, verified (2,2,2).) `{∏C=0} = ⋃_t S(t)⁻` (closures), each `S(t)⁻`
irreducible (determinantal-type). The origin lies in EVERY component's closure (it is the deepest
point), so `codim_{origin}{∏C=0} = min over components = min_t Mval(t)`. No "other component with
smaller codim" is missed; the strata exhaust `{∏C=0}`. The top-dimensional component is the
minimizing stratum (e.g. (2,2,2): `rank A=1`, dim 5, codim 3 = min Mval). So the LOCAL codim the
RLCT sees at the origin IS the global min — the lower bound's `min_t Mval` is the right target.

## The cover-inequality / lower-bound design

```text
rlctAt F  =  n/2 + (core's resolution min-ratio)        [Fubini-per-chart + S1.1 min-over-cover]
          =  n/2 + min over core charts i of min_j (h_{i,j}+1)/(2 k_{i,j}).
```
**Lower bound** `core min-ratio ≥ ½·min_t Mval`:
1. **Completeness/cover:** the core chart family is a COMPLETE resolution — its images cover a
   neighbourhood of `origin ∩ {core=0}`. (Pivot branches exhaust the rank-pattern stratification of
   `{∏C=0}`; off `{core=0}` the integrand is locally bounded, threshold-irrelevant.) ⟹
   `rlctAt(core) = min over ALL charts` (not just a sub-family) — the genuine RLCT, not an overestimate.
2. **Multiplicity control over all divisors** (CORRECTED — Codex, the real lower-bound obligation):
   the lower bound is NOT "every divisor ratio = ½·codim S(t')" — that is **FALSE in general** (see
   the flagged gap below). The genuine obligation is: for EVERY exceptional divisor `E` of the
   complete resolution, `h_E + 1 ≥ k_E · min_t Mval(t)` (equivalently ratio `(h_E+1)/(2k_E) ≥
   ½·min_t Mval`). This needs **vanishing-order/multiplicity control**, not just the codimension of
   the center. For OUR core it holds because the centers are **regular sequences** (multiplicity 1 ⇒
   `k_E = 1`, so ratio `= (h_E+1)/2 = ½·codim ≥ ½·min`), but this must be PROVEN per divisor, not
   assumed from codim. ⟹ `min over charts ≥ ½·min_t Mval`.
3. Combined with the UPPER (binding divisor on the min stratum achieves `½·min_t Mval`): **equality**.

So `rlctAt F = n/2 + ½·min_t Mval(t) = aoyagiLambda` (with `n/2` the regular term). ∎

## The complete R1 Lean-target decomposition (execution-ready)

`resolution_charts` (value-match, R3b, one-citation-clean), assembled from:

| # | Lean obligation | status / source |
|---|---|---|
| R1.1 | **the chart family `ι`** = pivot branches of the iterated L1 (Aoyagi affine atlas); per chart `(d_i, k_i, h_i)`, `k=1` on each exceptional divisor | construct (REUSES L1, done) |
| R1.2 | **universal divisor-ratio lemma**: smooth codim-`c` center (regular sequence, mult 1) ⇒ `core∘φ = u²·unit` (`k=1`) + `|det Dφ| = u^{c−1}·pos` (`h=c−1`), ratio `c/2` | the reusable core; new |
| R1.3 | **`codim S(t) = Mval(t)`**, the nested Schur-block residual = regular sequence of length `Mval(t)` cutting `S(t)` | thread-03 PROVEN (pen+paper); Lean obligation |
| R1.4 | **Fubini-per-chart** (smooth-block lemma): `rlctAt(Σx² + core-monomial) = n/2 + min_j (h+1)/(2k)` per chart, via radial-scaling `∫(|x|²+s)^{−c}dx = C·s^{n/2−c}` + Fubini | L2-arch card (adopted); fm-2 proves |
| R1.5 | **S1.1 min-over-cover**: `rlctAt(core) = min over charts` of chart-thresholds (down-set ∩ = min); needs the COVER (R1.6) | fm-2's S1.1 (proven, wiring) |
| R1.6 | **the COVER / completeness**: pivot branches' images cover a nbhd of `origin ∩ {core=0}` (exhaust the strata) | construct; the residual real work |
| R1.7 | **S2** (the ONE axiom): `monomialThreshold d k h = min_j (h_j+1)/(2k_j)` | cited |
| **assembly** | UPPER (R1.1+R1.2 binding divisor on min stratum, via R1.3) ≤ ; LOWER (R1.2 universal + R1.6 cover + R1.5 min) ≥ ; ⟹ `rlctAt F = n/2 + ½·min_t Mval` | the value-match |

**The split UPPER (cheap) / LOWER (residual real work):**
- UPPER = R1.1+R1.2+R1.3 (one branch, the binding divisor; L1-reuse) — cheap, mostly done in pieces.
- LOWER = R1.2-universal + R1.6-cover + R1.5-min — the residual real work. R1.6 (the cover) is the
  one that ranges over ALL branches; it is an EXHAUSTIVENESS statement (the strata partition
  `{core=0}`), an inequality over strata, NOT a per-chart exponent computation.

## What's NEW vs reused (honest accounting)

- **Reused / done:** L1 (the pivot split, R1.1), `codim S(t)=Mval` (R1.3, pen+paper proven), S1.1
  (R1.5, fm-2), Fubini-per-chart (R1.4, L2-arch adopted), S2 (R1.7, axiom).
- **New for R1 execution:** R1.2 the universal divisor-ratio lemma (smooth codim-`c` regular-seq ⇒
  `k=1,h=c−1`), and R1.6 the cover/exhaustiveness. These two are the R1-specific lift; R1.2 is a
  clean local lemma, R1.6 is the genuine residual work (the "mountain" that remains).

## Gaps flagged NOW (before execution — the controller's ask)

1. **The naive `rlct ≥ ½·codim` is FALSE — TWO counterexamples** (me + Codex, decorrelated): `xᵏ`
   (k≥2: rlct 1/(2k) < ½·codim) and **`(x²+y²)²`** (Codex: a sum of squares, Z={0} codim 2, but
   rlct = 1/2 ≠ 1 = ½·codim — the squaring doubles the vanishing order). The lower bound CANNOT come
   from codimension/stratification alone; it needs **multiplicity control**.
2. **THE MAIN GAP TO REMOVE (Codex, sharpened):** the lower bound's real obligation is per-divisor
   **`h_E + 1 ≥ k_E · min_t Mval`** for every divisor of a complete resolution — NOT "ratio =
   ½·codim of its stratum" (false; divisor ratio = `(h_E+1)/(2k_E)` depends on the F-vanishing order,
   not just the center's codim). For OUR core this holds via the **regular-sequence/multiplicity-1**
   structure (`k_E = 1`), but it must be PROVEN per divisor. This is the genuine R1 lower-bound
   difficulty — sharper than "the cover" alone. R1.2 must be the multiplicity-control lemma, not a
   codim-to-ratio shortcut.
3. **R1.6 (the cover) is also residual real work** — it ranges over all pivot branches (an
   exhaustiveness claim, `Z = ⋃_t S(t)`). Together with item 2 (multiplicity control), these are the
   two at-risk pieces for R1 execution; everything else (R1.1/R1.3/R1.4/R1.5/R1.7) is in hand.
3. **Local-vs-global codim:** verified the origin sees `min_t Mval` (it's in every component's
   closure); no smaller-codim component missed. Not a gap, but pin it in R1.6's cover argument.
4. **Properness for the cover transport** (S1.1 side): the min-over-cover needs the resolution proper
   (or the chart-cover + bounded-off-`{F=0}` argument) — shared with S1.1; confirm it's in fm-2's S1.1
   (the global blow-up is proper; single charts are not, per the earlier S1 properness note).

## NET

R1 is designed END-TO-END. UPPER bound = cheap (L1-reuse binding divisor). LOWER bound = the
universal divisor-ratio (regular-sequence `k=1`, NOT the false generic codim bound) + the cover
(R1.6, the residual real work) + S1.1 min. The full decomposition (R1.1–R1.7 + assembly) is the
execution plan; R1.2 + R1.6 are the new lifts, R1.6 the genuine remaining difficulty. Subtleties
(false codim bound; components/local codim; properness) flagged before execution, not during.
