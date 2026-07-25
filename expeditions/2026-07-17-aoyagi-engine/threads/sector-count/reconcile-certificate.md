# θ(3,3,4) + valid-covering-atlas reconciliation (sector-count #144)

Pen-and-paper `sector-count` (= pnp-fan re-charged; session ee61de1e), 2026-07-25. Decorrelated
exact-algebra + own Codex (`codex/reconcile-{prompt,answer}.md`), NO Lean. The central cover-route
decider: reconcile the four measurements + decide the valid-covering atlas. Verified on the atom defs
(`Corank2GWrapDecomp.lean`) and the CTheta engine, not on a summary.

## HEADLINE VERDICT

1. **θ(3,3,4) = 1** (top-dim components, zero-fibre r=0), with C = 8 = minAdm, RLCT = 4. [COMPUTED, two
   consistent facts: `C_theta([3,3,4],0)` = (C=8, θ=1); C=8 matches minAdm.] θ counts COMPONENTS, not
   charts — it gives NO atlas-size prediction (a single irreducible component still needs many charts).
   So "|valid| ≈ θ" is the wrong paper-faithfulness test.

2. **The 128 invalid leaves are FIXED-SHEAR DRIFT, not overproduction.** They are exactly the sigmaPiv
   pivots ∈ {4,5,6,7} = the coords `shearH` WRITES. Because `sigmaPiv` (= β) is post-composed AFTER
   `shearH`, `det D gWrap_p = F_p(u)^{|S|−1}·det DF`, a coordinate monomial only if the shear FIXES the
   pivot. This is exactly my earlier fan-certificate §1.4 finding (L1/L3 coupled: the shear must be fanned
   with the pivot), now reproduced exactly (my sympy model + Codex, decorrelated).

3. **NEITHER the 160 (normal-crossings) NOR the 196 (distinct-pivot) valid subset COVERS a neighbourhood
   of the origin.** Route (a) [all 288] is dead (128 invalid); route (b) [prune-to-valid] is ALSO dead as
   a cover. So the clean "prune-to-valid + it covers" route does not exist. [FACT — decorrelated: exact
   witness + Codex Q2 + my probe.]

4. **The valid-covering atlas is NEITHER 160 nor 196.** It is either (A) the (pivot, pivot-adapted-shear)
   PAIR fan — 288 chart SLOTS with the 128 bad maps replaced by shears that fix their pivots (the
   directions are needed, the fixed shear is wrong); or (B) the TRANSFORMED-CENTER resolution — where the
   genuine blow-up centers transform, the admissible pivots are restricted (dissolving both the shear-slot
   invalidity and the coinciding-pivot spuriousness), and the atlas is smaller and all-valid by
   construction. Deciding between (A)/(B) and computing (B)'s size needs the explicit branch tree +
   transformed-center ideals + the pulled-back loss ideal — the missing datum, the route lane's object.

## Reconciling the four measurements (they measure different things)

The corank-2 route works with the SPECIFIC gWrap chart `gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1`
(atoms verified in `Corank2GWrapDecomp.lean`). The 288-fan fans the three blow-up pivots:
`bbA1 ∈ {1,5,6,7}` (4) × `bbA0 ∈ {0..7}` (8) × `sigmaPiv ∈ {0..7,20}` (9) = 288.

| measurement | value | what it is | covers a nbhd of 0? |
|---|---|---|---|
| **θ(3,3,4)** | **1** | # top-dim irreducible components of the zero-fibre (C=8, RLCT=4) | N/A — a component count, not charts |
| **288** | 4·8·9 | the naive Cartesian pivot-fan of gWrap, FIXED shear | YES (set-cover; decomp-5b banked) but 128 charts are non-normal-crossings |
| **160** | 5·8·4 | normal-crossings subset = sigmaPiv pivot ∈ {0,1,2,3,20} (shear-COMPATIBLE) | **NO** (Q2: shear-slot cone escapes) |
| **196** | 288−92 | distinct-pivot (clean binding, no exponent stacking) | **NO** (coinciding charts needed for cover; Q3 witness `t·e_q`) |
| **25** | — | transport K-orbits (equivalence classes for building charts by transport) | N/A — a bookkeeping partition |

The normal-crossings criterion (160, by the OUTER sigmaPiv pivot) and the distinct-pivot criterion (196,
by pivot-coincidence across levels) are DIFFERENT, near-orthogonal partitions; their intersection is
still smaller and STILL does not cover.

## Exact evidence (decorrelated, reproducible)

Model: `gwrap_fan_model.py` (my own sympy transcription of the atoms). Reproduces decomp-5b exactly.

- **(a) monomial/polynomial split (my §1.4, exact):** `det D gWrap` vs sigmaPiv pivot p1 (p3=1,p2=0):
  - p1 ∈ {20,0,1,2,3}: coordinate monomial `−u0⁷·u1³·u_{·}⁸` (VALID). 5 values.
  - p1 ∈ {4,5,6,7}: polynomial factor, e.g. p1=4 → `−u0⁷·u1³·(u0·u1 + u8·u10)⁸` (INVALID). 4 values.
  - The polynomial factor is `h_{p1}^8` where `h_{p1}` = the shear-WRITTEN coord. Zero-without-coordinate-
    vanishing witness (Codex): `u0=u1=u8=ε, u10=−ε` ⟹ `(u0 u1 + u8 u10) = 0` with no coord zero — a
    coordinate monomial cannot do that. So the 128 are genuinely non-normal-crossings.

- **(b) coinciding pivots STACK but stay monomial:** p2==p3 (both=1) → `−u1¹⁰·u20⁸` (exponent 7+3=10);
  (both=5) → `−u20⁸·u5¹⁰`. These are VALID (coordinate monomial), but the stacked binding exponent (10,
  or with sigmaPiv up to 16) is where cruxB's "binding ∉ TE={8,9,12}" risk sits.

- **(c) coverage FAILS for the valid subset [DECISIVE, FACT]:** the surviving charts (sigmaPiv pivot ∈
  V={0,1,2,3,20}) have image ⊆ `{max_{w∈W}|x_w| ≤ C·max_{v∈V}|x_v|}` (W={4,5,6,7}), so the open cone
  `max_{w∈W}|x_w| > C·max_{v∈V}|x_v|` escapes EVERY valid chart, positive measure in every ball. Witness
  `x = t·e_4`: reached only by the invalid p=4 chart; in every valid p∈V chart, `x_p=0` forces the whole
  outer center (incl. coord 4) to vanish, contradicting `x_4=t`. My earlier "shear-slot bounded by M·x_20
  ⟹ overlap covers" was WRONG (self-caught + Codex): that bound is a property of points ALREADY in the
  pivot-20 chart; it cannot establish membership. `x_4/x_20 = 1/y_20 → ∞` as `y_20→0`. Scaling does not
  help — the escape cone is scale-invariant and meets every ball; homogeneity LOCALISES the obstruction to
  0, it does not remove it. (Whether `t·e_4` is in the zero-fibre needs the loss formula; the coverage
  FAILURE does not.)

- **(d) coinciding charts are NEEDED, not redundant [FACT, Codex Q3]:** `t·e_q` lies in the repeated-pivot
  chart but in NO distinct-pivot two-level chart (if outer pivot ≠ q, `x_q=0`; if outer=q and inner≠q,
  `x_q=0` again). So the 92 coinciding charts cannot be dropped as redundant. (Indicative: 50% of ball
  directions have `argmax{0..7} = argmax{1,5,6,7}`, i.e. genuinely route to a coinciding chart.)

## The two escapes the controller named

- **Escape (i) — coinciding-leaf dominant monomial ∈ TE?** UNDECIDED without the pulled-back loss ideal.
  The Jacobian exponent stacks (10; naive numerator 11), but the BINDING is set by the loss's dominant
  IDEAL monomial, not the Jacobian. The divisor `u_q` may be absent from the dominant monomial, or another
  axis may bind. `{8,9,12}` cannot decide it from the Jacobian alone. MISSING DATUM: the pulled-back loss
  ideal on a coinciding leaf. (The route lane holds `hideal`; this is a targeted computation there.)

- **Escape (ii) — do the 196 (or 160) cover alone?** NO (§c above, FACT). The shear-slot-dominant cone
  escapes, positive measure, scale-invariant. So the coverage cannot be recovered by pruning; it needs
  the pivot-adapted normalizations (A) or the transformed-center resolution (B).

## Structure & ideas observed

- This is the corank-2 concrete instance of my earlier fan-certificate §1.4 finding: **the pivot fan and
  the shear/normalization are COUPLED.** A single fixed shear cannot monomialise all fanned pivots; the
  shear-written pivots {4,5,6,7} give non-monomial (invalid) charts, and those directions are needed for
  the cover, so the shear MUST be fanned with the pivot (the (pivot, adapted-normalization) pair). The
  "N_p" normalization family (the landed recoord half) is presumably meant to be this per-pivot
  normalization — the open question is whether it fixes each fanned pivot (adapts to it), or is a single
  fixed shear (drift).

- **The transformed-center reading (Codex Q3, most likely the paper-faithful picture):** a genuine
  resolution's centers TRANSFORM under the preceding blow-ups; the pivot choices are NOT an independent
  Cartesian product. The shear-slot and coinciding branches are plausibly Cartesian-fan ARTIFACTS (in a
  q-chart with q in the second center, the strict transform of the second center is empty ⟹ no second
  blow-up there ⟹ the first-level q-chart already covers). This aligns with my case-11 adjudication
  (the fan should be LEDGER-CORNER-PRESERVING, not a naive Cartesian fan) — the general version is
  "transformed-center-admissible pivots only." If so, the genuine atlas is smaller and all-valid by
  construction, and it covers by properness. To confirm/compute: the explicit branch tree + transformed
  center ideals.

- **A candidate cheap fix worth the route lane's check:** if the construction applied `shearH` OUTERMOST
  (g = shearH ∘ sigmaPiv ∘ …) instead of `sigmaPiv` outermost, then sigmaPiv acts on un-sheared coords —
  monomial for ALL 9 pivots — and the outer shear (a global bijection) preserves both coverage and inner
  monomiality. This would make the full fan valid. Whether the Schur-clearing is geometrically valid in
  that order (the shear cancels terms the blow-ups create, so order may be forced) is the route lane's
  call. Flagged as a Speculation.

## Route recommendation + firmest / most-likely-to-break / next

- **Route:** NOT (a) [288 fixed-shear] and NOT (b) [prune-to-160/196] — both fail to cover. The route is
  **(A) fan the (pivot, pivot-adapted-normalization) pair** (retain the 288 direction-slots, adapt the
  128 bad shears) OR **(B) the transformed-center resolution** (admissible-pivot-only, smaller, all-valid
  by construction). (B) is the more paper-faithful and dissolves BOTH the shear-slot invalidity and the
  coinciding-pivot ∉TE risk; (A) is the more mechanical repair of the current construction.

- **Firmest [FACT]:** θ=1 (C=8, RLCT=4); the 128 invalid = shear-written-pivot fixed-shear drift; the 160
  and 196 valid subsets do NOT cover (scale-invariant shear-slot escape cone, witness `t·e_4`); coinciding
  charts are needed (witness `t·e_q`), not redundant.

- **Most likely to break the clean framing:** the assumption that the pivots fan as an independent
  Cartesian product with one shear. They do not — the shear (and, under transformed centers, the
  admissible pivot set) is pivot-dependent. This is the same L1/L3 coupling my fan certificate flagged.

- **Next (the decisive missing data, route lane + decomp-5b):** (1) the transformed-center ideals — are
  the shear-slot/coinciding branches genuine affine charts or Cartesian-fan artifacts? (decides (A) vs
  (B)); (2) the pulled-back loss ideal on a coinciding leaf — does the binding land in {8,9,12}? (escape
  i); (3) whether the N_p normalization family fixes each fanned pivot (adapts) or is a single fixed shear
  (if the latter, it is drift and route (A) requires adapting it). decomp-5b's parallel overlap check
  should now come back NEGATIVE (the valid subset does not cover) — consistent with §c.

---

## ADDENDUM — reconciling #145 (decomp-5b "100% covers" vs my "escape cone"): BOTH RIGHT, box-size regime

decomp-5b's MC inverts ball(0,1) targets into `dom = closedBall(0, 903)` and reports the valid charts
cover at 100%. My exact analysis says the valid subset leaves an escape cone. **These are consistent —
the disagreement is the huge box (hypothesis (b), confirmed exactly).**

A valid sigmaPiv chart (pivot p ∈ V={0,1,2,3,20}) with source-box radius R covers `x` only if
`|x_j| ≤ R·|x_p|` for all `j` in the center {0..7,20} — i.e. it tolerates a shear-slot/other-coord ratio
up to R. With R = 903 that tolerance is enormous, so ONLY the cone `{max_{w∈W}|x_w| > 903·max_{v∈V}|x_v|}`
(W={4,5,6,7}) escapes. That cone is scale-invariant with solid-angle fraction `~(1/903)^{|V|}` —
**0 hits in 2,000,000 MC samples** (`reconcile_box.py`), so a finite-sample MC NEVER lands in it and
reports a false 100%. But the cone is NON-EMPTY and positive-measure for ANY finite R (exact witness
`x = ½·e_4 + 10⁻⁵·e_V`: ratio `x_4/x_v = 50000 > 903`, covered ONLY by the invalid pivot-4 chart;
`covered-by-VALID = False`, verified). As R→∞ the cone's solid angle → 0 but never vanishes.

**Reconciliation verdict.** The valid subset does NOT cover a full neighbourhood of 0 for ANY finite box
(FACT — scale-invariant escape cone). decomp-5b's 100% is an MC false-negative masked by the 903-box's
huge ratio tolerance; it is NOT a genuine bounded-sector blow-up cover, it is "trivial coverage up to a
tiny escape cone the box tolerates." My (and the earlier column-vs-mixed) escape stands: the
shear-slot-/transversal-dominant directions genuinely leave every valid chart.

**Does the escape cone MATTER for the RLCT? — the one remaining datum.** A resolution need only dominate
the loss on a neighbourhood of the SINGULAR locus (loss = 0); a region where the loss is regular
(bounded away from 0) needs no chart. So route (B) survives IFF the escape cone
`{max_W|x_w| > C·max_V|x_v|}` does NOT meet the fibre/singular locus (then it is loss-regular, droppable).
This is the SAME missing datum as escape (i): the pulled-back loss on the escape cone. Note the box size
is IRRELEVANT to the RLCT per chart (monomial exponents are box-independent); it only inflates the
apparent coverage.

## ROUTE VERDICT (#144 + #145 together)

- **Route (a) [all 288, fixed shear]:** DEAD (128 non-normal-crossings charts).
- **Route (b)/(B) [prune to the 160/196 valid subset, or the K-orbit column charts]:** DEAD as a
  standalone COVER — the valid subset does not cover a neighbourhood for any finite box (scale-invariant
  escape cone; decomp-5b's 100% is the 903-box MC artifact). It could be RESCUED only by a loss-regularity
  argument on the escape cone (needs the loss).
- **Route (A) [full 288 slots, pivot-ADAPTED normalizations]:** live — replace the 128 bad fixed-shear
  maps with per-pivot shears that fix their pivots (the (pivot, normalization) pair fan; my fan-cert §1.4).
  Cost: re-derive the hideal per adapted chart.
- **Route (C) [θ=1 value-from-bounds, #109+#110+#111]:** STRONGLY RECOMMENDED. The RLCT lower bound
  `rlctAt ≥ ½·min Mval` is LANDED (#109); with a single minimizing-chart upper bound (#110) and the wire
  (#111), `2·rlct = cCodim` follows WITHOUT the full covering atlas. Given the coverage is genuinely hard
  (valid subset doesn't cover; θ=1 means one component, so the value is set by the one minimizing branch),
  bypassing the atlas is the pragmatic and paper-faithful route — the coverage difficulty is itself the
  argument FOR route (C).

**Recommendation to the elder+navigator council:** route (B) [K-orbit transport as a standalone cover] is
dead; pursue route (C) [value-from-bounds, #111] as primary (bypasses the atlas), with route (A)
[pivot-adapted-normalization full fan] as the fallback if a genuine covering atlas is required. The
transformed-center question (are the shear-slot/coinciding branches Cartesian-fan artifacts?) + the
escape-cone loss-regularity are the two data that would refine (A) vs a smaller genuine atlas; both need
the pulled-back loss ideal / branch tree (route lane).
