# R1 hfin — the UPPER-bound atom adjudication (resolution-atlas completeness, corank-sensitive)

**Seat:** `pen-and-paper` (witness; obstruction). **Date:** 2026-06-24.
**Gate:** the `cover_le` analytic atom `hfin` of `routeMLayerCover_of_atoms`
(`RouteMLayerCover.lean:180`): `∀ c', (∑_i ∫_{unitBox} monomialIntegrand(layerD/K/H i, c') < ⊤) →
∫_{routeMBaseNbhd} |routeMCore M|^{−c'} < ⊤` — the UPPER bound `rlctAtOn ≥ ½·minAdm` (below the
achiever threshold the actual integral is finite).
**Constraint:** proven-from-scratch, S2 (`monomial_rlct`) ONLY — the cited Aoyagi/Watanabe analytic
bound is NOT allowed.
**Method:** exact sympy (determinantal-variety structure, Newton-polyhedron weights, the `φ_M` unit
vanishing) + the Lean architecture (`Case222CoverGETail`, `RouteMState`, `ResolutionAtlas`,
`RouteMLayerSplit`) + one decorrelated `local-codex-consult` (gpt-5.x xhigh, conclusion withheld).
Scripts `scripts/*.py`; Codex `codex/hfin-{prompt,answer}.md`.

---

## VERDICT: hfin is an **OBSTRUCTION from the combinatorial layer atlas alone**; **REACHABLE
## from scratch (S2-only) only via the FULL recursive coupled resolution** — corank-sensitive, a
## substantially larger build than hdiv. NOT a headline wall, but the genuine R1 long pole.

> The `routeLayerAtlas` is a COMBINATORIAL leaf family `(ι, d, k, h)` carrying NO geometric charts
> (`IsResolutionAtlas` has only `threshold_ge` + `achiever`, both numerical). Its hfin hypothesis
> ("leaf-sum finite") correctly extracts `c' < ½·minAdm` — but the CONCLUSION (`∫|F|^{−c'} < ⊤`) is a
> GEOMETRIC finiteness that the leaf data cannot supply. Discharging it needs genuine charts COVERING
> `routeMBaseNbhd` up to null with a per-chart UPPER c-o-v `∫_chart |F|^{−c'} ≤ C·(leaf model)`, which
> for the corank-≥2 binding strata requires the FULL coupled/iterated resolution (the deeper sub-charts
> on `{unit = 0}`), NOT a single divisor. This is the exact `hfin`-is-corank-sensitive finding of
> thread 22, now pinned to its mechanism + characterised.

---

## 1. The architecture (what hfin actually demands) — read off the Lean

- `IsResolutionAtlas M ι d k h` (`ResolutionAtlas.lean:131`) is a **Prop with two NUMERICAL fields**:
  `threshold_ge` (every leaf threshold `≥ ½·minAdm`) and `achiever` (some leaf `= ½·minAdm`). **No chart
  maps, no cover claim, no surjectivity onto the base** (its own docstring: "(S-min) ... strictly weaker
  than full surjectivity onto `Adm M`"). So the atlas supplies the VALUE `⨅ monomialThreshold = ½·minAdm`,
  nothing measure-theoretic about the loss.
- Each `routeLayerAtlas` leaf is a descent path carrying a **SINGLE divisor** `foldDivisors [Mval(M,T)]`
  = `(d=1, k=[1], h=[Mval−1])` (`RouteMLayerSplit.lean:539`, the additive single-divisor reconciliation).
  So the leaf MODEL integral is **1-dimensional**: `∫₀¹ |y|^{Mval−1−2c'} dy`, finite iff `c' < Mval/2`.
  The leaf-sum is finite iff `c' < ½·minAdm` (`scripts/leaf_data.py`, exact). **No threshold-only
  tension**: the leaves carry the COUPLED total `Mval` (= 8 for (3,3,4)), so `threshold_ge` is genuinely
  true; the "threshold-only computes 3" from `verify-r1-diagb-334` was a DIFFERENT (rejected) per-row-
  multiplicity model — reconciled (Codex §2 + the Lean def).
- The hfin atom's conclusion `∫_{routeMBaseNbhd} |routeMCore|^{−c'} < ⊤` is the genuine geometric
  finiteness. The (2,2,2) template (`Case222CoverGETail.myF222_threshold_lt_top'`) proves it NOT by the
  leaf cover but by a **recursive resolution `recStep`** summing over ALL four A-pivot cells (`p=0,1,2,3`
  — every rank stratum), each chart bounded separately. The leaf data only extracts `c' < ½·minAdm`; the
  finiteness is the recursive cover. **THIS is what general hfin needs.**

## 2. The obstruction (exact): the per-chart UPPER bound fails on corank-≥2 strata

The per-chart upper bound needs, on each chart `φ_i`, `F∘φ_i ≥ c₀·(monomial)²` with the unit bounded
BELOW on the WHOLE chart (so `|F|^{−c'} ≤ C·(monomial)^{−2c'}` — a NORMAL-CROSSING presentation). This
is the OPPOSITE direction from hdiv (which needed `F ≤ C·(monomial)²`, unit bounded ABOVE on a SLICE).

**The #135 `φ_M` chart does NOT extend to this** (`scripts/hfin_V_vanishing.py`, exact): the (3,3,4)
chart's unit `V = Uval334` **vanishes on a positive-dimensional sublocus** `{a=0, c=0, Δ=0}` (S, τ free)
INSIDE the chart box. There `F∘φ = u²·V` vanishes faster than `u²`, so the single-divisor `u²` model
does NOT upper-bound `|F|^{−c'}`. `{V=0}` is the DEEPER corank stratum (rank Δ drops further) — `φ_M`
resolves the GENERIC (top) stratum but not this sub-stratum. hdiv was immune (it used `V ≥ c₀` on a
slice AVOIDING `{V=0}`); hfin must cover `{V=0}` too, recursively.

**The corank-≥2 binding core is determinantal, not single-divisor** (`scripts/hfin_obstruction_exact.py`,
exact): for (3,3,4) the binding stratum's core is `‖Δ·S‖²` (the (2,2,4) matrix product, Δ a 2×2 residual,
S a 2×4 block). Its zero locus `{Δ·S = 0}` is **reducible** (`{Δ=0}` dim 8 ∪ `{S=0}` dim 4 ∪ rank-1
intermediate) and `‖Δ·S‖²` is **NOT quasi-homogeneous** under a single weight (along `Δ=diag(t,t²)` it
has mixed `t²` AND `t⁴` orders → the Newton polyhedron has multiple facets). So its log-resolution needs
SEVERAL divisors/charts — NOT the one `foldDivisors[Mval]` divisor. A single-divisor leaf is
geometrically inadequate to UPPER-bound the integral over a corank-≥2 stratum.

## 3. The characterised class (where hfin is reachable directly vs needs the coupled cover)

The per-step achiever-path corank decides reachability of a single-divisor (smooth-center) cover, but
**hfin must cover ALL strata** of `routeMBaseNbhd`, not just the achiever (`scripts/hfin_all_strata.py`):

- **REACHABLE-from-scratch with smooth (corank-≤1) sub-charts only** — `M` where EVERY admissible path
  has all per-step coranks `≤ 1`. Exactly the cases with no corank-≥2 drop anywhere: `(2,1,2)` (and the
  near-trivial widths). The recursive `recStep` cover resolves each stratum by a smooth (rank-1) pivot
  blow-up — the (2,2,2)-template machinery generalises directly.
- **Needs the FULL coupled resolution** — `M` with ANY admissible path having a corank-≥2 drop (i.e.
  some boundary with both `M₀−t ≥ 2` and `M₁−t ≥ 2`). This is **almost all `M`** with a width `≥ 3`
  (incl. all the corank-2 binding cases `(3,3,4)`, `(2,2,4)`, `(3,3,3)`, `(4,4,2,2)`, `(5,3,4)`, and even
  `(2,2,2)`/`(3,3,3,3)` whose NON-achiever strata have corank-2 drops). The corank-≥2 stratum's chart
  needs a coupled (multi-divisor `diag(b)`-style) resolution — the same machinery the refuted per-node
  `hnode` and the prior `verify-r1-diagb-334` cert identified.
  - NOTE `(2,2,2)` IS done in Lean — its corank-2 NON-achiever stratum is handled because, being
    NON-minimising (higher `Mval`, threshold `> ½·minAdm`), its integral converges more easily; the
    `recStep` p-cells bound it. So "corank-≥2 stratum exists" does NOT alone defeat hfin — what matters
    is whether the recursive cover can bound EACH stratum's integral, which for a corank-≥2 stratum needs
    its coupled resolution chart (more work, but the rate is favourable off the minimiser).

## 4. Net verdict + what closing hfin from scratch needs

**hfin is REACHABLE from scratch (S2-only) — it is NOT a headline wall — but it is the genuine R1 long
pole: a full recursive coupled resolution cover**, substantially larger than hdiv. Specifically:

- A genuine **`recStep`-style recursive cover** of `routeMBaseNbhd`: at each node, split the integral
  over the pivot-rank cells (ALL strata, as `Case222CoverGETail` does for (2,2,2)), recurse on the
  reduced core, terminating at smooth leaves. This is the `routeMLayerCover` GEOMETRY the combinatorial
  atlas only bookkeeps.
- Each corank-≥2 cell needs its **coupled `diag(b)` resolution chart** (the symbolic shared-Δ coupling),
  resolving `‖Δ·S‖²` to normal crossings — the deeper sub-charts on `{unit=0}`. The #135 `φ_M` gives the
  TOP stratum of each cell; the recursion must descend into `{V=0}`.
- The leaf `(d,k,h)` data then supplies the per-cell threshold bookkeeping (the `monomialIntegrand`
  RHS), and the per-chart upper c-o-v transfers finiteness.

**Cost:** this is the same coupled-resolution machinery as the refuted general `hnode`, but now it MUST
succeed (not optional) and over ALL cells. The #135 `φ_M` closed form is the per-cell TOP-stratum chart;
hfin additionally needs the recursive descent into the deeper corank sub-strata of each cell. So hfin =
hdiv's `φ_M` machinery + a recursion over the corank sub-stratification + a per-cell UPPER c-o-v (unit
bounded below, which needs the deeper resolution where the unit vanishes).

## 5. Levels / scope / what would change the verdict

- **Levels separate.** This is the UPPER leg (`cover_le`/`rlctAtOn ≥ ½·minAdm`). hdiv (LOWER,
  `cover_ge_div`) is closed (#135 `φ_M`). The VALUE `⨅ monomialThreshold = ½·minAdm` is PROVEN
  (`routeLayerAtlas_value`).
- **Proved (exact):** the leaf is single-divisor `foldDivisors[Mval]`, `d=1`, model finite iff
  `c' < ½·minAdm`; the (3,3,4) `φ_M` unit `Uval334` vanishes on `{a=0,c=0,Δ=0}` (positive-dim) in-chart;
  the binding `‖Δ·S‖²` is reducible + non-quasi-homogeneous (multi-facet Newton polyhedron); the
  per-path corank classification (`scripts/hfin_all_strata.py`); the (2,2,2) Lean hfin is a recursive
  `recStep` cover (4 pivot cells), NOT the single-divisor leaf.
- **Decorrelated-corroborated (Codex, xhigh):** "hfin not provable from a threshold-only leaf family;
  the per-chart bound needs actual charts + `F∘φ ≥ c·monomial²`; the threshold data is numerical, not a
  resolution; OBSTRUCTION on the corank-2 stratum; to close from scratch, upgrade to genuine coupled
  `diag(b)` charts." Codex independently flagged the same `{V=0}` mechanism and the reconciliation that
  the atlas carries the coupled (not threshold-only) codim.
- **What would change it / make hfin EASIER:** if a per-stratum DIRECT finiteness bound (à la
  `myF222_threshold_lt_top'`, a recursive `recStep` with a per-cell `F ≥ dist²`-type lower bound) can be
  pushed through without a full normal-crossing resolution — the (2,2,2) proof suggests a recursion with
  per-cell bounds may suffice rather than a global atlas. The hard cell is always the corank-≥2 one. The
  one cited route (Aoyagi/Watanabe `rlct ≥ ½·codim`) is FORBIDDEN here (S2-only) — so the recursive
  coupled cover is the only from-scratch path.
- **The one thing most likely to be the real obstruction:** the per-cell UPPER c-o-v on a corank-≥2
  cell — proving `F∘φ ≥ c₀·(monomial)²` with the unit bounded below requires the unit's vanishing locus
  `{V=0}` to itself be resolved (recursively). Whether that recursion terminates with S2-only normal-
  crossing leaves (it should — the determinantal RLCT is rational and the iterated `diag(b)` peel
  resolves it, per `verify-r1-diagb-334`) is the load-bearing build risk.

## 6. Recommendation to the controller

hfin is reachable from scratch but is the **genuine R1 long pole** — a full recursive coupled resolution
cover, much larger than hdiv's single `φ_M`. Concretely: build the `recStep` recursion (generalising
`Case222CoverGETail`), with per-cell charts = the #135 `φ_M` for the TOP stratum + the coupled `diag(b)`
sub-charts (recursion into `{V=0}`) for the corank-≥2 cells, and a per-cell UPPER c-o-v. The hdiv `φ_M`
closed form is reused as the per-cell top chart. I'd estimate this as the largest remaining R1 build;
the alternative (cite `rlct ≥ ½·codim`) is forbidden by the S2-only constraint. NOT a wall — a precise,
large, recursive construction. Suggested first formalisation: lift `Case222CoverGETail`'s `recStep`
finiteness to a general-M recursion skeleton, then plug per-cell charts (smooth cells first, corank-≥2
cells via the coupled resolution).
