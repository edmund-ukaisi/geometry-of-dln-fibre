<!-- CHARTER — the fixed invariant core of this expedition.
     READ THIS FIRST, every wake / every convening / every brief. Elder owns it; controller commits.
     EDIT IN PLACE, NEVER APPEND. Hard cap ~1 page. If it grows, it decays like the logs did.
     History lives in journal.md / compass.md; TRUTH lives here. Compaction distills TO this, never away.
     Checkpoint: 2026-07-27 (GENERAL-D PHASE REFRESH — distilled to the general-d surface after the
     (3,3,4) rlct=½·codim MILESTONE landed cite-free + monument-free + kernel-gated. The whole
     (3,3,4)-phase route apparatus (route-P, one-object recursion, R0–R6, W3, the F1-tripwire) is
     RETIRED into compass/journal history; the general-d surface map is the new source of truth.) -->

# Charter — aoyagi-engine

## §0  The frame (the thing that dissolves the drift)
We build **Aoyagi's resolution-of-singularities machinery as reusable mathematics at full generality** —
objects useful *outside* the headline. The `rlct = ½·codim` result is a **corollary and a test**, NOT the
objective. Steering by the headline is what produced the drift (repeatedly): it rewards cheap
re-derivation, MVP shortcuts, category-wrong charts. **Steer by the objects.**

**"Done" for an object (VERIFIED, never assumed):** (i) GENERALITY — natural/canonical at the *weakest
hypotheses that suffice*, agreed COLD (no headline); (ii) STRIKE-ABLE LEAVES — every leaf bottoms at
proof-engineering we'd bet true, else the open part is ISOLATED and NAMED a frontier; (iii) COMPLETENESS
— blueprint the *whole* object, which dissolves critical-path guessing; (iv) SOUNDNESS — name = content,
correctly quantified, a mathematician reading the STATEMENT does not wince.

**Definition of done (the destination — changing THIS is wait-for-explicit-go):** sorry-free; `#print
axioms` = `[propext, Classical.choice, Quot.sound]`; each result at the weakest hypotheses; the reusable
engine authored upstream-ready in `Core`.

## §1  The GOAL
The **general-`d` theorem**: for every DLN dimension vector `d` (`Monotone`, `0 < L`, positive widths,
nonempty fibre) at the base point `B = 0`:

> `rlctGlobal (lossDLN d 0) = ½·codimRealFibre d 0`   (ALL `d`).

Lean landing point: build a **cite-free** `RlctRealInterface d` (delete the two `cited_*_ax` axioms,
`AoyagiCited.lean`), equivalently discharge / bypass the general monument `exists_coreResolution`
(`LearningCoefficient.lean:292`, currently `sorryAx`). The payoff `rlct_lossDLN_eq_half_codimRealFibre`
(`RlctPayoff.lean:478`) composes the interface's two fields into the equality.

**`(3,3,4)` is a LANDED MILESTONE, NOT the destination.** `dln_rlct334_eq_half_codim = 4` is built in
honest Lean, **cite-free + monument-free + kernel-gated clean-three** — both halves from geometry,
`exists_coreResolution` off the cone (`synthesis.md` / `statement-cards.md`). It de-risks the MECHANISM;
it is ONE coupled `L=2` instance (`minAdm = 8`, coupled-only), not general-`d`. Do NOT read it as done.

## §2  The CRUX — the whole gap = the cite-free LOWER bound
`RlctRealInterface d` has exactly two fields. The `≤` half (`cited_watanabe_upper`) is a bounded
single-chart change-of-variables lift — **general-`d`-liftable, mechanical, NOT the crux** (Card 3).
**The whole gap is the `≥` half `cited_aoyagi_lower`: `½·codimRealFibre d 0 ≤ rlctGlobal (lossDLN d 0)`.**

Everything else is landed or mechanical (so the map is complete; the territory is the value lower bound):
- **Geometric ½·codim general-`L`** — `minAdm = cCodim` (`MinAdmCCodim.lean:315`, `1 ≤ L`) + the
  base-change transfer. `codimRealFibre d 0` is a solved computable ℕ. [Object D landed; A, C landed.]
- **Deepest-point reduction general** — `rlctGlobal (lossDLN d 0) = rlctAt (coreGen d) 0` (homogeneity +
  lower-semicontinuity).
- **The abstract lower-bound ENGINES — ALL landed general-`d`, clean-three**: the `hideal_bwd`-free /
  `exists_coreResolution`-free V-lower wire (`SandwichCover.lean:237`), the SoS/Tonelli engine (the `|Z|/2`
  binding value, `MonomialSumSqRLCT.lean:269`), the arbitrary-depth cover fold (`covers_fanOfSteps`,
  `GeneralGeoAtlas.lean`), the per-chart survivor sandwich (`SurvivorSandwich.lean`).

**General-`d` needs a ONE-SIDED cover-atlas, NOT the two-sided principal normal form** (the wire's type
carries no `hideal_bwd`; confirmed in Lean + `worked.tex:718-720`).

## §3  The HONEST HARD PART + the first-rung GO/NO-GO
**The missing content = the geometry↔ledger CORRESPONDENCE.** In the landed Lean, `buildTree`/`stepUpdate`
carry the **LEDGER ONLY** (`localSub := id`; symbolic support-propagation explicitly DEFERRED to the
`genDivExp` redesign). The **geometry** lives SEPARATELY in `MonumentAtlas.stepMapRaw`/`foldG`/
`canonNormalizationOf`. So **L1** (the per-leaf from-below `hpull` factorization `loss∘g = monomial²·SoS`)
and **L3** (its exponents/`|Z|` realize `½·minAdm`) are **NOT yet consequences of the recursion.** The
central missing theorem: the composite geometric pullback `loss∘(foldG …)` at each leaf has monomial/`|Z|`
data matching what `stepUpdate` records — proved by induction on a **STRENGTHENED coupled-`diag(b)` class
STABLE UNDER COMPOSITION** (the clause that makes "recursive divisors are good by induction" non-circular).

**`(3,3,4)` is an `L=2` LUXURY.** One incidence + one blow-up leaves a nondegenerate **Morse** residual, so
the SoS engine closes the binding leaf immediately at the top ("precisely why `L=2` works and only `L=2`",
`worked.tex:709-710`). At `L≥3` one blow-up does NOT leave Morse — one must DEPTH-RECURSE on a COUPLED core
(coupled corank-≥2 peels don't factor), and the binding value is assembled from INTERMEDIATE divisor
thresholds COMPOSED with the bottom SoS — content `(3,3,4)` exercises NOT AT ALL. **So "monument-free at
full generality" is NOT YET EARNED** — it is extrapolation from `L=2` + locally-modelled single steps.

**THE FIRST-RUNG GO/NO-GO (BEFORE committing the ~10–16-tide build).** The geometry↔ledger CORRESPONDENCE
probe on a genuine deeper instance — `(3,3,3,2,2)`, `t = (2,2,1,0)` — generated from the REAL geometry
`stepMapRaw`/`foldG`/`canonNormalizationOf` (`MonumentAtlas.lean:325,373,939`), **NOT** `stepUpdate`
(carries no geometry) and **NOT** a hand-written fed-form. A pen-and-paper / exact-algebra seat
(`witness`/`obstruction`), decorrelated Codex. Verify SIMULTANEOUSLY: the composite Jacobian monomial;
`loss∘g ≥ m²·∑_Z z²` OR its coupled unit-tail analogue `E²‖v‖²`; `m` = the SAME monomial `stepUpdate`
records; `threshold(m) ≥ ½·minAdm` AND `|Z|/2 ≥ ½·minAdm`; **the child core stays in the strengthened
coupled-`diag(b)` class.** CLEAN + child-in-class ⟹ detail-at-scale (~10–16 tides). OBSTRUCTION — a composed
pullback over-vanishes / the child leaves the class / thresholds don't compose to `½·minAdm` ⟹ general-`d`
is a MONUMENT (a new coupled-core integrability theorem repairing Aoyagi's induction); fall back to the
two-sided resolution or OBJECTS-ONLY (a charter landing, citing `cited_aoyagi_lower_ax` — operator-gated).

## §4  Standing math-warnings (tripwires — each caught a real defect)
- **from-below-not-toric** — a toric-LP / Newton-polytope / monomial-ideal reading is an UPPER bound on the
  true rlct; it does NOT certify the lower bound. Every lower-bound cert must be from-below
  (resolution / regular-sequence).
- **engine-reads-the-shape** — the chain wire collapses `∑bₖ² = b_{k₀}²·U` and reads only
  `monomialThreshold(b_{k₀})`, DISCARDING the SoS vanishing; the `|Z|/2` binding value lives ONLY in the
  SoS block. Match the RHS shape to the engine (product-shaped regular sequence → SoS/Tonelli, NOT the chain).
- **ledger-is-not-geometry** — `resRank` is hardcoded `0`; derive `bexp`/`k₀` from the ACTUAL pulled-back
  loss `K∘g = monomial²·unit`, never off the hardcoded field. (Generalises to the §3 correspondence gap.)
- **the SoS-at-bottom DEPTH risk** — `(3,3,4)`'s SoS closure is an `L=2` luxury; at `L≥3` the SoS engine
  applies only at the recursion BOTTOM, the value assembled from intermediate thresholds. The most likely
  place a gap hides → the first-rung probe targets it.
- **the pivot-cross survivor FAILS at depth** — `Pmat[0][0] = E` gives `loss ≥ E²` ONLY at `L=2`; at
  `L≥3`, `loss = ‖P·C^(3)⋯C^(L)‖²` and the deeper product can vanish while `E ≠ 0`. The true model is
  `E²‖v‖²` — certifying the unit tail IS the recursive obligation. (Corrects the retired F13
  "corank-insensitive bypass composes through depth".)
- **the geometry↔ledger correspondence is UNBUILT** — §3; the sharpest structural gap.

## §5  Durability
Read FIRST, every cycle, by every role. Elder is sole author (holds the abstract-object frame; gates
against §0–§4); controller commits. `CLAUDE.md` points here. This file is what survives log growth.
