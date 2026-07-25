# Obstruction catalogue — decorrelated adversarial audit of route-B (transformed-center resolution)

**Seat:** pen-and-paper OBSTRUCTION (exact algebra, no Lean). **Direction:** try to REFUTE the three
route-B claims (§1 fan-the-construction / §2 per-step cover / §3 representatives + relabeling transport).
**Method:** exact symbolic algebra (sympy, exact-rational) + one decorrelated Codex xhigh consult
(`/tmp/audit-routeB/codex-s3b-answer.md`, frame-in/hypothesis-out). Scripts in `/tmp/audit-routeB/*.py`.

**Bottom line.** No single hard *mathematical* wall (the coreGen symmetries are real, the spine is
render-bounded, the full-fan cover atom is banked). BUT the brief's **economy claim is refuted**: "resolve
representatives only; never certify a non-representative leaf from scratch; collapses the monument" is
false as stated. Transport is a per-**leaf-orbit** symmetry-reduction that reduces the leaf COUNT, not a
mechanism that removes the per-leaf general-`d` resolution or the cover. Two named coherence obligations
(node non-transitivity; cover-vs-certificate seam) sit under the "one induction, two clauses" framing and
are not discharged by anything banked. The brief's own STOP-conditions **check the wrong thing** and would
give a false-GREEN.

Severity-ranked. Each item: the exact-algebra finding, then the build implication.

---

## O1 [SERIOUS — refutes the core economy] Node non-transitivity: the matched-gauge swap moves the ancestor pivot

**Finding (exact algebra + decorrelated Codex, independently agreeing).** The family the transport lemma
`transportChart` actually consumes is the FIXED product family `coreGen = entries of A_L···A_1`, with
hypothesis `hequiv : ∀ i, coreGen_i ∘ permOf σ = coreGen_{τ i}`. The Schur residual `{Gᵢ = b·Xᵢ}` the brief
names is the WRONG family (below, O4). So the transport is legal iff the within-run relabel `σ` is a
**coreGen symmetry**. Enumerated exactly (`test_coregen_sym.py`, `test_tension.py`, `test_deep.py`):

- **matched gauge** (swap the shared/contraction index in BOTH adjacent factors — rows of `A_S` AND cols of
  `A_{S+1}`): coreGen-INVARIANT, `τ = id`. ✔ Survives Schur regauge and compounding regauges at depth
  (4-layer `A_3A_2A_1A_0`, two regauges: still invariant).
- **end permutation** (output rows `α` / input cols `β`): coreGen PERMUTED, `τ ≠ id`. ✔
- **unmatched single-layer swap** (rows of `A_S` only): NOT a symmetry (product changes). ✘
- **single-ENTRY transposition** of two pivot entries: NOT a symmetry (0/6 for the 2×2 block). ✘

So the ONLY coreGen symmetry that swaps two ROW-fan pivots `(r_a,c)↔(r_b,c)` of an intermediate layer is the
**matched-gauge swap of the shared index**, and it necessarily co-permutes the adjacent layer
(`test_orbit.py`: the shared-index gauge ALWAYS swaps `A_{S+1}` cols too).

**The obstruction (Codex-surfaced, sub-facts confirmed here).** If that shared index was BORN from an
**ancestor** blow-up (a prior node's pivot lives on it), the matched-gauge swap MOVES the ancestor pivot.
The conjugated chart is therefore a leaf under a **different parent branch**, not the missing sibling under
the fixed parent. Codex's minimal witness `d=(2,2,2)`: after resolving the first 2×2 layer,
`b=(u₁, u₁u₂)`; the `u₂`-pivot Case-1 merge yields `b=(u₁u₂, u₁u₂)`, a two-row Case-2 center; swapping its
two shared-index rows forces swapping the adjacent first-layer shared indices = moving the ancestor pivot.
Since the unmatched swap is not a symmetry and no end-perm touches a middle index, **there is NO
parent-fixing coreGen symmetry swapping the two node pivots** — the parent stabilizer is NOT transitive on
the node's pivots.

**Why the "just do it per leaf-orbit" steelman does not rescue the economy.** The full-fan cover genuinely
needs ALL pivot charts (a finite group's orbit of one cone does not cover the punctured ball; the cover is
the complete argmax fan, not a single K-orbit — `test_cover_and_bchain.py`: full-fan escapes 0/200k,
col-pin escapes 67%). The full fan spans MANY coreGen-orbits of leaves. So one must resolve one branch per
leaf-orbit **from scratch** (the general-`d` L-A/L-B/L-C spine), and identifying the orbit representatives +
proving orbit-coverage is a real bookkeeping obligation the brief's per-NODE framing omits.

**Build implication.** Do NOT commit the team expecting transport to eliminate the per-leaf resolution.
`Corank2CoreGenEquivar` (the banked (3,3,4) object) IS the matched-gauge/end construction (correct — `ρ`
appears in both A0/A1 blocks, `α,β` are the ends), so the mechanism is sound; but the general-`d` version
with the correct **per-stage** σ (end for output/input runs, matched-gauge-touching-two-layers for
intermediate runs) is unbuilt, and it does not reach the parent-stabilizer-unreachable pivots. Those need
independent resolution. The genuine build is still: general-`d` spine per leaf-orbit-rep + full-fan
structural cover + a **node-stabilizer/chart-path coherence theorem** (currently unnamed).

---

## O2 [SERIOUS/MEDIUM] Cover-vs-certificate seam: the exponent-only seam cannot certify coverage

**Finding.** The brief runs the cover on TWO different chart-sets without reconciling them:
- §2 cover: box-containment transports because a coordinate swap is an **isometry** — this works for ANY
  swap (entry-transpositions sweep the full fan), and is banked on the TREE's actual full-fan g-maps
  (`closedBall_subset_iUnion_blockBlowup_image_radius` + `covers_subset`, route-a).
- §3 certificate: `hideal` transports only for **coreGen-symmetry** swaps (matched-gauge), which are NOT
  entry-transpositions.

These are DIFFERENT sets of permutations. A pivot reachable by an isometry but not by a coreGen symmetry
gets a cover-chart with NO transportable certificate. Reconciling "cover via tree g-maps" with
"certificates via transported (conjugated) charts" requires identifying the transported chart with an
actual tree leaf — a STRUCTURAL chart-to-path map. The seam is explicitly value-support only
(`AtlasRealizesExponents` = ℕ-exponent match, "NOT a structural chart↔leaf map", next-build-render §1), and
exponent values **cannot** certify coverage: Codex's exact counterexample — blow up `0∈ℝ²`, charts
`β₁(s,t)=(s,st)`, `β₂(s,t)=(st,s)`, both Jacobian-exponent 1 (value-support `{2}`); `{β₁,β₂}` covers but
`{β₁,β₁}` has the identical exponent value-support and misses every `(0,ε)`. (Confirms §3(c): the seam is
sound only as a numerical value adapter AFTER a genuine `Resolution` — chart validity + coverage — is
supplied; it is NOT a transport/coverage seam.)

**Build implication.** The `Resolution.hcover` must be established on the ACTUAL atlas charts. Either
(A) atlas = tree full-fan g-maps → banked cover, but every chart needs an independently-proven certificate
(O1 limits transport), or (B) atlas = transported charts → need a transported-chart cover, which the
exponent-only seam does not give. §3(c)'s "value-support-only is enough" is FALSE for the cover clause; it
is enough only for the value/realization clause.

---

## O3 [MEDIUM — reframes, not refutes] Transport reduces leaf COUNT, not the per-leaf hard part

Corollary of O1. Each leaf-orbit representative still needs a from-scratch general-`d` resolution (the
L-A/L-B/L-C Schur spine). The brief's "never certify a non-representative leaf from scratch / collapses the
monument" conceals that the orbit-REPRESENTATIVES ARE certified from scratch, and the general-`d` spine
build (render-bounded, detail-at-scale per the render, but genuinely unbuilt) remains the load-bearing
labour. Transport is a symmetry reduction on top, not a collapse. Honest framing: route-B does not make the
general-`d` `hideal` monument smaller; it reduces how many leaves you pay it on.

---

## O4 [MEDIUM] The "ONE NEW LEMMA" is mis-stated (wrong family) — correctly stated it holds, but is real work

The brief: "the STAGE generator family `{Gᵢ = b·Xᵢ}` is fixed up to reindex under within-run relabeling."
Two errors:
1. **Wrong family.** `transportChart` consumes coreGen (the product entries), NOT the Schur-cleared stage
   family `{b·Xᵢ}`. The stage family is related to coreGen by UNIMODULAR polynomial cofactors (`Q,P`), which
   is not a permutation `τ` — Codex's second warning, confirmed by the ChartTransport code (F is fixed =
   coreGen). "Stage family fixed up to reindex" is the wrong object.
2. **Wrong relabel granularity.** "within-run relabeling" (a bare permutation of run indices) is unsound at
   intermediate layers: it must be the per-stage-correct permutation — END perm (`α/β`, `τ≠id`) for
   output/input runs, MATCHED gauge (`τ=id`, touching TWO adjacent layers) for intermediate runs. A uniform
   single-layer/single-entry swap fails coreGen equivariance (O1) → silently unsound (a green chart whose
   `hideal` does not actually transport).

Correctly stated — "coreGen (the product) is equivariant under the per-stage matched-gauge/end permutation
induced by a within-run index swap" — the lemma is TRUE (my tests + Codex), and its general-`d` construction
is genuine detail-at-scale, not new math. But it is not the brief's stated lemma.

---

## §1 escape-cone diagnosis is INCOMPLETE (MEDIUM)

Each transformed-center chart is individually valid (banked, pnp-chartarch: `|jacDet|` a monomial, `injOn`
off the exceptional locus, `g(0)=0`, two-sided `hideal`) — the fixed-shear error IS fixed by presenting
each branch in its own coordinates. **But the brief's claim "the escape-cone pathology does NOT recur" is
wrong about WHY.** The escape cone is a **fan-completeness (col-pin) artifact**, INDEPENDENT of the
fixed-shear error: `test_cover_and_bchain.py` shows the col-pinned atlas misses ~67% of the box (the max
entry sits in a non-pinned column), and the transformed-center presentation does nothing about that. This
matches next-build-render §9 (Codex escape at `(4,4,4)` root case-2) and the `IsRealBranch:1065` docstring
("cover uses ROW-fan charts only; the column-orbit is the #86(B) per-step-σ transport, sorried"). §1
conflates the two independent pathologies; the fix is route-a **full-fan emission** — which then feeds
directly back into O1/O2 (full fan ⇒ every pivot needs a certificate ⇒ the node-transitivity + cover-cert
problems).

---

## §3(a) equal-b centers — NO obstruction (holds general-`d`)

Confirmed (`test_cover_and_bchain.py` + Codex (a)): the blow-up center is an equal-`b` run at every case,
for general monotone `d`, INCLUDING Case-2 successive clearing (each Case-2 step multiplies ALL remaining
`bᵢ` by the SAME `u_{S,J+1}`, so the residual stays equal-`b`; successive pivots differ in exponent but no
single center mixes unequal `bᵢ`) and the layer rollover (resets `J=0`; next Case-1 center is again a
maximal equal-`b` run). Wide/non-monotone (`d=(2,2,3,2)`): centers stay equal-`b`; the genuine non-monotone
defect is the printed raw-width label (`T`-label, already flagged L-B render:524-529, carries no label
field so no representation) — it does NOT spoil equal-`b` center geometry. Minor literal caveat: a Case-1
center also contains the exceptional `u_{s,k}`, which need not share the row divisor exponent — irrelevant
to the row-fan.

**⚠ The brief's STOP-condition (ii) checks the wrong thing.** §Guards STOP (ii) = "the stage-family
equivariance fails … (the center is NOT an equal-b run at some case)." The center IS equal-`b` (this
section) — so that guard passes GREEN. But the real risk is O1/O2/O4 (node non-transitivity, cover-cert
seam, wrong family), which the STOP-conditions do not name. The guards as written would give a FALSE-GREEN.

---

## What would settle the open part (recommended next)

1. **Decide the atlas identity up front:** tree full-fan g-maps (banked cover; certificates via transport
   where reachable + from-scratch elsewhere) vs transported charts (transport certificates; must re-prove
   the cover). O2 says you cannot have both for free.
2. **State + prove (or refute) the node-stabilizer/chart-path coherence theorem** O1/O2 need — the honest
   replacement for "one induction, two clauses." Likely form: a per-leaf-orbit representative set + a proof
   that the coreGen-orbit transports cover exactly the tree leaves they claim, with exponent-to-axis
   incidence retained (NOT exponent value alone).
3. **Rewrite the "one new lemma"** as coreGen (product) equivariance under the per-stage matched-gauge/end
   permutation (O4), and build its general-`d` form (the general-`d` analog of `Corank2CoreGenEquivar`).
4. **Re-scope the economy claim** (O3): route-B reduces leaf count via symmetry; the general-`d` L-A/L-B/L-C
   spine per orbit-representative + the route-a full-fan cover remain the load-bearing build. Gate the
   full-team commit on a general-`d` (not (3,3,4)) end-to-end of ONE intermediate-layer node: matched-gauge
   `hequiv` + the ancestor-pivot bookkeeping + the transported-chart cover, green-all.
