# Case222 monomial tree → general `resolution_charts`: what's (2,2,2)-specific vs general (fm3 prep)

Prep for #27 (general Route-M FORMALISATION, blocked on #26 design + the (S)/R1.6 exhaustiveness
reconcile). Maps the banked explicit (2,2,2) blow-up tree (`Case222Resolution.lean`, origin/fm/r1-cover)
onto the general target `resolution_charts` (`Skeleton.lean:1017`, currently `sorry`):
`rlctAtOn (dlnLoss M 0) 0 = ⨅ i:ι, monomialThreshold (d i)(k i)(h i)`.

## The (2,2,2) tree, node by node (what each node IS)

| node | Lean | what it does | Jacobian | output |
|---|---|---|---|---|
| step-1 | `step1A = pivotBlowupOn {0,1,2,3} 0` | blow up A-block at pivot a00 | `x0³` (`card−1=3`) | `myF222 = y0²·step1Residual` |
| Lemma-2 | `lemma2Hom` (Fwd/Inv) | measure-preserving REGULAR change, det ±1, NO blow-up | `1` | `step1Residual = resolvedForm ∘ lemma2Fwd` |
| step-2 E | `step2E = pivotBlowupOn {1,2,3} 1` | blow up resolved vertex at pivot E | `z1²` (`card−1=2`) | `resolvedForm = z1²·U`, `U≥1` (UNIT leaf) |
| step-2 δ | `step2D = ![z0, z1·z2, z1·z3, z1, z4,z5,z6]` | blow up at pivot δ (input slot 1, placed slot 3) | `z1²` | `resolvedForm = z1²·block` (block vanishes → step-3) |
| step-3 | `blockForm_step3` (sub-blowup) | blow up block vertex | `u³` | `block = u²·res`, `res≥1` (BLOCK leaf) |

VERIFIED CAVEATS (checked against the banked file, not asserted):
- `step1A_eq_pivotBlowupOn` and `step2E_eq_pivotBlowupOn` are PROVEN ties to the atlas. But there is
  NO `step2D_eq_pivotBlowupOn` and NO `step3_eq_pivotBlowupOn` banked — the δ-branch + step-3 are
  defined as explicit `![…]` maps / `blockForm_step3` algebra and tied to the atlas only via the
  `≥`-cover machinery (`Case222CoverGE`/`Tail`), not via a clean `= pivotBlowupOn` rewrite. For #27 the
  GENERAL construction should route EVERY node through `pivotBlowupOn` (the unit branch shows it's
  possible); the banked δ-branch not doing so is (2,2,2)-specific scaffolding, not a general pattern.
- `lemma2` measure-preservation is PROVEN (`measurePreserving_lemma2` / `_lemma2Hom`).

Leaf integrand shape: `monomial × unit`, `unit ≥ 1` (sum of 1 + squares). 8 unit leaves + 16 block
leaves = 24, all `monomialThreshold = 3/2`. The `⨅` over the cover = 3/2.

## KEY STRUCTURAL FACTS (carry to the general case)

1. **Each blow-up node = `pivotBlowupOn active p`** (the gated atlas). `step1A_eq_pivotBlowupOn`,
   `step2E_eq_pivotBlowupOn` tie the explicit charts to the atlas; Jacobian = `(x p)^(active.card−1)`
   (`pivotBlowupOnDeriv_det`). GENERAL: every node is `pivotBlowupOn` on its active coordinate block.
2. **The pivot-square factorization IS the homogeneity I flagged in the route-check.**
   `myF222(step1A y) = y0²·Q` — the loss is deg-2 in the active block, blow-up factors `(pivot)²`. This
   is GENERAL (any A-pivot, any node) and is exactly WHY the squeeze route failed and the monomial
   route is the live one: the `(pivot)²` is the exceptional divisor whose `(k,h)` feeds
   `monomialThreshold`, NOT an additive `nReg/2` smooth block.
3. **Lemma-2 (regular MP change) sits BETWEEN blow-up nodes.** det ±1, transports the lintegral with no
   Jacobian (`setLIntegral_image_of_mp`). GENERAL: the "Aoyagi Lemma 2" regular straightening — a
   measure-preserving normal-form step interleaved with the blow-ups. (NOT a squeeze, NOT a c-o-v of
   the rlct — a lintegral-level splice.)
4. **Branching at a node = the pivot CHOICE (which coordinate is the argmax pivot).** step-2 has E/F0/δ
   pivot branches; E/F0 → unit leaves, δ → block branch (needs step-3). GENERAL: the chart family index
   `ι` is the TREE of pivot-branch choices × affine-minor choices; per `Skeleton.lean:1006` the charts
   OUTNUMBER the strata (not a bijection — VALUE match only).
5. **Leaves are `monomial × unit`, `unit ≥ 1`.** `step2E_unit_ge_one`, `step3_unit_ge_one`. The unit
   `≥ 1` is the `0 < a` nonvanishing input to `integrableOn_monomial_mul_unit_iff`. GENERAL: every leaf
   bottoms out at a unit (sum of 1 + squares) once the singular directions are blown up.
6. **The cover = `g5_pivotNode` composed.** Each node's `∫_U g = Σ_p ∫|det φ'|·g∘φ` over its argmax
   cells; the tree is `g5_pivotNode` recursed (Codex shape: recurse on `g' = wᵢ·(g∘φᵢ)`).

## (2,2,2)-SPECIFIC (must be replaced by a general construction)

- **The explicit `![…]` chart maps** (`step1A`, `step2E`, `step2D` as `Fin 8`/`Fin 7` vector literals)
  — general needs the chart as `pivotBlowupOn active p` for a DERIVED `(active, p)` per node, not a
  hand-written literal.
- **The fixed tree depth (3) + the fixed 24-leaf count** — general depth/breadth come from the (S)/R1.6
  exhaustiveness design (#26/#17/#20): which charts exist + that they cover. THIS is the blocker — the
  index set `ι` and the per-leaf `(d,k,h)` are what the design must pin.
- **The specific `(k,h) = (3,2)` exponents giving 3/2** — general `(k,h)` per leaf come from the node's
  active-block size (`h = card−1` Jacobian) + the loss-base exponent (`k`); the `⨅` value is A1's
  `lambdaCore` (the cited `monomial_rlct` ≤-half + the clean `≥`-cover).
- **`lemma2Fwd/Inv` as explicit `Fin 7` maps** — general Lemma-2 is the regular straightening of a
  general bilinear rank-defect center, det ±1, a parametrized family.

## THE GENERAL CONSTRUCTION SHAPE (what #27 builds, once #26 pins the index set)

`resolution_charts M`: recurse `g5_pivotNode` over the blow-up tree. At each node:
  (a) pick the active block + argmax pivot `p` (the cover, from `argmaxCellOn_cover`);
  (b) `pivotBlowupOn active p` factors `(pivot)^(card−1)` Jacobian + `(pivot)²` loss factor
      (homogeneity) → `monomial × residual`;
  (c) Lemma-2 regular MP straighten the residual to normal form;
  (d) recurse on the residual until it bottoms out at a unit (`≥ 1`).
The leaves give `(ι, d, k, h)`; the cover (g5 composed) + the per-leaf monomial pullback give the
`⨅ monomialThreshold` value. SEPARATE the clean geometric `≥`-cover (S2-free, clean-three) from the
cited analytic `≤`-half (`monomial_rlct`, Aoyagi/Watanabe) — precision discipline (the `rlct=½·codim`
reading rests on the cited bound).

## THE DESIGN SUBSTRATE (r1-cover-and-decomposition.md + g121 — read for #27 readiness)

The general Route M is decomposed R1.1–R1.7 (`r1-cover-and-decomposition.md`). My lane is R1.1/R1.2/R1.6:
- **R1.1 chart family `ι`** = pivot branches of the iterated L1 (Aoyagi affine atlas); per chart
  `(d_i,k_i,h_i)`, `k=1` on each exceptional divisor. (REUSES L1.)
- **R1.2 universal divisor-ratio lemma** [MY CORE, NEW]: a smooth codim-`c` center cut by a REGULAR
  SEQUENCE (multiplicity 1) ⇒ `core∘φ = u²·unit` (`k=1`) + `|det Dφ| = u^{c−1}·pos` (`h=c−1`), ratio
  `c/2`. The general analog of `myF222_step1A` (`u²·unit`) + `pivotBlowupOnDeriv_det` (`u^{c−1}`). The
  `k=1` (regular sequence, mult 1) is WHY `rlct = ½·codim` here, NOT the false generic codim bound
  (`xᵏ` gives `1/(2k) < ½`; `(x²+y²)²` gives `1/2 ≠ 1`). Multiplicity control is the load-bearing point.
- **R1.6 cover/exhaustiveness** [the "mountain", co-owned]: the pivot branches' images cover a nbhd of
  `origin ∩ {core=0}` (exhaust the rank-pattern strata). An exhaustiveness claim `Z = ⋃_t S(t)`, NOT a
  per-chart exponent computation. The genuine residual difficulty.

**The (C2) node structure (g121, decorrelated pp + Codex):** each NONTRIVIAL node is
  (1) unit-pivot chart (normalize a nonzero pivot minor to a unit), (2) **det-1 Schur straighten**
  (unit-pivot row/col ops, **Jacobian 1**, reduces the chain + STRAIGHTENS the bilinear rank-defect
  center `{r−pq=0}` to a coordinate subspace `{w=0}`, `w:=r−pq`), (3) smaller-chain residual,
  (4) **coordinate-subspace blow-up** of the now-coordinate center `{y₁=…=y_c=0}`, `c=Mval(t)`: chart
  `yᵢ=u, yⱼ=u·vⱼ`, **Jacobian `|u|^{Mval(t)−1}`**, `F∘π = u²·F_res`, `(k,h)=(1,Mval(t)−1)`, ratio
  `Mval(t)/2`. THE MONOMIAL WEIGHT comes from the BLOW-UP (4), the det-1 Schur (2) contributes NONE.

This CONFIRMS my route-check from the design side: the per-node RLCT weight is the blow-up's `u²`
exceptional factor (monomial route), NOT an additive `nReg/2` smooth block (the off-path squeeze). The
det-1 Schur's job is to keep the center a coordinate subspace so `pivotBlowupOn` can fire — it is the
"regular-change" step my `schur_node_loss_presentation` (`‖Â·A2‖² = ∑E²+∑(bE+SΓ)²`) may serve (it is
the residual `‖Ahat·A2‖²` row-decomposition, the post-blow-up object the Schur straightens).

**AWAITING (the blocker, #26 in progress):** pp2's blueprint synthesizing pp3's C1–C4 HETEROGENEOUS
node taxonomy (coupled blow-up / Fubini-pinch / full-rank pass-through Schur / k_E≥2 NC-completion) +
the (S-min) achiever. g121 covers the BASIC node (coordinate node-1 + bilinear-straighten node-≥2);
the C1–C4 refinement (which node type fires when, and the k_E≥2 NC-completion = the one place `k>1`
needs Newton-crossing completion) is what #26 must pin before the general tree's index set `ι` is
determined. NOT yet written to a file I can read — it is the #26 deliverable. HOLD until dispatched.

## DEPENDENCY (why HOLD)

The index set `ι` (which charts exist) + that they cover (a.e.) = the (S)/R1.6 EXHAUSTIVENESS design,
adjudicated by pp2 (witness, #20) + pp3 (obstruction, #17) and blueprinted by #26. Building the tree
before that lands = guessing the index set = the exact interface-mismatch failure mode caught at the
squeeze interface. HOLD until #26 dispatches the precise target.
