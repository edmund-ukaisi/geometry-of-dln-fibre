# R1-UPPER general-L box-finiteness — bounded-vs-wall DE-RISK

**Scout:** explore/reconnaissance (aoyagi-full).
**Target:** `routeMCore_threshold_lt_top {L : ℕ} (M : Fin (L+1) → ℕ)` — the ∀L bare sorry at
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean:426`. Statement: the route-M threshold integral
`∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} < ⊤` for `c' < ½·minAdm M`, for every depth `L`.
**Method:** verify-first (source-read of the actual Lean machinery) + exact-algebra on the `minAdm`
recursion. NO heavy Lean build. Codex CLI broken (Item 111) — proceeded on own analysis; a decorrelated
reviewer is requested from the controller.

---

## VERDICT: WALL (confirms Items 57 / 97; now with exact-algebra + Lean-object backing)

The ∀L R1-UPPER box-finiteness does **NOT** close via the corank-recursion scaffold. The scaffold
(`core_schurGen_lt_top`, `SchurCore`, `SchurRecStep`) is proven bedrock and does discharge the box at
depth `L = 2` (all `M`), but it is **intrinsically two-matrix** and its WellFounded recursion is on the
**corank of one square factor**, not on the number of layers. For `L ≥ 3` the target threshold
`½·minAdm M` is a **sum over a multi-boundary rank path**, and no two-matrix reduction reaches it. This
is a genuine research wall (an L-layer JOINT resolution that does not exist in the repo or in Mathlib),
not a bounded labour build.

This is **not** a new finding — it reproduces the Item-57 (2026-06-28) and Item-97 (2026-06-30)
verdicts. The value of this pass is (a) it independently re-derives the wall from the *actual Lean
objects* (not a design sketch), (b) it pins the obstruction with exact algebra over the proven `minAdm`
recursion, and (c) it corrects the Item-113 framing "NEEDS-DESIGN (below the walls)" — for the UPPER
atom this is the *same* L≥3 wall already named, not a fresh design frontier.

---

## 1. What is PROVEN vs OPEN (source-verified)

### The UPPER leg reduces cleanly, ∀M, to ONE named object (PROVEN, axiom-clean)

`RouteMBoxReduction.lean` supplies the decision-independent half:

- `routeMCore_le_matBox (M) (c')` — `∫_{routeMBaseNbhd M} |routeMCore M|^{−c'} ≤ routeMLayerBoxIntegral M c' 1`,
  pure measure-preserving plumbing (open box ⊆ closed cube; transport through `paramsEquivFlat` MP;
  `dlnLoss M 0 = frobSq(prod M A)`). **Fully ∀M, axiom-clean, no threshold claim.**
- `routeMCore_threshold_lt_top_of_box (M) (hbox : RouteMBoxThresholdFinite M)` — discharges the exact
  `:426` statement **given** `hbox`. ∀M, axiom-clean.

So the `:426` sorry is dischargeable the instant `RouteMBoxThresholdFinite M` is supplied, where
```
RouteMBoxThresholdFinite M := ∀ c' < ½·minAdm M,  ∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^{−c'} < ⊤.
```
**`RouteMBoxThresholdFinite M` for general L IS the entire open content.** (The header of
`RouteMBoxReduction.lean` states this explicitly and flags the general-`M` case a "category error,
decorrelated-Codex-confirmed.")

### The corank scaffold (PROVEN bedrock) — but two-matrix, corank-recursive

`RouteMSchurGeneral.lean`:
- `SchurCore p r c' T := ∫_{Δ∈matBox r r T} ∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'} < ⊤` — a **TWO-matrix**
  object: `Δ` square `r×r`, `S` free `r×p`.
- `SchurThreshold p lam` — the abstract threshold contract (`lam 0 = 0`, `lam r ≤ r²/2`,
  `lam r ≤ jp/2 + lam(r−j)`).
- `SchurLowerIH`, `SchurRecStep` — the IH and per-step contract, recursing on **corank `r` → r−j**.
- `core_schurGen_lt_top` — the WellFounded-on-**corank** wrapper. **Sorry-free, axiom-clean**
  (`[propext, Classical.choice, Quot.sound]`); the analytic content sits in the `SchurRecStep`
  hypothesis.
- The concrete `SchurRecStep` is discharged for the `p=4` binding family (corank-2 base
  `core_schur2_lt_top`, corank-3 firing) and, via the rect mirror, for general `(M0,M1,M2)` at depth 2
  (`routeMBoxThresholdFinite_mnp`, Item 100).

**Key structural fact (load-bearing):** there is no `L`-index anywhere in this scaffold. `p` (output
width) is a fixed spectator; the recursion measure is the corank of the *single* square factor. It
resolves the singularity of *one* two-matrix product `Δ·S`.

### The L=2 discharge (PROVEN) — works BECAUSE prod is two-matrix at L=2

`RouteMBoxThresholdRRP.lean`: at depth 2, `prod (![r,r,p]) A = A0·A1` is **literally** the
`SchurCore p r` shape (`A0 = Δ` square `r×r`, `A1 = S` free `r×p`). So `paramsBoxM (![r,r,p]) 1` IS the
free two-matrix box, the box integral IS `SchurCore p r c' 1`, and the corank recursion applies verbatim.
`schurLambdaP p r := ½·minAdm(![r,r,p])` is `rfl`, so the gate fires up to exactly the target threshold.

### OPEN: `RouteMBoxThresholdFinite M` for L ≥ 3 — the wall (below).

---

## 2. The obstruction, exact-algebra-verified (`/tmp/minadm2.py`, `/tmp/minvssum.py`, `/tmp/singlecut.py`)

### Instrument first (bedrock: verify the object I measure)

The threshold is `½·minAdm M`. `minAdm` is defined `((Adm M).inf' Mval).toNat` (`Lambda.lean`), and the
Lean file `RouteMLayerSplit.lean` **proves** (`minAdmRec_eq_minAdm`) the layer-peeling recursion
```
minAdm(M₀,…,M_L) = min_{t ≤ min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t,M₂,…,M_L) ]   (arity descent, one fewer LAYER)
```
I reimplemented the faithful `Adm`/`Mval`/`admPred` (the block-bound + weak-decrease + last-exponent-zero
constraints) and cross-checked: recursion **== faithful-brute, 0 mismatches / 4000 random chains**, and
the Lean anchors reproduce (`minAdm(2,2,2)=3`, `minAdm(3,3,4)=8=4·3−4`, `minAdm(4,4,2,2)=4`). The
recursion is the trusted object.

### Depth-2 tightness (why L=2 closes)

`schurLambda(r,p) = min(r²/2, min_j(jp/2 + schurLambda(r−j,p)))` (the SchurCore corank recursion) equals
`½·minAdm(r,r,p)` for **all** `r,p ≤ 4` (checked). The corank recursion computes exactly the depth-2
admissible minimum. This is why the two-matrix machinery is *tight* at L=2.

### The min-vs-sum wall at L ≥ 3

The target `minAdm` is a **sum** over the binding rank path; the binding minimizer `T` has ≥2 active
(nonzero) boundary terms in **86 / 256** L=3 chains (widths 1..4). Example `(2,2,2,2)`: minAdm=3, binding
`T=(1,0,0)`, per-boundary terms `[1,2,0]` — a rank drop `2→1` (codim 1) then `1→0` (codim 2), summing to
3. Two **distinct** rank-drop events at two boundaries.

The two-matrix machinery undershoots from **both** sides — a two-sided squeeze no re-cut escapes:

1. **Sequential fibre-peel** (`MatMulFibre.fibre_lintegral_mul_le`, the "iterated-fibre engine"):
   peeling one factor `X : p×n` off `X·Y` caps at **`c' < p/2`** (the peeled layer's row count) and
   preserves the SAME exponent `c'` on the residual `Y`. Iterating over layers therefore caps the total
   at `min_s (width_s)/2` — the **single most-binding layer**, undershooting the sum. (Item-57's
   "threshold undershoot", now located in the actual Lean engine at `MatMulFibre.lean:399`, cap `p/2`.)

2. **Single-cut Schur collapse** (treat prefix·suffix as one two-matrix core at boundary `k`, i.e.
   collapse the chain to `(M₀, M_k, M_L)`): the best such collapse `min_k minAdm(M₀,M_k,M_L)` is
   **≥ minAdm always** (0 undershoots / 256), and **strictly exceeds** minAdm in **44 / 256** L=3 chains
   (e.g. `(2,2,2,3)`: minAdm=3 but every single cut ≥ 4). Forcing all rank drop through one boundary
   costs strictly more; the true minimizer distributes it across ≥2 boundaries. Worse, even where the
   collapse value ties minAdm, the collapsed `SchurCore` is the **free** two-matrix box, whereas
   `paramsBoxM M 1` is the **product-constrained** box (`P = A₀·…·A_{k−1}` is a genuine product, not a
   free matrix). For L≥3 the product map `(A₀,…,A_{L−1}) ↦ (P, Q)` is **not** measure-preserving and
   **not** onto a box, so no change of variables dominates `routeMLayerBoxIntegral M` by a free
   `SchurCore`. At L=2 they coincide precisely because there is no earlier boundary — `prod = A₀·A₁` IS
   the free two-matrix product.

**Conclusion of §2:** the sum threshold is achievable in principle (it is the true Aoyagi codim), but
its realization needs a **joint** resolution that blows up along the whole rank flag *simultaneously* so
the per-boundary codims add — exactly what a sequential/single two-matrix step cannot do. The
`SchurCore`/`SchurRecStep` scaffold cannot be re-parametrized to recurse over layers: its object is
two-matrix and its measure is corank.

---

## 3. The MINIMAL named gap

**Gap R1U-∀L (the L-layer joint resolution for the box-integral finiteness).**

> Prove `RouteMBoxThresholdFinite M` for `M : Fin (L+1) → ℕ` with `L ≥ 2` general, i.e.
> `∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^{−c'} < ⊤` for all `c' < ½·minAdm M`, where `prod M A` is the
> `L`-fold product `A₀·A₁·…·A_{L−1}`.

**Why the proven scaffold does not reach it (precise):**
- The scaffold's object `SchurCore p r` is a *two-matrix* integral `∫∫ frobSq(Δ·S)^{−c'}`; its recursion
  descends **corank** `r`, with `p` (output width) a fixed spectator and **no layer index**.
- For `L ≥ 3` the box integrand is `frobSq(A₀·…·A_{L−1})^{−c'}`, an `L`-fold product. It is not of the
  form `frobSq(Δ·S)` for any free `(Δ, S)` measure-equivalent to `paramsBoxM M 1`.
- The threshold `½·minAdm M` is a **sum** (`minAdmRec`'s layer descent) over ≥2 active boundaries for a
  large fraction of chains; the two-matrix engine caps at the **min** boundary (fibre-peel) or forces a
  single boundary (collapse, which overshoots the value AND changes the object). Both fail.
- What is *missing* is genuinely new mathematics: an `L`-layer joint blow-up / resolution whose Jacobian
  and Morse split realize the additive `minAdm` codim across all boundaries at once. Neither the repo
  (only the algebraic `prod_front_peel` exists — `RouteMFrontPeel.lean`, pure matrix algebra, no
  analytic peel bound) nor Mathlib has this.

**Sub-structure of the gap (for scoping, if ever charged):**
- (a) an `L`-layer analog of the radial-Δ cover + minor-pivot Schur split that peels **each** layer
  boundary at its own shifted exponent and recurses on a chain with one fewer layer (mirroring
  `minAdmRec`'s arity descent), composing the per-boundary Morse contributions **additively** — a new
  WellFounded recursion on the **arity** `L`, not on corank;
- (b) the joint-domination lemma that the sequential peels do not double-count and reach the exact
  `½·minAdm` sup (the analog of the O2 pushforward, but across layers rather than corank);
- (c) the measure-theoretic handle connecting the constrained product box to the peel — the piece that
  `fibre_lintegral_mul_le` provides at *one* boundary but which loses the exponent across boundaries.

This is the "L-layer JOINT resolution that does not exist" of Item 97 and the "min-vs-sum structural"
wall of Item 57.

---

## 4. The de-risk sub-questions, answered

The mission asked to verify (a) termination, (b) per-step bound + composition, (c) no hidden research
wall — modelled on how `genm-l3interior` adjudicated the interior chart. Answers:

- **(a) Does a recursion terminate?** A *corank* recursion terminates (`core_schurGen_lt_top`,
  WellFounded on `r`, PROVEN). A *layer* recursion would terminate on arity `L` (`minAdmRec` descends
  arity, structurally). Termination is **not** the obstruction.
- **(b) Does the per-step finiteness bound hold and compose?** At the corank level, yes (the scaffold).
  At the **layer** level: the only built per-step bound is `fibre_lintegral_mul_le`, which caps at `p/2`
  and **preserves the exponent** on the residual — so it does **NOT** compose to the sum. There is no
  built exponent-shifting layer-peel bound. This is where the wall bites.
- **(c) Hidden research wall?** **YES** — the L-layer joint resolution (Gap R1U-∀L §3). It is *not*
  labour on a proven template (contrast `genm-l3interior`, where the L≥3 interior chart was a *monomial
  generalization* of a worked L=2 chart, verified by exact algebra, so BOUNDED). Here the L=2 discharge
  is **intrinsically two-matrix** and there is no worked L≥3 analog to generalize — the two-matrix
  object literally cannot represent the L-fold product. This is the opposite adjudication to
  genm-l3interior: a genuine wall, not bounded labour.

**Contrast with genm-l3interior (LOWER interior), for the controller.** That de-risk found the L≥3
interior achiever chart was a monomial *generalization* of the L=2 one (a worked template existed;
exact algebra confirmed the same monomial shape ∀L) → BOUNDED labour. The R1-UPPER box-finiteness has
**no such worked template at L≥3**: the L=2 template is two-matrix by construction and the target
threshold changes character (min → sum). So the two atoms of the general-L R1 resolution adjudicate
**oppositely**: LOWER interior = bounded (charge); UPPER box-finiteness = wall (operator-gate).

---

## 5. Cross-check against the standing fallback

The synthesis has always carried a fallback (Item 39): R1-UPPER finiteness has a **CITED** route —
Watanabe's universal `rlct ≤ ½·codim` — so the from-scratch N4 is the "go-the-distance" upgrade, and a
scoped retreat to the cited upper bound keeps the *headline* intact if N4 walls. This de-risk confirms N4
(the from-scratch ∀L box-finiteness) **is** a wall; the cited fallback remains the honest route for the
general-L upper bound if the headline needs it. (The exact `rlct = ½·codim` equality is Cited already —
`RlctInterface.cited_aoyagi_dln` — per CLAUDE.md; that citation covers the finiteness the from-scratch N4
would otherwise supply.)

---

## Files / anchors

- Target sorry: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchur.lean:426`
  (`routeMCore_threshold_lt_top`).
- Reduction (PROVEN, ∀M): `lean/DLNFibre/DLN/RLCT/Validate/RouteMBoxReduction.lean`
  (`routeMCore_le_matBox`, `RouteMBoxThresholdFinite`, `routeMCore_threshold_lt_top_of_box`).
- Two-matrix corank scaffold (PROVEN, corank-recursive): `RouteMSchurGeneral.lean`
  (`SchurCore`, `SchurRecStep`, `core_schurGen_lt_top`).
- L=2 discharge (PROVEN, two-matrix): `RouteMBoxThresholdRRP.lean` (`prod = A0·A1 = SchurCore p r`).
- The single-boundary fibre-peel cap `c' < p/2`: `MatMulFibre.lean:399` (`fibre_lintegral_mul_le`).
- The algebraic (not analytic) front-peel: `RouteMFrontPeel.lean` (`prod_front_peel`).
- The proven layer-peeling threshold recursion: `RouteMLayerSplit.lean`
  (`minAdmRec`, `minAdmRec_eq_minAdm`).
- Exact-algebra scripts (reproduce §2): `/tmp/minadm2.py`, `/tmp/minvssum.py`, `/tmp/singlecut.py`.

## Instrument caveat (bedrock)

The exact-algebra above measures `minAdm` (the *threshold value*) and the *shape* of the recursion
objects — it establishes that no two-matrix reduction reaches the sum threshold, which is the precise
sense in which the scaffold falls short. It does **not** numerically integrate the box (I did not compute
`∫ frobSq(prod)^{−c'}` at any c'); the finiteness claim rests on the RLCT/codim theory (`½·minAdm` = the
true threshold, Aoyagi/Cited) that the whole expedition already relies on. The verdict is: the *proven
machinery* cannot supply that finiteness at L≥3, and the missing piece is new mathematics — not that the
finiteness is false (it is true, by the cited theory).
