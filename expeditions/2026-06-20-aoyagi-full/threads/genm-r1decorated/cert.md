# R1-UPPER decorated `I_π(s)` contract + BUILD-vs-CITE — design certificate (pen-and-paper)

**Seat:** pen-and-paper (OBSTRUCTION + WITNESS). **Branch:** `genm-r1decorated` off
`expedition/aoyagi-full` (synced to `1468a586`, UPDATE-690). **No Lean build.** Exact algebra
(sympy/scipy) + a decorrelated `local-codex-consult` (xhigh, hypothesis withheld). **Mission (from
UPDATE-690 / #58):** (A) pin the decorated `I_π(s)` contract Lean-ready so the plain-IH
`sjJointResolution` becomes its `π=∅` consumer; (B) adjudicate BUILD-vs-CITE for the one genuine-new
brick, on `(2,2,2,2) t=1` → the corank-2 deeper-product case — to make the operator's cite-footprint
call crisp.

---

## HEADLINE VERDICT

**(B) BUILD is viable — and the CITE fallback adds NO new footprint (it is the *existing*
`cited_aoyagi_dln`).** The "genuine-new brick" splits into two DIFFERENT objects that UPDATE-690's
phrasing conflates:

1. **The atom-route product-Gram principalisation** — `det(Q_b Q_bᵀ)=‖∧^q Q_b‖²` of the matrix
   PRODUCT `Q_b=A_{k,b}·Z` — **is genuinely `B` (from-scratch resolution-of-singularities; Mathlib
   lacks Cauchy–Binet, SVD, and any decomposition valid on the rank-drop locus).** But it is a
   **TRAP, not a requirement**: it only appears if you integrate the corank block `Γ` OUT (the atom
   route). It is provably an over-count artifact on `{det=0}` (`pure-vs-atom-adj.md`), and the native
   route never forms it.
2. **The native R-BLOWUP depth recursion** — peel one boundary at a time, outside-in; the corank
   block is a CHART coordinate (blown up, never integrated out); the deeper factor is a spectator
   until its own boundary. **This AVOIDS the Gram determinant entirely and is `A` (break-it-down
   buildable):** chart algebra on the banked radial engine + the monomial endpoint + the
   `Case111/Case222` templates + the banked charge budget. Its one substantial (bounded) brick is the
   **general-`(L,S,J)` single-radial chart lemma with a shared-support ledger** — NOT res-of-sing.

My exact algebra tested the **one load-bearing thing no prior doc checked with matrix algebra**: does
the native recursion reach normal crossing when the shared deeper factor is a genuine PRODUCT
`Z=W₁·W₂` at corank ≥ 2 (the case beyond the verified single-matrix `(3,3,4)`)? **Answer: YES, on a
finite explicit sequential chart cover, with the shared support closed under the regular elimination.**
Decorrelated Codex reached the same (BUILD, bounded) independently, confidence 0.72, and named the same
residual risk — the Case-1 equal-run generator-mix — which I then probed and found bounded.

**So the operator's real call (crisp):**

- **(A) BUILD** the native R-BLOWUP `(S,J)` recursion (mandate-default). Multi-tide (est. 12–20 tides,
  possibly a sub-expedition). Removes R1-UPPER box-finiteness's dependence on the cite. Residual risk:
  the general chart lemma's shared-support closure (bounded chart algebra, not a math wall; my +
  Codex's confidence, ~0.72–0.8). **No new cite.**
- **(B) CITE** — rest R1-UPPER box-finiteness on the **already-carried** `RlctInterface.cited_aoyagi_dln`
  (Aoyagi `rlct = ½·codim`, which the payoff *already* cites and which delivers `rlct ≥ ½·codim` =
  exactly the box-finiteness). **Near-zero cost. Cite-footprint UNCHANGED** — this corrects
  UPDATE-690's "add a 2nd interface (footprint change)"; no second interface is needed, and no
  product-Gram-principalisation axiom is needed.

The decision is **from-scratch-purity (BUILD, multi-week) vs status-quo-cite (CITE, free)** — NOT a
cite-footprint expansion. Both keep the headline; the difference is whether R1-UPPER box-finiteness is
proved geometrically or rests on the same Aoyagi citation the payoff already uses.

**No contradiction with `r1upper-derisk.md` / `r1upper-wall-review.md` (a scope clarification).** Those
docs correctly show the **two-matrix corank scaffold** (`SchurCore Δ·S`, WellFounded on *corank*)
cannot reach the additive `½·minAdm` sum threshold for `L ≥ 3` — a factor-of-2 undershoot at
`(3,3,3,3)`. Their own §3 names the missing piece as "**a new WellFounded recursion on the ARITY `L`,
not on corank**." That arity recursion IS the native R-BLOWUP depth recursion this cert adjudicates as
`A`/buildable. So the two verdicts compose: *corank scaffold walls* (wall-review) → *the arity/depth
R-BLOWUP recursion is the buildable route* (this cert), matching `minAdmRec`'s layer descent. The
decorated `I_π(s)` induction (A) is exactly that arity recursion made into an inductive statement.

---

## (A) The decorated `I_π(s)` contract — Lean-ready shapes

### The object, in the repo's own machinery

The plain hypothesis (`RouteMBoxReduction.lean:165`) is
```
RouteMBoxThresholdFinite (M) : Prop :=
  ∀ c' : NNReal, (c':ℝ) < (minAdm M : ℝ)/2 → routeMLayerBoxIntegral M (c':ℝ) 1 < ⊤
```
The plain IH `∀ M', RouteMBoxThresholdFinite M'` is on the **EXHAUSTED lane** (UPDATE-690, 3
confirmations): at the binding cut `minAdm M = a + minAdm(redChain t* M)` (definitional, `0/4000`) the
residual exponent saturates the reduced-chain threshold, leaving **zero budget** for the coupling. The
fix is to carry the accumulated weight **inside** the inductive statement.

**Key simplification I verified (collapses the `outer-construction-cert` threshold to repo machinery).**
The decorated threshold `Θ(M,π)=½(min_{T⪰π}Mval − A(π))` equals **`½·minAdm(remChain π)`**, because
`min_{T⪰π}Mval_M(T) = A(π) + minAdm(remChain π)` (Mval decomposes as accumulated-charge + min-over-the-
remaining; this is exactly `minAdmRec`'s layer descent iterated). **Verified `3592/3592` over all
admissible prefixes of all width-`1..4` 4-chains** (`r1d_theta.py`). So the decorated object is just
`RouteMBoxThresholdFinite` **of the remaining chain**, weighted by the accumulated decoration — no new
threshold notion is needed; reuse `minAdm ∘ remChain`.

### Shapes a formaliser would write (no proofs)

```lean
/-- A partial rank profile: `k` peeled cuts, weakly decreasing, admissible.  Prefix of a full branch.
    `remChain π = (t_k, M_{k+1}, …, M_L)` is the still-unresolved chain (iterated `redChain`). -/
structure PartialProfile {L : ℕ} (M : Fin (L+1) → ℕ) where
  cuts     : List ℕ                       -- (t₁, …, t_k)
  weakDec  : cuts.Chain' (· ≥ ·)          -- weakly decreasing
  admis    : True                         -- t_j ≤ admBound (spell out via Adm)
-- remaining chain after peeling the profile (iterate `redChain`; π=∅ ↦ M):
def PartialProfile.remChain {L} {M} (π : PartialProfile M) : Σ L', (Fin (L'+1) → ℕ) := …
-- accumulated charge A(π) = Σ (t_{j-1}-t_j)(M_j-t_j)  [= LayerSplit.codim summed; banked value half]:
def PartialProfile.accumCharge {L} {M} (π : PartialProfile M) : ℕ := …

/-- The BUILDABLE decoration (native R-BLOWUP / Aoyagi diag(b) carrier).  NOT a Gram determinant. -/
structure SJDecoration {L} {M} (π : PartialProfile M) where
  bMon     : Fin (leadWidth π) → Monomial DivVar   -- the diag(b) radial monomials  b_i = ∏ u
  support  : Gen → Finset DivVar                    -- which exceptional u divides which generator
  -- (the SHARING relations — DATA-A/DATA-1: provably necessary at corank ≥ 2)

/-- The decorated finiteness predicate.  `Wπ` is the accumulated RADIAL-MONOMIAL Jacobian weight
    (from the blow-up charts) — a MONOMIAL, NOT det(Q_b Q_bᵀ). -/
def DecoratedBoxThresholdFinite {L} {M} (π : PartialProfile M) (dec : SJDecoration π) : Prop :=
  ∀ c' : NNReal, (c':ℝ) < (minAdm (remChain π).2 : ℝ)/2 →
    ∫⁻ (over the remaining-chain box) (Wπ dec) · |loss(remChain π)|^(-(c':ℝ)) < ⊤

/-- The carrier threshold Θ(M,π), collapsed to repo machinery. -/
def carrierThreshold {L} {M} (π : PartialProfile M) : ℝ := (minAdm (remChain π).2 : ℝ)/2
```

**Peel step (Cases 1 & 2 — the recursion engine), soundness = threshold-monotonicity:**
```lean
/-- One peel at the next legal cut u=t_{k+1}: adds charge a=(t_k-u)(M_{k+1}-u), creates one radial
    exceptional for the current corank block, shifts s ↦ s − a/2, extends the decoration. -/
theorem decorated_peel_step {L} {M} (π : PartialProfile M) (dec : SJDecoration π)
    (u : ℕ) (hu : legalNextCut π u)
    (ih : DecoratedBoxThresholdFinite (π.extend u) (dec.extend u)) :
    DecoratedBoxThresholdFinite π dec
-- soundness reduces to  minAdm (remChain (π.extend u)) ≥ minAdm (remChain π) − a   (0/171, DATA-C):
theorem carrierThreshold_mono {L} {M} (π : PartialProfile M) (u : ℕ) (hu : legalNextCut π u) :
    carrierThreshold π − (peelCharge π u : ℝ)/2 ≤ carrierThreshold (π.extend u)
```
(`peelCharge π u = (last-cut-of-π − u)(M_{index+1} − u)`; the "≥" is threshold monotonicity,
`min_{T⪰(π,u)}Mval ≥ min_{T⪰π}Mval`, verified `0/171` by DATA-C, on the banked `minAdm`.)

**Base (well-founded on chain arity / profile length ≤ L):**
```lean
/-- π full (remChain a single node, or L=1 one-matrix / free-vector): the banked Morse terminal
    weighted by the accumulated ∏ b_i monomial. -/
theorem decorated_base {L} {M} (π : PartialProfile M) (dec : SJDecoration π)
    (hfull : (remChain π).1 = 0 ∨ …) : DecoratedBoxThresholdFinite π dec
-- consumes: sjBase1_freeMatrix / sumSqND_box_lt_top  ×  monomialIntegrand_integrable_of_lt (weighted).
```

**The plain-IH slot (π = ∅ is the top-level consumer):**
```lean
/-- π=∅ (no peels): remChain ∅ = M, accumCharge = 0, Wπ = 1, carrierThreshold = ½·minAdm M.
    So DecoratedBoxThresholdFinite ∅ (trivial dec) = RouteMBoxThresholdFinite M. -/
theorem routeMBoxThresholdFinite_of_decorated {L} (M : Fin (L+1) → ℕ) :
    DecoratedBoxThresholdFinite (PartialProfile.empty M) (SJDecoration.trivial) →
    RouteMBoxThresholdFinite M
-- and the decorated statement is closed by well-founded recursion on profile length via
-- decorated_peel_step (Cases 1&2) with decorated_base at the leaves — matching the EXISTING outer
-- spine (Nat.strong_induction / routeMBoxThresholdFinite_of_step), but over the DECORATED statement.
```

So the existing spine (`routeMBoxThresholdFinite_of_step`, `Nat.strong_induction_on`) stays as the
**outer scaffold**; `sjJointResolution` / `RouteMBoxThresholdFinite M` is recovered as the `π=∅`
corollary via `routeMBoxThresholdFinite_of_decorated`. The measure-route inventory
(`chartInner_blockReindex_eq`, `chartInner_schurWeld_eq_of_emb`, `chartInner_schurShearFree_eq`,
`freedSchurLoss_inner_peel_lt_top`, the terminal, `gen_rowMix_const`) is the **complete steps-1–2
inventory** that realizes ONE `decorated_peel_step` (one Case-2 peel), pre-integrated — reusable, slots
under the decorated recursion.

**Route note (load-bearing).** The `outer-construction-cert.md` writes `W_π = ∏ det(Q_b Q_bᵀ)^{−p/2}`
(Gram-determinant weights). **That is the ATOM flavor and commits to the `B`-trap.** The buildable
decoration is the **radial-monomial `diag(b)` + support map** (SJDecoration above): the block is never
integrated out, so no Gram determinant forms. The abstract threshold accounting (`Θ`, charge `A(π)`,
monotonicity) is route-agnostic and identical either way; only the WEIGHT realization differs, and only
the radial-monomial one is `A`.

---

## (B) BUILD-vs-CITE — exact evidence on the smallest cases

### The mechanism (Test 1, `(2,2,2,2) t=(1,0,0)`, `r1d_test1.py` — sympy, exact)

- **Incidence-chart identity EXACT.** `A=α[[1,a],[b,ab+δ]]`, `B=[[u−ar,v−as],[r,s]]` ⟹
  `A·B = α[[u,v],[bu+δr, bv+δs]]` = `α·[pivot row (u,v); b·(pivot) + δ·(r,s)]`. Verified `= 0` residual.
- **The one-shot / atom is REFUTED.** One blow-up of `{δ=u=v=0}` leaves the residual
  `‖[[ξ,η],[bξ+r,bη+s]]·C₃‖²` **vanishing at the chart origin** (order ≥ 2 in my chart; worked-tex:
  order 4 in theirs) — NOT a unit. One blow-up does not resolve; the depth recursion is required.
- **The depth recursion is clean.** That same residual is a **FRESH depth-2 core** `‖X·C₃‖²`
  (`X=[[ξ,η],[bξ+r,bη+s]]`, `C₃` untouched) — recurse on it. `Γ`/the block is a CHART coordinate,
  never integrated out. **No `det(Q_b Q_bᵀ)` ever forms.**
- **Where the atom's product-Gram trap lives.** `Q_b = A_{1,b}·A₂` is a `1×2·2×2` PRODUCT; on
  `{A₂ rank-drops}` (rows `∝`), `‖Q_b‖² = (w₁+k w₂)²(c₁₁²+c₁₂²)` VANISHES on a codim-1 sub-locus even
  for a nonzero row — the extra product-vanishing the atom must jointly principalise (which coordinate
  divides which minor). The depth recursion never sees it.

### The CRUX (Test 2, the corank-2 deeper-PRODUCT case — the untested extension)

The worked-tex verified the coupled `diag(b)` resolution for rank-1 peels (L=3,4) and corank-2 where
the deeper factor is a SINGLE matrix (`(3,3,4)`, `rlct=4=½·Mval`). **Nobody had checked, with matrix
algebra, whether it extends when the shared deeper factor is a genuine PRODUCT** `Z=W₁·W₂` (the
worked-tex flagged this "optional refinement, not blocking" but never ran it). Smallest witnesses
(`r1d_witness.py`): `(3,3,3,4) t=(1,0,0)` — layer-1 corank 2, deeper product `C²·C³`, `minAdm=7`.

**Q1 — does the coupled term inherit the deeper exceptionals on ONE finite sequential cover?**
(`r1d_test2b.py`, `r1d_test2c.py` — sympy, exact) **YES.**
- The shared factor `Z=W₁·W₂` rank-drops on `{det W₁=0} ∪ {det W₂=0}` — **loci INTRINSIC to `Z`,
  independent of the coupling rows `T,R`.** The recursion blows up these intrinsic loci (one radial per
  deeper boundary); the centers do not depend on `T` or `R`, so the SAME chart cover resolves both
  `‖T·Z‖²` and `‖R·Z‖²`.
- Explicit rank-1 deeper drop: after the deeper-boundary blow-up the reduced factor `= v·X` (v the
  deeper exceptional), so `v` divides **every** generator — main `~v·x₁ⱼ` and coupled `~δ·v·xᵢⱼ`.
  Shared `v`; `δ` is a **passive prefactor**. Ledger closed.
- Toric confirmation (scipy LP, exact): 3-layer deeper-product SHARED `{u²x², u²v²y², u²v²w²z²}` gives
  RLCT `0.5`, fully-separate gives `1.5` — the deeper-product layer `w` is captured by the SAME
  shared-radial mechanism as the shallow ones; sharing necessary AND toric-reachable.

**Q2 — do the block-elimination transforms `Q,P` stay regular with a product deeper factor?**
(`r1d_test2c.py`) **YES.**
- `Q,P` are built from the **current factor's own entries** (row/col unipotents); the deeper factor is
  absorbed to the right `(PCQ)(Q⁻¹Z)`. `det P = det Q = 1` regardless of `Z`. Regularity is
  INDEPENDENT of single-vs-product deeper factor.
- **Codex's residual risk probed** (its 0.72 failure mode: a Case-1 equal-run chart where the regular
  elimination mixes generators of different `b_i`-support). A row-mix `m' = m + λc` (non-δ row + δ-row)
  gives `m' = v·(x₁₁+λδx₂₁, x₁₂+λδx₂₂)` — leading support `{v}` PRESERVED (the δ-term is HIGHER order),
  elimination matrix unipotent (det 1, no pole). The δ-prefactor is a passive higher-order perturbation
  on the shared divisor; the row-mix creates no incompatible-support generator and no denominator. The
  ledger stays closed. **Bounded chart algebra, not a joint principalisation.**

**Scope of my certificate (honest).** The Q1/Q2 computations are on representative rank-1-deeper-drop
instances and the toric skeleton — they establish the MECHANISM is sound (intrinsic centers, shared
radial, absorbed-right regularity, passive-δ Case-1 merge). They do **not** constitute a proof for all
widths / all equal-run partitions. That general statement IS the "general-`(L,S,J)` single-radial chart
lemma with shared-support ledger" — the single substantial bounded brick. My verdict: the mechanism
does not wall; the remaining work is bounded (finite `(S,J)` recursion, certified value), substantial
multi-tide labor, NOT res-of-sing.

---

## The BUILD plan (if the operator chooses A — the mandate default)

**Route: native R-BLOWUP `(S,J)` depth recursion.** Do NOT integrate the block out (no
`gammaAtom_aniso_shifted` → outer Gram-det: that is the `B`-trap on the degenerate strata).

Chart sequence per peel (one Case-2 step; Case-1 for partial equal runs):
1. finite pivot-chart cover of the rank-≥t / corank strata — `pivotChartCover_matBox_le_sum` +
   `pivotLocus_eq_iUnion` (banked).
2. incidence chart + **one** radial blow-up of the current corank block — `radial_morse_residual_power_le`
   engine (banked); Jacobian power `= block codim` (verified `= a`).
3. `Z`-independent unit block-elimination `Q,P` (det = 1) → reduce residual to `diag(1, D')`; advance
   `(S,J)`; append the radial to the shared `b_i` (extend `SJDecoration.support`).
4. recurse on the reduced block × downstream product (fresh shorter chain).
Terminate at `S=L+1`: loss `= Σ b_i²` on a finite cover, each chart `(monomial)²·(unit ≥ c₀>0)`;
finiteness by `monomialIntegrand_integrable_of_lt` (coordinatewise `κ_i−2c'N_i>−1`), below threshold
since terminal exponents `= Mval ≥ minAdm` (banked `minAdmRec_eq_minAdm`; `0/171` monotonicity).

**Banked substrate (consumable now):** `radial_morse_residual_power_le`, `pivotChartCover_matBox_le_sum`,
`Case111`/`Case222` (`(2,2,2)` templates), `monomialIntegrand_integrable_of_lt`,
`monomialThreshold_ge_of_mult`, `minAdmRec_eq_minAdm`, `sjChargeUpdate_accum`, `sjSubordination`,
`sjBase1_freeMatrix`, `minAdm_leadWidth_mono`, `sjRunMin_antitone`; plus the steps-1–2 measure inventory
(realizes one Case-2 peel).

**Single hardest (bounded) brick:** the **general-`(L,S,J)` single-radial chart lemma at opaque widths
with the shared-support ledger** — lift `Case111/Case222` from `(2,2,2)` to arbitrary widths, proving
the transformed loss `→ reduced-chain × monomial radial factors` on the finite cover, with the Case-1
equal-run/shared-divisor merge (an existing-divisor center; ordinary chart, my Q2(iii)). Substantial
multi-tide labor.

**Mathlib gaps for BUILD:** NONE fatal. Resolution-of-singularities / blow-up / monomialisation are
ABSENT from Mathlib, but the native route substitutes the **banked radial engine + explicit charts**
for them — the whole point of R-BLOWUP is that it CONSTRUCTS the normal-crossing coordinates by explicit
charts rather than invoking abstract resolution. The only elementary missing lemma (`det(Q_bQ_bᵀ)=‖∧^q‖²`
= Cauchy–Binet) is **not needed** on the native route (it is the atom-route object).

**Tide-count estimate:** ~12–20 tides (opaque-width `Case111/Case222` lift ≈ 5–8; the recursive loss
identity + shared-ledger ≈ 4–6; the weighted base/endpoint wrapper ≈ 2–3; assembly + `π=∅` corollary
≈ 2–3). Possibly its own sub-expedition. **This matches "BUILD per mandate; multi-week+."**

## The CITE statement (if the operator chooses B)

**No new interface. No product-Gram-principalisation axiom.** R1-UPPER box-finiteness
(`RouteMBoxThresholdFinite M` = `∫ frobSq(prod)^{−c'} < ⊤` for `c' < ½·minAdm`) is exactly
`rlct ≥ ½·codim` (finiteness below threshold). This is delivered by the equality
`RlctInterface.cited_aoyagi_dln : rlct(lossDLN) = ½·codim` **already carried** (used by the payoff
`RlctPayoff.lean`, per CLAUDE.md). Discharge `routeMCore_threshold_lt_top` from it via the deepest-point
domination + the banked `routeMCore_le_matBox` reduction (a mostly-plumbing measure-theoretic step
connecting the box integral to the local zeta pole; that connective lemma is the only build). The
Watanabe-`≤` framing in the old Item-39 fallback is the wrong quantity/direction (regular-model ceiling,
= total param dim, not fibre codim) — the wall-review already corrected this; the equality
`cited_aoyagi_dln` is what does the work. **Cite-footprint UNCHANGED.**

---

## Decorrelated Codex (xhigh, hypothesis withheld — `codex/buildcite-{prompt,answer}.md`)

Fired on (B) with my leaning withheld (I framed both BUILD and CITE neutrally and asked for the
adjudication + cheapest discriminating test). Returned, INDEPENDENTLY:
- **VERDICT: BUILD (bounded).**
- Q1 **sequential-finite-cover-suffices** — "later charts pull back the shared tail `Z=W₁W₂` once, so
  both `TZ` and `δRZ` inherit the same new exceptional coordinates via the same generator-support map;
  simultaneous principalisation is only forced by the atom/Gram-det route, not this native blow-up."
- Q2 **transforms-stay-regular** — "`Q,P` divide only by pivot blocks made units in the active incidence
  chart, older decorations are passive monomial prefactors, the deeper product is absorbed to the right;
  no failing configuration."
- Its cheapest discriminating test = the sequential pullback through the `W₁|W₂` boundary with
  `det Q(0)·det P(0)` unit check + common terminal-monomial supports — **which is exactly what my
  `r1d_test2c.py` computes** (det = 1, shared `v`).
- **Confidence 0.72; most likely wrong via** "a product-depth Case-1/equal-run chart where `Q,P` remain
  analytic but MIX generators with different old `b_i`-supports, so the shared-support ledger is not
  closed under the regular elimination."

**Agreement:** full, on the verdict (BUILD), the mechanism (intrinsic-`Z` resolution, shared support,
absorbed-right regularity, atom-route = the only place simultaneous principalisation is forced), and the
discriminating computation. **The one place Codex flagged as its failure mode (Case-1 generator-mix
breaking ledger closure) I probed directly** (`r1d_test2c.py` [iii]): the δ-prefactor is a passive
higher-order perturbation, the elimination is unipotent, leading support preserved — the ledger stays
closed on the representative instance. This raises confidence but does not close the general-width chart
lemma (which stays the substantial bounded brick).

---

## OPERATOR-facing summary (one paragraph)

R1-UPPER box-finiteness is **BUILD-viable with NO cite-footprint change either way.** The scary
"product-Gram principalisation" is a *trap of the atom route* (integrate the block out → a
determinantal-variety resolution Mathlib lacks); the **native Aoyagi R-BLOWUP depth recursion avoids it
entirely** and is break-it-down-buildable on the banked radial/chart engine — I verified, with exact
matrix algebra, the one previously-unchecked case (corank-2 coupling to a genuine deeper PRODUCT): the
deeper factor's rank loci are intrinsic (coupling-row-independent), so one finite sequential chart cover
resolves both coupled terms with the shared support closed under the (unit, det-1) block-elimination;
decorrelated Codex reached the same BUILD verdict independently (conf. 0.72, and its named residual risk
— the Case-1 generator-mix — I probed and found bounded). **So the choice is: (A) BUILD the native
recursion (mandate default, ~12–20 tides / possible sub-expedition, removes the finiteness's dependence
on the cite, residual risk = the bounded general-`(L,S,J)` chart lemma) vs (B) rest the finiteness on
the ALREADY-carried `cited_aoyagi_dln` (the same Aoyagi `rlct=½·codim` the payoff cites — near-zero
cost, footprint unchanged).** UPDATE-690's "(B) = add a 2nd cited interface (footprint change)" is
over-stated: no second interface, no new axiom — the CITE fallback is the status quo. Recommend BUILD
per mandate, scoped as its own sub-expedition, with CITE as the honest zero-cost retreat if the general
chart lemma over-runs.

---

## Closing (registers)

- **Firmest (Claim, exact-verified).** The native R-BLOWUP depth recursion reaches normal crossing for
  the corank-2 deeper-PRODUCT coupled core on a finite explicit sequential chart cover: the shared
  factor's rank loci are intrinsic (Test 2b), the deeper exceptional divides both coupled terms
  (Test 2c[ii]), the block-elimination is unit and Z-independent (Test 2c[i]), and the Case-1 row-mix
  preserves the shared support (Test 2c[iii]). The atom-route Gram-det of the product IS `B`
  (Test 1[1d] + Mathlib recon) but is an avoidable trap.
- **Most likely to break it (the one thing to watch).** The general-width chart lemma's shared-support
  closure across ALL equal-run partitions (Codex's 0.72 failure mode) — if a formaliser finds an
  opaque-width Case-1 configuration where the regular elimination genuinely needs a simultaneous move,
  THAT (not the atom's Gram-det) would be the wall, and the retreat is the zero-footprint CITE. My
  computation makes this unlikely on the representative instance but does not prove the general case.
- **Next construction to settle the open part.** Run the sequential pullback on the full `(3,3,3,4)
  t=(1,0,0)` matrices (not the reduced skeleton) through both boundaries, listing terminal monomial
  supports + `det Q(0) det P(0)` at each — the direct opaque-width analog of `r1d_test2c.py`. If it
  reaches `Σ b_i²` with `rlct = 7/2` and unit transforms, the general chart lemma is de-risked for the
  first genuine deeper-product corank-2 witness; that is the cheapest thing to do before committing the
  multi-tide BUILD. *(Speculation registered; the Lean route is the controller's.)*

### DATA index (mine — exact, separated from Codex interpretation)
- `r1d_witness.py` — smallest deeper-product corank-2 witnesses; `minAdm` anchors reproduced
  (`(2,2,2)=3`, `(3,3,4)=8`, `(4,4,2,2)=4`). `(3,3,3,4) t=(1,0,0)`: layer-1 corank 2, deeper product,
  `minAdm=7`.
- `r1d_test1.py` — `(2,2,2,2)` incidence identity EXACT; one-shot/atom residual non-unit; depth-recursion
  fresh core; atom product-Gram extra-vanishing `(w₁+kw₂)²(c₁₁²+c₁₂²)`.
- `r1d_test2b.py` — deeper-product coupling: `Z`-intrinsic rank loci (`det W₁ · det W₂`,
  `T,R`-independent), one chart cover for both coupled terms.
- `r1d_test2c.py` — (i) `det P=det Q=1` Z-independent; (ii) shared deeper exceptional `v` divides both;
  (iii) Case-1 row-mix unipotent, support preserved; (iv) toric shared-vs-separate (0.5 vs 1.5 at
  3 layers).
- `r1d_theta.py` — the `Θ(M,π)=½·minAdm(remChain π)` collapse (deliverable A), `3592/3592` over all
  admissible prefixes of all width-`1..4` 4-chains.
