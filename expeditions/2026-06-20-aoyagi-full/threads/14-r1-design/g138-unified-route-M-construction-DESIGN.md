# Unified general Route M construction — the `resolution_charts` blueprint (pp-hall, 2026-06-22, #138)

**The heart of the hero-task mountain.** The wall is lifted; this reconciles the witness leg (#132/#134,
ROUTE-HOLDS + the (S-min) sharpening) with pp3's obstruction leg (#136, C1–C4 + the heterogeneous-node
taxonomy) into the UNIFIED general Route M construction DESIGN that fm3+crux2 formalise for
`resolution_charts` (`rlctAtOn(dlnLoss M 0) 0 = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)`). Decorrelated design
check fired (Codex gpt-5.5 xhigh, contract-shaped — folded below when landed).

## Reconciliation up front: what pp3's C1–C4 corrects in my witness leg
My #132 was right on the VALUE (no missed branch, no undershoot, terminating) and pp3 CONVERGED on that.
But pp3 correctly sharpens two of my framings — adopt both:
- **#132 OVERCLAIMED "`k_E = 1` on every exceptional divisor."** True for **per-factor rank-defect**
  blow-ups (my multilinearity: scaling one factor by `x` ⟹ `F` degree-2 in `x`), but **FALSE at
  normal-crossing-completion / intersection blow-ups** (pp3 C3 witness `(1,1,1)`: `f=x²y²` blown up at the
  origin `(x,y)=(u,uv)` → `u⁴v²`, `k_E(u)=2`). There the Jacobian discrepancy `h` compensates so the RATIO
  stays `codim/2`. **The sound lower bound is the multiplicity-control inequality `m·k ≤ h+1`
  (`monomialThreshold_ge_of_mult`, green), NOT `k_E=1`.** (Verified `g137_reconcile.py`.)
- **#132/#134's "blow up the first factor's rank-defect" is INCOMPLETE.** A rank drop can be in a LATER
  factor while the first factor is full rank (pp3 C2 witness `(1,2,1)`: `C¹=(x₁,x₂)` full rank but
  `C¹C²=0`, the missed stratum `Mval=1` is the minimiser). **Need the full-rank pass-through Schur chart.**
  (Verified `g137_reconcile.py`.)
Both corrections keep the value `rlctAtOn(core) 0 = ½·minAdm Mval`; they fix the CONSTRUCTION.

## §0 — the target (core-only, levels separate)
`resolution_charts M : rlctAtOn(dlnLoss M 0) (0 : Params M) = ⨅ᵢ monomialThreshold (dᵢ)(kᵢ)(hᵢ)`, on the
**reduced widths** `M = H − r` (the singular core). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is L2/Fubini
(`product_reduction`), NOT here. The value side `⨅ = ofReal(lambdaCore M)` is A1's job; R1 builds the
chart family `(ι, d, k, h)` whose `⨅` realises it.

## §1 — the NODE TAXONOMY (the branch logic, over layer structures)
**(AMENDED after the decorrelated Codex design check — see §1.5: the first-pass 4-type taxonomy was NOT
exhaustive; a fifth MIXED node is required.)** At a node (a matrix-chain core `‖C_L⋯C_1‖²` at its origin),
classify by the **active layer**, with rank-defect/full-rank read **relative to the active prefix image**
(Codex fix 1: `rank t_{s-1}` incoming), into one of: separating (C4), pure coupled-defect (C1), pure
full-rank-pass-through (C2), or **MIXED partial-drop (C5)** when `t_{s-1} > t_s > 0`. C3 (NC-completion) is
a divisor-arrangement post-pass, not a node type. {C4, C1, C2, C5} partition the active-layer structure.

- **C1 — coupled rank-defect blow-up** (the MONOMIAL mechanism, the live route; the squeeze is OFF-PATH,
  §1.6, decision C / g134). **TWO steps per node** (fm3's ΣM caveat, #36): the blow-up carries the weight,
  the EXACT Schur-descent carries the `ΣM`-drop.
  **(A) `pivotBlowupOn active p`** of the rank-defect center (a smooth coordinate subspace `{pivot-block=0}`,
  NOT the determinantal variety): `core ∘ φ = x_p²·Q`, Jacobian `|x_p|^{card−1}`. **The `x_p²` is the
  EXCEPTIONAL DIVISOR** — `(k,h) = (1, card−1)`, ratio `card/2` via `axisRatio_regularSeq`, **ACCOUNTED by
  `monomialThreshold`, NOT stripped** (`x_p²` vanishes on `{x_p=0}`, NOT a unit; g141). **Step A does NOT
  drop `ΣM`** — the hard-pivot-normalized residual `Q = ‖Â·A2‖²` has the SAME dimensions `M` (`Â` a full
  `M_0×M_1` matrix; g143).
  **(B) the EXACT det-unit Schur-descent** (the `lemma2Fwd` generalization — a concrete det-`±1` c-o-v,
  lintegral-level splice, NO Jacobian, NOT a two-sided bound): the unit-pivot row/col ops clear `Â`'s pivot
  row+col (`L·Â·R = blockdiag[1, S]`, `S = D − b·a`), giving `[regular pivot row] + ‖S·A2red‖²` with
  `‖S·A2red‖² = dlnLoss M' 0`, `M'_0 = M_0−1`, `M'_1 = M_1−1`. **THE `ΣM`-DROP IS HERE** — `ΣM' = ΣM − 2 <
  ΣM` (`Σdrop = 2 > 0`, the `ChainDimSplit.measure_drops` shape; g143). **(C) RECURSE** on the strictly
  smaller core `‖S·A2red‖²` via the dispatcher (`lex` terminates via step-B's `Σdrop`). The squeeze
  `flatCore − Φ ∈ ideal(E)` (#131) is the OFF-PATH BOUND (drops the `x_p²` weight, §1.6) — step B is the
  EXACT change, NOT the squeeze. **Constructibility of the general exact Schur-descent (vs the
  rank-deficiency that blocked the SQUEEZE) is the crux2 check, held** (#35/#36); if it does not generalize,
  C1 falls back to iterated blow-up (the cover handling chart-locality) — but step B is the intended
  `ΣM`-drop mechanism. The squeeze `flatCore − Φ ∈ ideal(E)` (#131) is
  PARKED off-path — NOT C1's mechanism (it drops the `x_p²` weight, §1.6).

- **C2 — full-rank pass-through** (pp3's catch; the later-factor drop).
  The active factor is FULL rank on the prefix image but the product still drops rank (the drop is
  downstream). **DESCEND on the downstream chain `C_{>s}` (restricted to `im(C_s)`)** — the rank-defect is
  downstream, so the dispatcher recurses on `C_{>s}` (the full-rank factor's coords ride as spectator/
  regular coords, or get their own `pivotBlowupOn` if their block is itself singular). **DEPTH `L` drops**
  (the factor is consumed), `ΣM` need not. NOT a det-unit GL absorption — at the deepest point `C_s → 0`
  so `det(C_s) → 0` is NOT a unit (g142); the correct C2 is the downstream-descent, same monomial frame as
  C1. Witness: `(1,2,1)`.

- **C3 — NC-completion (`k_E ≥ 2` allowed)** (pp3's correction to my `k_E=1`).
  A post-pass turning the union of per-factor exceptional divisors into a normal-crossing arrangement may
  need intersection blow-ups where one exceptional coordinate absorbs ≥2 factors' vanishing (`k_E ≥ 2`).
  The Jacobian discrepancy compensates: ratio stays `codim/2`. **No `k_E=1` assumption** — the lower bound
  is multiplicity-control `m·k ≤ h+1` throughout (robust to `k_E ≥ 2`). Witness: `(1,1,1)` origin blow-up.

- **C4 — Fubini pinch / separating layer** (pp3's branch; width-1 / rank-1 bottleneck / `s=0`).
  A width-1 inner layer (or a rank-pinch / empty-Schur node) makes the core a PRODUCT of separate smooth
  blocks: `‖C_{s+1}·C_s‖² = ‖C_{s+1}‖²·‖C_s‖²` at a rank-1 bottleneck (verified `(3,1,3)`,
  `g137_c4_lex.py`). Resolve by **Fubini product-min** (rlct of a product), NOT a coupled blow-up (which
  leaves an empty Schur complement and STALLS). Witness: `(2,1,2)`, `(3,1,3)`.

- **C5 — MIXED partial-drop node** (the Codex-found gap; `t_{s-1} > t_s > 0`).
  The active factor has a PARTIAL rank drop on the active prefix image: a rank-`t_s` **survivor** block
  (passes through later layers before being killed downstream) PLUS a rank-`(t_{s-1}−t_s)` **complement**
  (resolvable now). **Resolve by the block-column split**: `C_s` image `= survivor ⊕ complement`; the
  product splits as a column-independent block concatenation `[C_{>s}·survivor | C_{>s}·complement]`, the
  complement resolved by C1 (iterated `pivotBlowupOn` now) and the survivor by C2 (downstream-descent to
  its later kill-layer). C5 is the **C1+C2 composite** — BOTH iterated blow-up / recursion, **NO det-unit
  GL change** (the earlier "block-column det-unit to verify" concern is DISSOLVED, g142: C2 is
  downstream-descent not GL absorption). Witness: `t=(3,3,2,2,2,0)` (Codex; `g139_mixed_node.py`).

**Branch decision at a node** (the dispatcher fm3 builds; rank read RELATIVE TO THE ACTIVE PREFIX IMAGE):
1. if any inner layer is separating (width-1 / rank-1 pinch / forced `s=0`) → **C4** (Fubini split,
   recurse on each block);
2. else, on the active factor's rank on the incoming prefix image (rank `t_{s-1}`):
   - drops to `0` / fully coupled → **C1** (blow up, Schur, recurse, `ΣM` drops);
   - full rank `= t_{s-1}` (no drop here, later-factor drop) → **C2** (pass-through, `L` drops);
   - partial `t_{s-1} > t_s > 0` → **C5** (block-column split: complement via C1, survivor via C2);
3. on the accumulated exceptional divisors → **C3** NC-completion (intersection blow-ups, `k_E ≥ 2` ok),
   read `(k,h)` from the FULL pulled-back density on the strict transform of `{∏C=0}` (**C1-condition**:
   geometric codim `= Mval`, NOT the raw Jacobian/Hessian rank — the `(4,3,2)` thin-product trap).

## §1.5 — the Codex design check: the 4-type taxonomy was NOT exhaustive (MIXED node), three fixes
A decorrelated Codex design review (gpt-5.5 xhigh, conclusion withheld) found a genuine gap in the
first-pass {C1,C2,C4} taxonomy and forced three load-bearing fixes — all adopted (verified
`g139_mixed_node.py`). The catch and the fixes:
- **The missed node (C5):** `t = (3,3,2,2,2,0)`. Layer 2 has a partial rank drop `3→2`; the surviving
  rank-2 block passes through layers 3,4 (full rank) before being killed at layer 5. This node is NOT C2
  (active factor not full rank on the prefix), NOT C4 (survivor rank 2, not a width-1 pinch), NOT C3 (NC
  only), and NOT C1 *as stated* (the single Schur step does not give "regular squares + reduced chain" —
  the survivor is not regular until the later layers pass). ⟹ a fifth **MIXED** node (C5 above) is
  required; the first-pass taxonomy was not exhaustive. This corrects my §"most likely to break" hedge —
  the mixed node is real, not merely a risk.
- **Fix 1 (rank relative to the active prefix image):** "full rank" / "rank defect" must be read on the
  INCOMING prefix image (rank `t_{s-1}`), not the global matrix rank — so a partial drop `t_{s-1}>t_s>0`
  is the well-defined C5 case (neither global-full nor global-zero). Adopted in the §1 branch decision.
- **Fix 3 (C3 termination invariant):** NC-completion blow-ups need NOT change `L` or `ΣM`, so `lex(L,ΣM)`
  alone does not bound C3. Add a third lex component `ncDefect` = the number of non-normal-crossing
  exceptional intersections (strictly drops per NC blow-up). Termination measure becomes
  **`lex(L, ΣM, ncDefect)` on `ℕ³`** (§3 amended).
- **Fix 4/5 (value robustness):** the multiplicity-control `m·k_E ≤ h_E + 1` must be proved for ALL
  divisors including C5/mixed and C3 centers (Codex confirms the NC-intersection case: `k_E = Σ k_i`,
  `h_E+1 = Σ(h_i+1)`, so the ratio is a weighted average — cannot undershoot); and the `(C=∃)` achiever
  must select an actual leaf path to the minimiser, where the minimiser may itself be a mixed/C5 stratum.
  Both fold into §2 — `(C≥)` is uniform over all four node types, `(C=∃)` is the `(S-min)` achiever.

## §1.6 — the SQUEEZE is OFF-PATH (decision C / g134); C1's mechanism is MONOMIAL (controller correction)
The first draft of this design (concurrent with the squeeze adjudication) described C1's mechanism as the
SQUEEZE (#129/#131): `c₁·Φ ≤ flatCore ≤ c₂·Φ`, additive `Φ = (nReg regular squares) + ‖S·A2red‖²`. **That
mechanism is OFF-PATH** — triple-decorrelated (decision C / g134: fm3 STOP + crux2 CONCESSION + rv3 + Codex
+ sympy):
- `dlnLoss ∘ pivotBlowupOn = x_p²·Q` is a PRODUCT; `x_p²` **vanishes** on `{x_p=0}` (NOT a unit, g141), so
  the squeeze + `rlctAt_mono` (which strips only genuine units, the `c₁,c₂` constants) cannot remove it —
  doing so DROPS the exceptional weight. A squeeze/det-1-only recursion conserves dimension ⟹ telescopes to
  ambient/2 = 4 for `(2,2,2)`, NOT `3/2` (the g32 dimension-conservation death).
- **The LIVE route is MONOMIAL** (C1, §1): step A `pivotBlowupOn` → `x_p²·Q` (`x_p²` the accounted
  exceptional divisor, `(k,h)=(1,card−1)`; step A does NOT drop `ΣM`) + step B the EXACT det-unit
  Schur-descent (`lemma2Fwd` generalization, NOT the squeeze/bound) which removes the pivot row+col (`ΣM`
  drops by 2, g143) + step C recurse. The `ΣM`-drop is step B (fm3's #36 caveat); the squeeze is the
  off-path bound, NOT step B's exact change.
**The #131 squeeze (`schur_node_squeeze` / `flatCore − Φ ∈ ideal(E)`) and `lemma2Fwd` are both PARKED
off-path / `(2,2,2)`-specific** — the squeeze is a sound analytic fact but drops the `x_p²` weight;
`lemma2Fwd` is the `(2,2,2)` presentation. Neither is C1's general mechanism. (The #140 framing calling the
squeeze "the straighten's content", and my prior fix calling C1 "blow-up + `lemma2Fwd`-generalized
straightening", are BOTH superseded: C1 is ITERATED `pivotBlowupOn` + recurse.) The value machinery (§2)
was already monomial; C1's internal step is iterated blow-up + recursion.

## §2 — the chart family `(ι, d, k, h)` + the (S-min) value argument
- **`ι`** = the root-to-leaf PATHS of the branch tree (Fintype: finite branching × finite depth by §3
  termination). `d_i` = the chart dimension; `(k_i, h_i)` = the per-divisor `(F-vanishing, Jacobian)`
  exponents read off the chart (C1-condition: from the full pulled-back density on the strict transform).
- **The value via `(S-min)` + `le_antisymm`** (my #134 sharpening, the formaliser-clean route):
  - **(C≥) uniform lower bound:** `∀ i, ½·(minAdm Mval) ≤ monomialThreshold (d_i)(k_i)(h_i)`, via
    `monomialThreshold_ge_of_mult` (green) with `m = minAdm Mval` and the **multiplicity-control**
    `m·k_{i,j} ≤ h_{i,j}+1` per divisor (C3-robust: holds for `k_E ≥ 2` too — this is THE place pp3's C3
    bites, and the green lemma already takes general `k`). Needs every center admissible (codim is some
    `Mval(T) ≥ minAdm`) — the C1-condition geometric-codim read.
  - **(C=∃) one achiever:** `∃ i, monomialThreshold (d_i)(k_i)(h_i) = ½·(minAdm Mval)`, the path to the
    **minimising stratum**'s binding divisor (`(k,h)=(1, Mval−1)`, ratio `Mval/2`), via
    `monomialThreshold_le_regularSeq` (green). This is the **(S-min)** residual: ONE path reaches a
    minimiser. NB the minimiser is generally NOT the generic stratum — `(2,2,2)`: the rank-1 incidence
    stratum (codim 3), reached at depth 2 (the C1 step on the residual after the first blow-up).
  - `⨅_i monomialThreshold = ½·minAdm Mval = ofReal(lambdaCore M)` by `le_antisymm`. **This replaces
    `IsResolutionAtlas`'s per-path `threshold_eq` (the #133 binding-center form) by `(C≥)` + `(C=∃)`** —
    drops the stratum-as-binding-center fiddliness; full `stratum_surjective` becomes the conceptual
    statement, `(S-min)` the load-bearing minimum.

## §3 — TERMINATION: lex(depth `L`, `ΣM`, `ncDefect`) on `ℕ³` (pp3 hdrops-fix + Codex C3-fix)
The measure is **`lex(L, ΣM, ncDefect)` on `ℕ³`** (well-founded), `ncDefect` = # non-normal-crossing
exceptional intersections:
- **C1** (coupled Schur): `L` same, `ΣM` strictly drops (Schur removes the resolved pivot row+col;
  `ChainDimSplit.measure_drops`, green, needs `Σdrop > 0`).
- **C2** (full-rank pass-through): `L` strictly drops (a factor consumed); `ΣM` need NOT drop — the
  **DEPTH drop** carries it (the case `ΣM`-alone fails, `Σdrop = 0`).
- **C5** (mixed): decomposes into a C1 micro-step (complement, `ΣM` drops) + a C2 micro-step (survivor,
  `L` drops); each micro-step strictly decreases `lex(L, ΣM)`, so the node terminates.
- **C4** (Fubini split): each child block has strictly smaller `L` (the split severs the chain).
- **C3** (NC-completion): `L`, `ΣM` may be UNCHANGED, but `ncDefect` strictly drops per intersection
  blow-up (Codex fix 3) — the third lex component bounds it.
- **base** `L = 1`: `F = ‖C_1‖²` a pure smooth block, `rlct = (#entries)/2`, terminal.
No stuck node: a nonterminal node is C1/C2/C4/C5 (each drops `lex(L,ΣM)`) or a C3 NC-pass (drops
`ncDefect`). (pp3 10+ shapes; my #132 trace; `g137_c4_lex.py` + `g139_mixed_node.py`.)

## §4 — how Case222's explicit tree generalizes ((2,2,2)-specific vs general)
The `(2,2,2)` build (`Case222CoverGE`, 24 leaves) is the concrete template; the general construction
parametrises it over `M`:
| (2,2,2)-specific | general-M analogue |
|---|---|
| fixed 3-blow-up tree (`Z_A` codim4 → `Z_B` codim4 → incidence codim3) | the C1/C2/C4 branch tree, depth = `lex`-bounded, parametrised over `M` |
| the explicit incidence chart `A=α[[1,a],[b,ab+δ]]`, `B=[[u−ar,…]]` | the general node = `pivotBlowupOn` (step A, `x_p²` weight, ΣM unchanged) + EXACT Schur-descent (step B, `S=D−ba`, ΣM−2) + recurse (step C) |
| all 24 leaves' threshold `= 3/2` (a coincidence of `(2,2,2)`) | leaves' thresholds VARY; only the `⨅ = ½·minAdm` via `(C≥)`+`(C=∃)` is general (NOT all-equal) |
| `lemma2Fwd` det-`±1` one-shot splice | the per-node EXACT det-unit Schur-descent (step B, the `ΣM`-drop: removes the pivot row+col, `S=D−ba`) — `lemma2Fwd` generalized to a det-`±1` c-o-v (NOT the squeeze/bound); general constructibility = the crux2 check (#36) |
| conjugation symmetries σ1/σ2/σ3 (S₂-style) | the layer symmetry group; OR the C2/C4 branches cover non-pivot summands without conjugation |
| `r = 1`, `B = 0` | general `r` (D1 shifts the regular part; the core at general `r` is the C1/C2/C4 tree) |
**What is reusable as-is** (g3 memo + my reconciliation): the `recStep`/`g5_pivotNode` cover engine
(`{N}`-generic), the box/Tonelli/monomial toolkit, the S1 transport substrate, `Adm`/`Mval`/`lambdaCore`
(A1, general), the green `monomialThreshold_ge_of_mult`/`_le_regularSeq`. **What is the general lift:** the
C1/C2/C4/C5 dispatcher + the general node (step A `pivotBlowupOn` `x_p²` weight + step B EXACT Schur-descent
`ΣM`-drop + step C recurse) + the `(S-min)` achiever path. The g3-memo risk #1 (the "regular-change
generalization") is the **crux2 constructibility check** (#36): does the EXACT det-unit Schur-descent (step
B, `lemma2Fwd` generalized) construct generally vs the rank-deficiency that blocked the squeeze? If yes,
C1 is the both-steps node; if not, C1 falls back to iterated blow-up. The residual is the dispatcher
exhaustiveness + step-B constructibility + the `(S-min)` achiever.

## §5 — the formaliser interface (what fm3+crux2 build, #27)
1. **`RouteMNode` dispatcher** — classify a node into C1/C2/C4/C5 (+ C3 post-pass); the branch logic of §1,
   rank read RELATIVE TO THE ACTIVE PREFIX IMAGE (Codex fix 1). Exhaustiveness over layer structures is the
   one combinatorial obligation.
2. **Per-branch chart + `(k,h)`** — C1 (both steps, #36): step A `pivotBlowupOn active p` (`core∘φ = x_p²·Q`,
   the `x_p²` exceptional divisor `(k,h)=(1,card−1)`; `step1A_eq_pivotBlowupOn`/`step2E_eq_pivotBlowupOn`
   banked; ΣM unchanged) + step B the EXACT det-unit Schur-descent (`lemma2Fwd` generalized,
   `measurePreserving_lemma2`; removes pivot row+col, ΣM−2; NOT the squeeze — crux2 constructibility check
   #36) + step C recurse; C2: the downstream-descent (recurse on `C_{>s}|im(C_s)`, `L` drops — NOT a det-unit GL absorption, g142); C4: the Fubini product split
   (`(2,1,2)`-style); C5: the block-column split → C1 micro-step (complement) + C2 micro-step (survivor).
   C3: NC-completion intersection blow-ups (`k_E ≥ 2` ok, `ncDefect` drops). Read `(k,h)` from the
   strict-transform density (C1-condition). **The squeeze `schur_node_squeeze` AND `lemma2Fwd` are PARKED
   off-path / `(2,2,2)`-specific — NEITHER is a general per-node chart mechanism (C1 = iterated blow-up).**
3. **The value** — `(C≥)` via `monomialThreshold_ge_of_mult` (multiplicity-control `m·k ≤ h+1`, proved for
   ALL divisors incl. C5/C3 — Codex fix 4) + `(C=∃)` via `monomialThreshold_le_regularSeq` (the `(S-min)`
   achiever path to the minimiser, which may be a C5/mixed stratum — Codex fix 5) + `le_antisymm`.
4. **Termination** — `lex(L, ΣM, ncDefect)` well-founded recursion (§3).
5. **Assemble** `resolution_charts` from 1–4.

## The one combinatorial obligation that remains (named precisely)
Everything reduces to **dispatcher exhaustiveness** + the **`(S-min)` achiever**:
- **(Exh)** every nonterminal node is exactly one of C1/C2/C4/C5 (active layer separating ⟹ C4; else, on
  the active factor's rank on the prefix image: fully-coupled ⟹ C1, full-rank ⟹ C2, partial `t_{s-1}>t_s>0`
  ⟹ C5), with C3 the NC post-pass — exhaustive over layer structures. The C5 mixed node closes the gap
  Codex found in the first-pass {C1,C2,C4}. This is the rank-pattern combinatorics of `{∏C=0}` (the Core
  `RankPattern`/`OrbitKostant` carrier); the C5 block-column split is the one new mechanism.
- **(S-min)** one branch path reaches the minimising stratum `T* ∈ argmin Mval` (the binding divisor,
  ratio `Mval(T*)/2`). The minimiser is realizable (`Core.baseChange_normalForm`) and reached by the
  binding branch (depth-bounded). The seam is `prefix : RealizableRank M → Adm M`. NB the minimiser may be
  a mixed/C5 stratum (Codex fix 5) — the achiever path must thread C5 nodes.
Both live on the `Core` rank-pattern lattice — the quiver-orbit↔rank-pattern translation does the
load-bearing combinatorial work, the value side rides the green `monomialThreshold` lemmas.

## Most likely thing to break this (revised post-Codex, multi-drop CHECKED)
With C5 added, the dispatcher is exhaustive over single partial-drop structures (Codex's stress). The
multi-drop worry (≥2 layers partially dropping at once, e.g. `t=(3,2,2,1,0)` with drops at layers 1 and 3)
is now CHECKED and DOWNGRADED (`g139_multidrop.py`): multi-drop **linearises** into iterated single-layer
C5 — process the leftmost drop as a C5 node (complement via C1, survivor via C2), and the remaining drops
descend into the reduced chain, each handled at its own recursion level. One active layer per level; the
left-to-right order works because the Schur/pass-through at layer `s` produces a reduced chain whose
layers `> s` retain their relative drops. So multi-drop is NOT a new mechanism — it is the recursion
serialising single-layer C5 steps, each `lex`-decreasing.
The genuine residual is now just the **#27 formalisation induction** (prove the dispatcher total +
exhaustive for all `M` by induction on `lex(L,ΣM,ncDefect)`) and **(Exh)/(S-min)** as Lean obligations —
no open *mechanism* remains, and (correcting an earlier flag) **no det-unit step to verify**: under the
iterated-blow-up frame every node (C1/C2/C4/C5) is blow-up + recursion (the `(pivot)²` monomial weight),
with NO det-unit GL absorption anywhere (g142 — C2 is downstream-descent, not GL; C5 inherits that). The
one thing to confirm in Lean: the block-column split's column-independence (C5) is a clean `Finset`
partition of the active factor's columns into survivor/complement — flagged for the C5 chart construction.

## Decorrelation + provenance
Witness leg #132/#134 (ROUTE-HOLDS, (S-min)) + pp3 obstruction #136 (C1–C4, two sharpening witnesses) +
two Codex passes (#132 math, #136 own) CONVERGED on the value; this design folds pp3's C1–C4 corrections
into my taxonomy (k_E≥2 via mult-control not k_E=1; pass-through for later-factor drops; Fubini for pinches;
geometric-codim read). A fresh decorrelated Codex design check on the taxonomy exhaustiveness + lex
termination is fired (`codex/g138-routeM-{prompt,answer}.md`) — folded when landed. Scripts: `g137_*` in
`g129-scripts/` (reconcile, C4+lex, `g141_offpath_confirm`, `g142_residual_smaller`, `g143_both_steps`). **Controller correction (§1.6, decision C / g134; refined #36):** C1 = TWO steps — step A `pivotBlowupOn` (`x_p²` weight, ΣM unchanged) + step B EXACT det-unit Schur-descent (`lemma2Fwd` generalized, the ΣM-drop; NOT the squeeze, which is the off-path bound) + step C recurse. Step-B general constructibility = the crux2 check (#36). Builds on g134/decision-C, #132/#134 (witness + S-min), #136 (pp3 C1–C4), fm3's case222 map (uniform `pivotBlowupOn` node),
r1-design §1-4 (the value-match + the two proof routes R3a/R3b), `Core.RankPattern`/`OrbitKostant` (carrier).
