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

- **C1 — coupled rank-defect blow-up** (the #127/#129/#131 squeeze step, the main case).
  The active factor has a genuine rank-defect coupling to the next factor. Blow up the rank-defect center
  (a smooth coordinate subspace `{pivot-block = 0}`, NOT the determinantal variety); in each affine chart
  a HARD-unit pivot appears (post-blow-up). The Schur step decouples (SQUEEZE form, #129/#131):
  `c₁·Φ ≤ flatCore ≤ c₂·Φ`, `Φ = (nReg regular squares) + ‖S·A2red‖²`, `S = D − b·a`,
  `flatCore − Φ ∈ ideal(E)` (the regular gens). Descend on `‖S·A2red‖² = dlnLoss S.red 0`. `ΣM` drops.

- **C2 — full-rank pass-through Schur** (pp3's catch; the later-factor drop).
  The active factor is FULL rank but the product still drops rank (the drop is downstream). Pass the
  full-rank factor through (absorb it via its invertible action — a measure-preserving GL change on the
  next factor's coords, det a unit), descending on the reduced chain so the later-factor drop is resolved.
  **DEPTH `L` drops** (the factor is consumed), `ΣM` need not. Witness: `(1,2,1)`.

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
  (which passes through later full-rank layers before being killed downstream) PLUS a rank-`(t_{s-1}−t_s)`
  **complement** (Schur-reducible now). The active factor is neither full-rank (C2) nor zero/clean-coupled
  in one Schur step (C1) — the survivor is not regular until the later layers are passed. **Resolve by the
  block-column split**: `C_s` image `= survivor (rank t_s) ⊕ complement (rank t_{s-1}−t_s)`; the product
  splits as a block-column concatenation `[C_{>s}·survivor | C_{>s}·complement]` (column-independent), the
  complement resolved by C1 (Schur now) and the survivor by C2 (pass-through to its later kill-layer).
  C5 is the **C1+C2 composite** at one node. Witness: `t=(3,3,2,2,2,0)` (Codex; `g139_mixed_node.py`).

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
| the explicit incidence chart `A=α[[1,a],[b,ab+δ]]`, `B=[[u−ar,…]]` | the general hard-pivot Schur chart (#127 `(L,R)` transvections, #131 `S=D−ba`) |
| all 24 leaves' threshold `= 3/2` (a coincidence of `(2,2,2)`) | leaves' thresholds VARY; only the `⨅ = ½·minAdm` via `(C≥)`+`(C=∃)` is general (NOT all-equal) |
| `lemma2Fwd` det-`±1` one-shot splice | the per-node SQUEEZE (#129/#131), NOT a clean factor — the corrected interface |
| conjugation symmetries σ1/σ2/σ3 (S₂-style) | the layer symmetry group; OR the C2/C4 branches cover non-pivot summands without conjugation |
| `r = 1`, `B = 0` | general `r` (D1 shifts the regular part; the core at general `r` is the C1/C2/C4 tree) |
**What is reusable as-is** (g3 memo + my reconciliation): the `recStep`/`g5_pivotNode` cover engine
(`{N}`-generic), the box/Tonelli/monomial toolkit, the S1 transport substrate, `Adm`/`Mval`/`lambdaCore`
(A1, general), the green `monomialThreshold_ge_of_mult`/`_le_regularSeq`. **What is the general lift:** the
C1/C2/C4 dispatcher + the per-node squeeze (now #131-certified) + the `(S-min)` achiever path. The g3-memo
risk #1 (the regular-change generalization) is RESOLVED by the squeeze; the residual is the dispatcher's
exhaustiveness + the achiever path.

## §5 — the formaliser interface (what fm3+crux2 build, #27)
1. **`RouteMNode` dispatcher** — classify a node into C1/C2/C4/C5 (+ C3 post-pass); the branch logic of §1,
   rank read RELATIVE TO THE ACTIVE PREFIX IMAGE (Codex fix 1). Exhaustiveness over layer structures is the
   one combinatorial obligation.
2. **Per-branch chart + `(k,h)`** — C1: the #131 hard-pivot Schur squeeze (`schur_node_squeeze`, green on
   fm2's branch) + the blow-up `pivotBlowupOn`; C2: the pass-through GL change (det-unit); C4: the Fubini
   product split (`(2,1,2)`-style); C5: the block-column split → C1 micro-step (complement) + C2 micro-step
   (survivor). C3: NC-completion intersection blow-ups (`k_E ≥ 2` ok, `ncDefect` drops). Read `(k,h)` from
   the strict-transform density (C1-condition).
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
no open *mechanism* remains. The one place to stay honest: the C5 block-column split's measure-preservation
(the survivor/complement basis change must be det-unit, like C2's pass-through) — assert it inherits the
#131 Schur det-unit property; verify in the C5 chart construction (the analogue of the #131 cert for the
block-column split) before #27 locks the C5 chart.

## Decorrelation + provenance
Witness leg #132/#134 (ROUTE-HOLDS, (S-min)) + pp3 obstruction #136 (C1–C4, two sharpening witnesses) +
two Codex passes (#132 math, #136 own) CONVERGED on the value; this design folds pp3's C1–C4 corrections
into my taxonomy (k_E≥2 via mult-control not k_E=1; pass-through for later-factor drops; Fubini for pinches;
geometric-codim read). A fresh decorrelated Codex design check on the taxonomy exhaustiveness + lex
termination is fired (`codex/g138-routeM-{prompt,answer}.md`) — folded when landed. Scripts: `g137_*` in
`g129-scripts/` (reconcile, C4+lex). Builds on #131 (squeeze), #132/#134 (witness + S-min), #136 (pp3 C1–C4),
r1-design §1-4 (the value-match + the two proof routes R3a/R3b), `Core.RankPattern`/`OrbitKostant` (carrier).
