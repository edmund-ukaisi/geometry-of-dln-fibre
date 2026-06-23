# C5 `hnode` constructibility at a deep MIXED node — WITNESS (pp, decorrelated, 2026-06-23)

- **Seat:** `pen-and-paper`. **Direction:** witness (exhibit the construction) — the decision gate for
  `routeStep`'s fate (formaliser-scale vs per-node-mechanism research).
- **Question:** is the per-cell blow-up Schur presentation `hnode` (the explicit hypothesis
  `schur_straighten_squeeze_exists` consumes) uniformly constructible at a deep MIXED (C5) partial-drop
  node `t=(3,3,2,2,2,0)`, with the reduced core a SINGLE chain and the pivot column → 0?
- **Decorrelation:** exact symbolic algebra (sympy, `loss − split = 0` verified) + hypothesis-withheld
  Codex (`codex/c5-hnode-{prompt,answer}.md`, VERDICT: WITNESS). Converged on WITNESS via two routes.
- **Scripts:** `r1-realizability-scripts/c5_*.py` (5 scripts).

## VERDICT

**WITNESS — the C5 `hnode` is uniformly constructible. The §4 gap is formaliser-scale (weeks), NOT a
per-node-mechanism research gap.** With ONE honest interface nuance (§4): the cleanest mechanism is a
smooth Fubini-shear (the rank-1 defect resolves as a REGULAR ½ direction), which is *simpler* than —
and a variant of — the existing hard-pivot `schur_node_squeeze_unif` interface. The single-reduced-chain
requirement holds; there is NO second core, NO new geometry.

## 1. The honest near-miss I hunted down (the role's "too clean" check)

A naive squeeze test passed `0 fails / 3000` — but it was a CONFOUND. It fixed the defect coordinate
`δ` small while sampling the survivor core `Φ` generic, missing the `Φ → 0` (deepest-point) behaviour.
The cross term `2δ·(Gq·e)` is `√Φ`-scale (`Gq ~ √Φ`, `e` bounded), so `loss/Φ = 1 + O(δ/√Φ)` BLOWS UP
as `Φ → 0` with `δ` fixed. **A fixed-`δ` bounded-pivot reading of the C5 node does NOT give a uniform
squeeze near the deepest point.** This killed the first (lazy) witness and forced the correct mechanism.

## 2. The correct C5 structure (exact, symbolic — `loss − split = 0`)

At a partial-drop node (incoming prefix rank `a`, active factor → survivor rank `b`, complement rank
`a−b`; the witness has `a=3, b=2`, complement rank 1), the block-LU of the active factor `A = L·U`
(`U = [[p,q],[0,δ]]`, `δ` = Schur complement = the rank-1 defect coordinate, `p` = survivor pivot
full-rank) gives, with the downstream `Ctil = Cnext·L = [G | e]`:

    loss = ‖G·p‖²(survivor)  +  ‖G·q + δ·e‖²(complement column)

The decisive move is the **smooth shear** `δ' := δ + (G·q · e)/‖e‖²` (invertible iff `‖e‖² ≠ 0`),
which EXACTLY diagonalises (verified symbolically, `c5_squeeze_retest.py`):

    loss  =  ‖e‖²·δ'²   ⊞   [ ‖G·p‖² + ‖G·q‖² − (G·q·e)²/‖e‖² ]
          =  [regular ½-square in δ']   ⊞   [the survivor's reduced-chain core, DISJOINT in δ']

- **The defect `δ` is a REGULAR direction** (`‖e‖²·δ'²`, a clean Morse ½), NOT a blow-up exceptional.
- **The survivor is ONE reduced chain** (the bracket = `‖G·survivor‖²` projected off the `e`-line) —
  carried forward, recursed. NO second core. The "block-column split" of g138 is a basis choice inside
  the single product `Cnext·A`, confirmed by exact Frobenius orthogonality `‖[X|Y]‖²=‖X‖²+‖Y‖²`
  (`c5_hnode_actual.py`, `diff = 0`).
- **The pivot `b → 0` (G2) holds** in the right basis: the survivor's non-vanishing entries lie in the
  survivor block/gauge, NOT the pivot column (Codex Q3 — concurs).

## 3. Why `‖e‖² ≠ 0` (the load-bearing assumption) holds per chart

`e = Cnext·(complement direction)`. At the node's defect-deepest (`δ=0`) the complement direction is
NOT in the active factor's image (that is where the rank drops), so `Cnext·A = 0` does NOT force `e=0`.
Where `e = 0`, the downstream ALSO kills the complement — a DEEPER rank-defect, handled on ANOTHER
branch of the recursion. The blow-up's chart cover (charts `e_i ≠ 0`, one per nonzero component = the
**full pivot atlas** / `pivotBlowupOn`) guarantees `‖e‖² ≠ 0` PER CHART. This is the standard,
finite, exhaustive chart cover already used at C1 nodes — not new machinery.

## 4. The interface nuance (honest, for the formaliser)

Two equivalent mechanisms land at the same value; they need DIFFERENT (both formaliser-scale) Lean
interfaces:

- **My Fubini-shear route:** the rank-1 defect → a regular ½ via the smooth shear `δ'`. This is a
  **Fubini/shear node** (regular generator ⊞ reduced core), like the C2/C4 family — NOT the C1 squeeze.
  Interface: a measure-preserving shear (det-1) + the spectator-peel `rlctAtOn(reg ⊞ core) = ½ + rlctAtOn(core)`
  (the S1-Fubini idiom already in the library, `measurePreserving_coreShear`, `rlct_additive_smooth_block`).
- **Codex's hard-pivot route:** blow up the complement, normalise `e` to a unit, and the loss takes the
  literal `schur_node_squeeze_unif` form `ΣE² + Σ(b·E+SΓ)²` with the survivor as `SΓ`, `b→0` (Codex
  Q1/Q2 [FACT]). Interface: the EXISTING `schur_straighten_squeeze_exists` `hnode`, reused verbatim.

**Node count + the (C≥) on iterated intermediates (pp2 g224/g225, decl-grounded).** The banked
`schurState` drops 1 per pivot vertex per step (rank-1 peel), so a full rank-`b`→0 drop is `b` iterated
rank-1 C1 nodes (NOT one rank-`b` node). For the witness `t=(3,3,2,2,2,0)`: **3 divisor nodes** (1 C5 at
`s=3`, 2 iterated rank-1 C1 at `s=6`) + 4 C2 gauge nodes; uniform per-step `ΣM`-drop = 2. This is
value/termination-neutral (verified, `c5_c1_iterated.py`/`c5_codim_consistency.py`). The (C≥) on the
iterated INTERMEDIATE strata is **automatic** (pp2 g225): every intermediate the iterated path crosses
is a weakly-decreasing rank vector through the bottleneck ⟹ admissible ⟹ `Mval(M₀, T_int) ≥ minAdm(M₀)`
BY DEFINITION of `minAdm = inf over Adm`. So the iterated steps' `PivotWitness` strata (the intermediates,
not just the endpoints) all satisfy C≥ with no extra work; the binding (`= minAdm`) is hit only at the
achiever `T*`.

Both are **single-reduced-chain**, both formaliser-scale. The Codex route reuses the proven lemma as-is
(no new interface) — likely the cheaper Lean path. The shear route is conceptually cleaner (the defect
is genuinely regular, not a blow-up) and may simplify the codim bookkeeping (a rank-1 partial drop adds
ONE regular ½, matching the `Mval` increment).

## 4b. Cascade alignment — pp2's g219 is the realization skeleton (decorrelated convergence)

pp2 (g219, `#96` seed `f4b3fc9`) independently proved `Adm M = RealizableRank M` via the **canonical
diagonal cascade** `C_s = diag(1^{t_{s+1}}, 0)` (running partial-product rank `= t_j`, valid iff
`t_{s+1} ≤ min(t_s, M^{s+1})` = admissibility), landing on the SAME achiever-only verdict (T* realized
by its cascade; NOT full `stratum_surjective`). Cross-checked exactly at `t=(3,3,2,2,2,0)`
(`r1-realizability-scripts/c5_cascade_hnode_match.py`):

- The cascade ranks reproduce `[3,3,2,2,2,0]` ✓. The C5 step (`3→2`) is the cascade block
  `diag(1,1,0)`: the two surviving `1`s ARE my survivor block (rank 2, recurses); the dropped 3rd
  coord IS my complement (rank 1, resolved by the shear). The cascade's per-step rank-drop sequence
  DICTATES the `ChainDimSplit` sequence `routeStep` emits; my per-node hnode is the analytic chart at
  each cascade node.
- **One realization, two layers:** cascade = combinatorial skeleton (`rankFn(cascadeTuple M T*) = T*`),
  hnode = analytic flesh (each node's local resolution takes the hnode form). Together they give the
  achiever leaf reaching `minAdm` with the right divisor codims → `foldFamily_iInf_eq_half_minAdm`
  closes the value. The Lean grind is: pp2's cascade realizer + the 1-index↔2-index `rankFn` reindex
  (pp2 owns) + my per-node hnode chart (this cert) + the achiever-leaf wiring into `routeMIota`.

**CONVERGENCE CONFIRMED (pp2, post-cross-check).** pp2 read this cert and confirmed the C5 shear
*refines* its g194 C1-complement: my survivor-core = pp2's C2-survivor (one chain); my `‖e‖²·δ'²`
defect = pp2's C1-complement, and for the **rank-1 defect the exact shear gives a REGULAR ½ directly**
— cleaner than a `pivotBlowupOn` exceptional (the rank-1 complement is a smooth Morse, not a blow-up).
pp2's answers pin the coordination: (Q2) the cascade is a SINGLE deterministic descent per `T` (NOT
branched within a `T`; the branching = which `T`, in `routeStep`); for `T*` the cascade's drop-sequence
`t_0→t_1→…→0` IS the `ChainDimSplit` chain, my hnode the chart at each node. (Q3) at a partial drop
`C_s = diag(1^{t_{s+1}},0)` zeroes the `(t_s−t_{s+1})` complement directions, keeps the `t_{s+1}`
survivor — exactly my survivor⊕complement. **I implement pp2's cascade drop-sequence; my hnode is the
per-node chart. NOT a parallel cascade.** The `e≠0` question (§3) is resolved as chart-selection: the
cascade's adapted basis selects the `e≠0` chart (rank-1: a single point, generic `e≠0`); termination is
`e`-independent (`ΣM` drops regardless — `c5-termination-CERT.md`).

## 5. Net for `routeStep`'s fate

**No per-node-mechanism research gap exists at C5.** The partial-drop node is the SAME single-Schur /
Fubini-shear mechanism as the pure-defect C1 node, iterated one complement-pivot at a time (Codex Q4:
larger partial drops iterate the rank-1 case — "chart bookkeeping and unit verification, not new
multi-core geometry"). This CONFIRMS the prior verdict (`r1-realizability-feasibility-CERT.md`): the §4
gap is **DLN-chart-combinatorics, formaliser-weeks, gated on the general `hnode`/shear chart**. The
`routeStep` dispatcher is **roadmapped-but-reachable**, not blocked on open math.

The honest deliverable for the expedition is unchanged: **(2,2,2)-instance end-to-end + conditional
general spine (all named pieces green) + roadmapped `routeStep`** — but the roadmap is now de-risked: the
hardest node type (the deep MIXED C5 that Codex flagged as the escape hatch) is constructible.

## Most likely thing to break this

The `‖e‖²≠0` chart-cover argument (§3) assumes the complement-`e=0` locus is genuinely handled by a
deeper branch with strictly smaller recursion measure — i.e. the recursion TERMINATES through the
`e=0` sub-branches. This is the `lex(L, ΣM, ncDefect)` termination (g138 §3), which is banked for the
single-path `ChainDimSplit` but NOT yet checked for the per-chart branching the C5 cover introduces. If
a C5 `e=0` sub-branch fails to decrease the measure, the recursion could stall. The next decorrelated
step that would fully settle it: verify the C5 per-chart branching (the `e_i≠0` cover + the `e=0`
deeper-defect sub-branch) is `lex`-decreasing — a finite termination check, formaliser-scale, NOT a
new mechanism.
