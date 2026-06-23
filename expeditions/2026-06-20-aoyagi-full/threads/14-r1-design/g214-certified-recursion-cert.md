# Certified routeStep recursion — the descent-soundness rides redCore_eq, NOT a new lemma (pp-hall, 2026-06-23, #39/#85)

**fm3's certified-recursion ruling** (the fresh formaliser + Codex g206 item 2 surfaced a recursion-level
vacuity gap): `split.red` is an ABSTRACT `ChainDimSplit` field — nothing ties it to what the pivot blow-up
ACTUALLY produces, so `routeAtlas`'s child exponents describe `dlnLoss(split.red) 0` while the real residual
is whatever the geometry gives ⟹ the recursion is SYNTACTIC, not a certified resolution (the g183
vacuity-trap, one level deeper). My cert-author read on the 3 questions:

## Q1 — ROOT-ANCHORING: CONFIRM (codim = Mval(root M, T), faithful via reindex-invariance)
Every per-leaf `PivotWitness` carries a **root-M-admissible** `T` with `codim = Mval(root M, T)` (the
geometric codim in the ORIGINAL ambient), all down the path — NOT `Mval(reduced chain, T_local)` (which
undershoots, g207: `minAdm(schurState M) < minAdm(root M)`). **Faithful because the geometric codim is
INVARIANT under the det-1 reduced reindex** (`redEmbed` is measure-preserving / a diffeomorphism; codim is a
change-of-variables invariant). So the center's codim, computed in the root ambient, `= Mval(root M, T)`
independent of recursion depth. `foldFamily_threshold_ge_of_pivotWitness` then bounds all leaves by
`½·minAdm(root M)`. (My §2/§4 always used `Mval(root M, T)`.)

## Q2 — schurState is a clean DEF, AND the descent-soundness is crux2's redCore_eq (NOT a new obligation)
- **`schurState M` IS a clean `ChainDimSplit M` DEF** (g214): `⟨drop, red, hsum, hdrops⟩` with
  `drop = (fun s => if s ∈ {0,1} then 1 else 0)`, `red = (fun s => M s − drop s)` = `(M_0−1, M_1−1, M_{≥2})`.
  Verified: `drop + red = M` (hsum), `Σ drop = 2 > 0` (hdrops), `Σ red < Σ M` (termination), `red ≥ 0`.
  Precondition `M_0, M_1 ≥ 1` (the C1 node; `≥ 2` for the genuine coupled-defect, else C4/leaf). So
  `split.red = schurState.red` — the genuine reduced widths. NECESSARY (termination + the value widths).
- **BUT the width def alone does NOT tie `split.red` to the blow-up's ACTUAL residual** (Codex g206 item 2,
  RIGHT). The descent-soundness is the per-cell CERT FIELD:
      `residual ∘ chart =ᶠ dlnLoss(schurState.red) 0 ∘ redEmbed`   (up to the bounded unit `g`),
  and **that IS crux2's `IsSchurStraightenSqueeze.redCore_eq`** (`G y² = dlnLoss S.red 0 (redEmbed y)`,
  `GeneralR1Recursion.lean`) — ALREADY the per-cell transport datum's field. So the descent-soundness is NOT
  a new analytic obligation; it's `redCore_eq`, which the per-cell `IsSchurStraightenSqueeze` already carries.

**THE FIX (fm3's (a)+(b), confirmed + tightened):**
- (a) define `schurState`, prove `routeStep.split = schurState` ⟹ `split.red` is the genuine reduced chain,
  NOT abstract;
- (b) prove the cell's `IsSchurStraightenSqueeze.S.red = schurState` ⟹ `redCore_eq` (already carried) ties
  `split.red` to the genuine residual `= dlnLoss(schurState.red) 0` (up to `g`).
So `split.red` is BOTH a def AND pinned to the residual by `redCore_eq`. **No new descent lemma** — the
soundness rides crux2's existing `redCore_eq`, gated only on `S.red = schurState` wiring. (2,2,2) check
(g215, Case222 backbone): step-1 A-pivot residual `Q = resolvedForm = dlnLoss(reduced (1,1,2)) 0` up to the
regular block `= redCore_eq` for the node; `schurState.red = (1,1,2)` matches. Dischargeable.

## Q3 — ACHIEVER i₀ root-anchored: YES
The binding leaf codim `= minAdm(root)`, `T* ∈ Adm(root)`. g148 always resolved each layer to its `T*`-rank
where `T*` is the ROOT minimiser; the binding divisor codim `= Mval(root, T*) = minAdm(root)`. Root-anchored
by construction (the achiever path resolves each layer to its `T*`-rank, `T* ∈ Adm(root M)`).

## The certified-recursion architecture (the NET)
A `routeStep` is a certified resolution (not syntactic) iff:
1. `routeStep.split = schurState` (the def; `split.red` = the genuine reduced widths, proven);
2. the per-cell `IsSchurStraightenSqueeze` has `S.red = schurState` ⟹ `redCore_eq` pins `split.red` to the
   residual `= dlnLoss(schurState.red) 0` (the descent-soundness, crux2's existing field);
3. the sibling root-anchored `PivotWitness` (`codim = Mval(root M, T)`, `T ∈ Adm(root)`) feeds the value lane
   (`foldFamily_threshold_ge_of_pivotWitness` C≥ + `foldFamily_achiever` C=∃).
The three lanes: (A) `IsSchurStraightenSqueeze` transport [`G = reduced ∏S_s`, `g` in `c₁/c₂`, `S.red =
schurState`], (B) the sibling root-anchored `PivotWitness` [value, C≥/C=∃], (C) `split.red = schurState`
[the def tying them]. The (2,2,2) milestone (concrete Case222 charts) is the anchor; this makes the GENERAL
recursion a certified resolution.

## Decorrelation
pp-hall exact algebra (g214: `schurState` is a clean ChainDimSplit def across (2,2,2)/(3,3,2)/(3,2,3)/
(2,2,2,2)/(4,3,2); g215: the residual = `dlnLoss(schurState.red) 0` = `redCore_eq`, (2,2,2) Case222 check).
Codex down env-wide (the AISI-wrapper hang) — exact-algebra + the structural redCore_eq identification
carries it; a decorrelated subagent pass is the substitute channel if wanted. Builds on g183/g194 (the C1
mechanism), g207 (root-anchoring), crux2's `IsSchurStraightenSqueeze.redCore_eq` (the descent field), g125
(the triangular-block-solve), the g161 reconciliation (`G = reduced ∏S_s`, `g` in `c₁/c₂`). The recursion-
level vacuity gap (Codex g206 item 2) is the g183 vacuity-trap one level deeper — closed by tying `split.red`
to `redCore_eq` via `S.red = schurState`.
