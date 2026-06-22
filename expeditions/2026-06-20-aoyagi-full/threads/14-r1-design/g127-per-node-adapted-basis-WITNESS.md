# Per-node (uᵢ,ψᵢ) adapted-basis straighten — WITNESS on a REDUCED chain (pp-hall, 2026-06-22, #127)

**TOP-priority crux gate for fm-2's `schur_straighten_exists`.** WITNESS (not infer from outer #125) the
per-node adapted-basis transvection straighten on a REDUCED chain's deepest point, and confirm the
hard-1-pivot interface (blow-up normalizes the pivot → MP transvection straighten) holds AT a reduced node.

**Verdict: WITNESS.** The per-node adapted-basis straighten is exhibited on the (3,3,3) reduced node and
recurses uniformly; the only obstruction is trying to straighten at the raw all-bilinear origin BEFORE the
blow-up (which is why blow-up-first is the correct interface). Two decorrelated legs converged (pp-hall
exact + Codex xhigh, which generalized the block calculation to arbitrary reduced nodes).

## The witness (exact, on the (3,3,3) reduced node)
Top (3,3,3) zero-core `‖A1 A2‖²` at the origin: all generators bilinear, Jacobian rank 0 — NO regular
block, NO unit pivot, so the straighten CANNOT start at the raw origin. **Blow up `{A1=0}`** (`A1 = x·Â`,
`Â = [[1,p,q],[r,s,t],[u,v,w]]`, `Â[0,0]=1` a HARD constant): `F = x²·‖Â A2‖²`. This `‖Â A2‖²` (hard pivot)
is the REDUCED NODE's input.

**The (uᵢ,ψᵢ) adapted basis = the hard-pivot row/col TRANSVECTIONS** (the `uᵢ` = pivot column direction,
`ψᵢ` = pivot-row covector):
- `L = [[1,0,0],[−r,1,0],[−u,0,1]]` (clear col 0: `Rᵢ −= Â[i,0]·R₀`),
- `R = [[1,−p,−q],[0,1,0],[0,0,1]]` (clear row 0: `Cⱼ −= Â[0,j]·C₀`),
- both **det = 1 (TRANSVECTIONS, MEASURE-PRESERVING)** — because the pivot is a HARD 1, no division.
- `L·Â·R = blockdiag[1, S]`, `S = [[s−pr, t−qr],[v−pu, w−qu]]` = the reduced 2×2 Schur chain factor.

**The loss-level identity, witnessed (exact, diff = 0):** `‖Â A2‖²` straightens to `[regular pivot row =
the 3 entries of row 0 of Â·A2] + ‖S·A2red‖²`, where `A2red` = rows 1,2 of `A2` and `S·A2red` is a
genuine smaller zero-core (a `(2,2,3)` matrix-chain product) — the next recursion node
(`g127_loss_identity.py`). This is the (2,2,2) anchor's `step1Residual_eq_resolvedForm` pattern, witnessed
one level deeper on (3,3,3).

## The general per-node block (Codex, pp-confirmed)
At ANY reduced node with a hard pivot, `A = [[1, a],[b, D]]`, `L = [[1,0],[−b,I]]`, `R = [[1,−a],[0,I]]`
(unipotent, det=1), `L·A·R = blockdiag[1, S]`, `S = D − b·a` (the Schur complement). The pivot-row product
variables are regular (Jacobian block = identity, pivot literally 1); the residual is the smaller chain
product `S·Bred` — again a matrix-chain zero-core. This is the `(uᵢ,ψᵢ)` straighten for `schur_straighten_exists`.

## The hard-1-pivot interface — holds per-node, UNIFORMLY
- **FACT:** the raw zero-core origin is all-bilinear (Jacobian rank 0), so straightening can't start there;
  a blow-up is required first.
- **Every nonterminal reduced node** is again a zero-product matrix-chain core at its own origin
  (all-bilinear). Blowing up the rank-stratum center gives affine charts indexed by a nonzero homogeneous
  coordinate; in each chart THAT coordinate is normalized to `1` — so the next pivot is again a HARD `1`.
  The straighten is again a det=1 transvection. **Recurses uniformly** (`g127_uniform.py`).
- **Chart-locality qualification (Codex, the #109 caveat restated):** no SINGLE chart supplies the pivot
  for all exceptional directions, but the blow-up chart COVER always supplies SOME hard-1 pivot locally —
  if the chosen pivot coordinate vanishes, that point belongs to another chart. NOT an obstruction.

## Recursion closes (ΣM strictly drops)
The residual `S·A2red` is a smaller matrix-chain zero-core `dlnLoss M' 0`. The Schur step replaces the
active factor by an `(m−1)×(n−1)` Schur factor and restricts the next factor to the matching `(n−1)` rows,
so `ΣM' < ΣM` every nonterminal step ((3,3,3) ΣM=9 → reduced (2,2,3) ΣM=7). Terminal zero-size /
already-resolved cases stop. This is #123's field-6 (well-foundedness) + field-4 (reduced-chain map),
witnessed per-node.

## Net for fm-2's `schur_straighten_exists`
**WITNESS — the per-node adapted-basis transvection straighten is exhibited + uniform across reduced
nodes.** The interface fm-2 builds:

    blow-up gives hard-1 pivot  →  det-1 transvection straighten (L·A·R = blockdiag[1, S], S = D − b·a)
    →  regular pivot-row block + smaller zero-core residual ‖S·Bred‖²  →  recurse (ΣM' < ΣM)

The straighten is MEASURE-PRESERVING (det=1 transvections, hard pivot) — so it uses `rlctAtOn_comp_homeomorph`
(needs MP, available — `S1Fubini.lean:54`), NOT the unit-weight transport (that is the DIFFERENT
a114e07e/L2-outer case, where there's no blow-up and the pivot is the perturbed unit `(1+w0)`). The
`(uᵢ,ψᵢ)` adapted basis is the explicit `(L,R)` transvection pair above, reusing the green `lemma2Fwd`
structure (the (2,2,2) anchor) generalized to the reduced node. Both pieces (blow-up `pivotBlowupOn`,
transvection straighten `lemma2Fwd`-style) are green; the crux is uniform assembly, NOT a new mechanism.

The honest correction the controller flagged is now SOLID: "per-node = YES" is no longer inferred from the
outer #125 — it is WITNESSED on the (3,3,3) reduced node (the explicit `(L,R)` transvections, the diff=0
loss identity, the uniform recursion), with the per-node pivot HARD (from the blow-up), the straighten a
det=1 MP transvection (NOT the outer unit-Jacobian peel).

Decorrelation: pp-hall exact (3 scripts `g127-scripts/`: the reduced-node transvection straighten, the
diff=0 loss identity, the uniform recursion) + Codex xhigh (independent: WITNESS, the general
`A=[[1,a],[b,D]]→blockdiag[1,D−ba]` block, the chart-cover hard-1 qualification, ΣM'<ΣM, "the only
obstruction is the raw origin before blow-up"). Converged. Consult `codex/g127-per-node-witness-{prompt,answer}.md`.
Builds on #125 (outer), #126 (per-node-distinct), #121 (C2), #123 (contract fields).
