# #109 reconciliation — (C2) GL-straighten THEN blow-up; det-1 Schur is NEEDED (pp-hall, 2026-06-21, #121)

**fm-2 + Codex (decorrelated, Aoyagi web-search) reframing.** The general-M chart is (C): det-1
GL-straightening of regular blocks THEN explicit blow-ups along rank-defect strata (monomial Jacobian
`∏u^h`) ⟹ `rlctAt = min_j (h_j+1)/(2k_j) = ⨅ monomialThreshold = resolution_charts`. Reconcile with #109:
is the det-1 Schur a NEEDED PIECE (C2) or SUPERSEDED by a pure blow-up cover (C1)?

**Verdict: (C2) — GL-straighten THEN blow-up. The det-1 Schur is GENUINELY NEEDED, not eliminable.**
Two decorrelated legs converged (pp-hall exact (2,2,2)-anchor + Codex xhigh). This SHARPENS #118's
"both-in-sequence": the det-1 Schur is not just present — it is load-bearing for the project's
coordinate-subspace blow-up machinery.

## The decisive reason (exact, (2,2,2)-anchored)
The project's blow-up machinery (`g5_pivotNode`, S1.1 `hsurj`/`hImE` for monomial charts) blows up
COORDINATE subspaces `{y_1=…=y_c=0}`. The recursion's centers must therefore STAY coordinate subspaces.

- **Node 1:** blow up `{A1=0}` — ALREADY a coordinate subspace (the entries of A1). Jacobian `x^3`
  (codim 4), `F = x²·‖Ahat A2‖²`, `Ahat[0,0]=1` a unit. NO straightening needed here. (This is the
  one node where pure-(C1) coincides with (C2).)
- **Node ≥2:** the residual `‖Ahat A2‖²` (`Ahat[0,0]=1` unit). The rank-defect center, in the inherited
  `(p,q,r,b)` coords, is the **bilinear hypersurface `{r−pq=0}`** (the Schur complement `w=r−pq`), NOT a
  coordinate subspace. **The coordinate-subspace blow-up CANNOT be applied to it directly.** The det-1
  Schur (unit pivot `Ahat[0,0]=1`: row op `R2−=q·R1`, col op `C2−=p·C1`) reduces `Ahat→[[1,0],[0,r−pq]]`,
  and the det-1 change of variable `w := r−pq` (unit Jacobian, `dr/dw=1`, no weight) STRAIGHTENS the
  center to the coordinate `{w=0}`, on which the blow-up applies. (`g121_node2.py`, Codex-confirmed.)

So the det-1 Schur does TWO load-bearing jobs at node ≥2: **(i)** reduces the chain (strict transform =
smaller `‖∏C'‖²`, keeping the recursion a matrix-chain core whose next center is again a rank stratum —
#109's validated substitution algebra), and **(ii)** straightens the rank-defect center to a coordinate
subspace so the (C1)-style coordinate blow-up can fire at all. Without it, after a coordinate blow-up the
residual is NOT a clean smaller chain-core, its rank-defect centers are NOT coordinate subspaces, and the
recursion does NOT close as the `⨅ monomialThreshold` chain-core recursion (`g121_c1_test.py`).

## (C1) is insufficient FOR THE PROJECT'S MACHINERY (the honest scope)
- **(C1) pure coordinate-subspace blow-up cover, no straightening:** INSUFFICIENT at node ≥2 — the center
  is bilinear/non-coordinate, the coordinate machinery cannot apply.
- **(C1) via general-ideal / arbitrary-smooth-center blow-up (no Schur):** mathematically possible
  (Hironaka), but that is DIFFERENT machinery Mathlib LACKS (the rejected heavier path). Not the route.
- **(C2) det-1 Schur straighten THEN coordinate blow-up:** the correct build for the project's machinery.
  The det-1 Schur is what keeps every recursive center a coordinate subspace after a unit pivot is chosen.

## The clean recursion node (fm-2's re-scoped #111 chart family)
Each nontrivial node:
1. **Unit-pivot chart:** choose a nonzero pivot minor, normalize to a unit on the chart.
2. **Det-1 Schur straighten** (unit-pivot row/col ops): clear the pivot row/col, replace the rest by its
   Schur complement; **Jacobian = 1** (no weight). Reduces the chain.
3. **Smaller-chain reduction:** residual = a zero-product matrix-chain core of smaller dims (the strict
   transform; #109's substitution, all diff=0).
4. **Coordinate-subspace blow-up** of the now-coordinate rank-defect center `{y_1=…=y_c=0}`, `c=Mval(t)`:
   chart `y_i=u`, `y_j=u·v_j`, **Jacobian `|u|^{Mval(t)−1}`**, `F∘π = u²·F_res`, exceptional `(k,h)=(1,
   Mval(t)−1)`, ratio `Mval(t)/2`. **THE MONOMIAL WEIGHT.**
5. **RLCT contribution:** `(h_j+1)/(2k_j)`; headline `= ⨅_leaves monomialThreshold`. The monomial weights
   come from the BLOW-UPS (step 4); the det-1 Schur (step 2) contributes NONE.

`IsSchurChart` (fm-2's contract) must carry: a **det-1 straightening field** (unit-Jacobian, the chain
reduction) AND a **Jacobian-weight field** (`(k,h)` per exceptional, from the blow-up). Both per node.

## Honest revision status of #109 (the find-confound, completed)
- **#109's det-1 Schur substitution (all diff=0) is SOUND** and is the GL-straightening PIECE (step 2) of
  (C) — a real, needed coordinate change, NOT a wrong route.
- **#109's framing was INCOMPLETE** (now corrected across #118 + #121): it described the GL/Schur part and
  omitted the blow-up's monomial weight + the fact that the Schur straightens (not resolves). The recursion
  does not "bottom at a smooth leaf via det-1 alone"; it is (C2) = det-1 straighten THEN coordinate blow-up,
  headline `⨅ monomialThreshold`, monomial(× smooth-block) leaves.
- **For fm-2:** build (C2) — the GL-straightening (det-1 Schur) + the coordinate-subspace blow-up. NOT the
  blow-up cover alone (C1), which the project's machinery cannot close at node ≥2.

Decorrelation: pp-hall exact ((2,2,2)-anchor: node-1 coordinate, node-2 bilinear-center-needs-straightening,
the (C1)-doesn't-close argument; 3 scripts `g121-scripts/`) + Codex xhigh (independent: C2, same bilinear
crux, same node Jacobian `u^{Mval(t)-1}`, same "coordinate machinery can't take a non-coordinate center").
Converged. Consult `codex/g121-C1-vs-C2-{prompt,answer}.md`. Builds on #118 (`g118-correction-note.md`).
