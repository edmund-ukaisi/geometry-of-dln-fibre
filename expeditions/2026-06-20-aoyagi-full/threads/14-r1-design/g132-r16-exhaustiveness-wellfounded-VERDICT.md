# R1.6 — cover-exhaustiveness + well-foundedness: ROUTE-OR-OBSTRUCTION VERDICT (pp-hall, 2026-06-22, #132)

**The pivotal gate.** Independent decorrelated leg (parallel to pp3, written WITHOUT reading pp3's cert):
does the (C2) per-node recursion (blow-up → squeeze-straighten → descend on `dlnLoss S.red 0`,
`ΣM' < ΣM`, base `L=1` smooth block) produce an atlas that (a) **exhaustively** covers the core
zero-locus (so `⨅` over the atlas = `rlctAtOn(core) 0`, not just an upper bound) and (b) **terminates**?

## VERDICT: ROUTE EXISTS (no structural obstruction). Both (a) and (b) hold, under five precisely-named load-bearing conditions. Two-leg decorrelated (pp-hall exact + Codex gpt-5.5 xhigh, conclusions withheld — converged, including Codex's independent insistence on the squeeze form).

This is `resolution_charts` (`Skeleton.lean:1017`, currently `sorry`): `rlctAtOn(core_M) 0 = ⨅ᵢ
monomialThreshold(dᵢ,kᵢ,hᵢ)`. The `⨅`-direction (`≥`: the inf is not too small) IS exhaustiveness; the
recursion descent is well-foundedness. Aoyagi's recursive blow-ups are a published complete resolution,
and the route survives the squeeze correction (#129/#131) intact.

## The atlas is a TREE (the structural picture)
- **Per node** the blow-up of the active factor's rank-defect center is an affine CHART COVER (Proj
  atlas — one chart per nonzero homogeneous pivot coordinate). `rlctAtOn(core) 0 = ⨅_{charts}` (S1.1
  min-over-cover).
- **Within each chart** the pivot is a HARD unit (#127), the squeeze step (#129/#131) gives the EXACT
  equality `rlctAtOn(core) 0 = nReg/2 + rlctAtOn(reduced core) 0`, and the reduced core
  `‖S·A2red‖² = dlnLoss S.red 0` recurses (its own chart cover).
- **Leaf** `L = 1`: `‖C_1‖²` pure sum of squares, `rlct = (#entries)/2`.

So the atlas is a tree: nodes branch into charts (the `⨅`), each chart descends by a squeeze-equality to a
strictly smaller node. The whole-tree value `= ½·(min codim over all centers) = ½·min_t Mval` (+ the
regular `nReg/2` accumulated along the path).

## (a) EXHAUSTIVENESS — holds, in two parts

### (a1) The cover is exhaustive (the `⨅` is the genuine RLCT, not an over-estimate)
- **Local (per node):** blow-up of a coordinate center `I = (z₁,…,z_c)` has the standard affine charts
  (`z_i = x`, `z_j = x·v_j`). With ALL pivot charts included, the cover reaches both the punctured
  complement of the center and the exceptional fibre — the projective-atlas tautology, exhaustive by
  construction (`g132_r16_exhaustiveness.py`). [Codex (a1): identical — "pivot=1 is the homogeneous
  direction coordinate, not a claim the original coordinate is nonzero".]
- **Composite (the tree):** exhaustive of `{∏C=0}` near the origin **iff the centers are the strict
  transforms of the admissible nested rank strata**. Every point of `{C_L⋯C_1=0}` has an admissible
  per-factor rank tuple `(s₁,…,s_L)` with product rank 0; the tree's root-to-leaf paths ARE that index
  set (which minor is the nonzero pivot at each level selects the factor's resolved rank). So every
  stratum is reached (`g132_r16_center_adversarial.py`, `g132_r16_admissible_centers.py`). The A2-side /
  rank-aligned components are reached at deeper tree levels inside the A1-chart, via the recursion on
  `‖S·A2red‖²`.

### (a2) No undershoot (the `⨅` does not drop below `½·min_t Mval`) — the SHARP point
The danger flagged in the R1-design memo (and by Codex): a divisor where `F` vanishes to high order
(`x^k`, `k≥2`, gives `rlct = 1/(2k) < ½`; `(x²+y²)²` gives `½ < 1`) would make the inf undershoot. **This
is structurally excluded by MULTILINEARITY:**
- The matrix-chain product `∏C` is **multilinear** in its factors, so scaling any single factor by a
  blow-up coordinate `x` makes `F = ‖∏C‖²` **exactly degree-2 homogeneous in `x`** — verified for the
  first and a middle factor of a 3-factor chain, x-degree exactly 2 (`g132_r16_undershoot.py`). Hence the
  monomial factor is `x^{2k}` with `2k = 2`, i.e. **`k_E = 1` on every exceptional divisor**.
- The Jacobian `|det Dφ| = x^{c−1}` ⟹ `h_E = c−1`; the per-divisor ratio `(h_E+1)/(2k_E) = c/2 =
  (center codim)/2`. So the leaf threshold along a path `= ½·(min codim along the path)`, and the atlas
  inf `= ½·(min codim over all centers) = ½·min_t Mval` — **exact, no undershoot**.
- Successive blow-ups use DISTINCT exceptional coordinates (level-1 `x`, level-2 `y`, …); the composite
  divisor is **normal-crossing** `∏ xᵢ^{2kᵢ}` with every `kᵢ = 1` (`g132_r16_refined_center.py`). No
  single coordinate accumulates order ≥ 4, because each level scales a different factor of a different
  (reduced) chain, each multilinearly. The `(x²+y²)²` multiplicity-2 trap is FORCED OPEN by
  multilinearity, not assumed away.
- **The squeeze is load-bearing here too** (Codex independently insisted): the Schur step is NOT a
  Frobenius-value equality (the unimodular `L` is not orthogonal, #129); it is the squeeze
  `c₁Φ ≤ F ≤ c₂Φ` resting on `F − Φ ∈ ideal(E)` (#131). This is what prevents a "hidden higher-order
  vanishing entering at the regular block" — the regular squares stay multiplicity-1, the reduced core is
  again a smaller matrix-chain core handled recursively, never a single high-multiplicity divisor.

Ground-truth check: `(2,2,2)` r=1 core is `M = H − r = (1,1,1)`, `core = (c₁c₂)²` — already
normal-crossing; the atlas is the identity chart, `⨅ monomialThreshold(d=2,k=(1,1),h=(0,0)) = ½ =
rlctAtOn(core)` (`g132_r16_value_222.py`). Matches the Lean-verified `rlctAt(dlnLoss 222) = 3/2`
(= `nReg/2 + ½`).

## (b) WELL-FOUNDEDNESS — holds
The recursion measure is `ΣM = Σ_s M_s`. The Schur step removes the resolved pivot row+col, so
`ΣM' < ΣM` at every nonterminal node. This is **already proven in Lean** (`ChainDimSplit.measure_drops`:
`Σ red < Σ M ⟸ 0 < Σ drop`). The only obligation is `Σ drop ≥ 1` at every nonterminal node — i.e. **no
stuck node** (singular but no resolvable pivot). That cannot happen for a nonzero matrix-chain core with
positive widths: the singular core has a nonzero minor to blow up (else it is already rank-0 = the smooth
leaf); a factor forced 0 on the stratum contributes a regular `Σx²` block, not a singular pivot
(`g132_r16_wellfounded.py`, traced `ΣM` strictly decreasing + terminating on `(3,3,3),(2,2,2,2),(4,3,2),
(5,4,3,2),(2,2,2)`). Base case `L=1`/rank-0 = the smooth block. [Codex (b): identical, including the
"no stuck node" argument and the zero-width/empty-residual terminal handling.]

## The five load-bearing facts (the route's hinges — for the formaliser)
1. **Full affine pivot cover** at every blow-up (all pivot charts, not a selected subfamily) — else the
   tree only upper-bounds.
2. **Centers = admissible zero-product rank strata** (strict transforms of the nested rank strata; blow
   up ONLY inside `{∏C=0}`). Blowing up a non-admissible center (product rank > 0, not in the zero fibre)
   would miss branches OR introduce a spurious low-ratio divisor. The recursion structurally pivots only
   on `{∏C=0}`'s rank-defect, so this holds by construction — but it must be STATED (Codex fact 2).
3. **Schur strict-transform = the SQUEEZE** `c₁Φ ≤ F ≤ c₂Φ` (`F − Φ ∈ ideal(E)`, #129/#131), re-identifying
   the residual as a smaller matrix-chain core — NOT the false unimodular Frobenius-equality.
4. **Every exceptional divisor has `k_E = 1`** (multilinearity ⟹ `F = x²·reduced`), so the per-divisor
   ratio = `c/2` and the atlas inf = `½·min_t Mval` (no undershoot, no `(x²+y²)²` trap).
5. **`ΣM` strictly drops** until the `L=1` smooth base (`ChainDimSplit.measure_drops`, already Lean-green).

Without facts 2-3 the tree is only a candidate (can miss branches or introduce spurious low-ratio
divisors); with all five, the atlas `⨅` equals the genuine local RLCT.

## Most likely thing to break this
The one fact still needing a Lean-grade proof (beyond the green `measure_drops` and the #131 squeeze) is
**(a1)-composite**: that the tree's centers reach EVERY admissible rank stratum — the "branch set =
admissible-rank-stratum index set" claim. This is the genuine exhaustiveness content (R1.6 in the design
memo's decomposition). It is the rank-stratification combinatorics of `{∏C=0}` (the type-A quiver / nested
rank-pattern lattice the Core engine handles abstractly); the danger is an admissible stratum with no
root-to-leaf path reaching it (a "missed branch"), which would make `⨅` an over-estimate. My argument that
the index sets coincide is structural but not yet a Lean-grade combinatorial proof — that is the residual
real work R1.6 names. The multiplicity-1 (fact 4) and termination (fact 5) are solid; the squeeze (fact 3)
is #131-certified; the cover-completeness (fact 2 + a1-composite) is the piece to harden.

## Next construction to settle the open part
State + certify the **branch ↔ admissible-rank-stratum bijection** for the general matrix-chain core: the
recursion's root-to-leaf paths (the pivot/minor choices at each level) are in bijection with the admissible
per-factor rank tuples `(s₁,…,s_L)` cutting `{∏C=0}`, and each path's center chain has min-codim = that
stratum's codim = `Mval(t)`. That + facts 1,3,4,5 closes R1.6. (This is the `Core`-engine rank-pattern
lattice meeting the `DLN` resolution — a natural place for the quiver-orbit ↔ rank-pattern translation to
do load-bearing work.)

Decorrelation: pp-hall exact (8 scripts `g132_r16_*` in `g129-scripts/`: well-foundedness trace, tree
exhaustiveness, adversarial center check, multiplicity via multilinearity, refined composite normal-crossing,
admissible-centers pin, (2,2,2) ground-truth) + Codex gpt-5.5 xhigh (independent: route sound for the full
flag/pivot atlas, the SAME five hinge facts, the SAME multilinearity `k=1`, the SAME squeeze insistence, the
SAME no-stuck-node — converged). Consult `codex/g132-r16-exhaustiveness-{prompt,answer}.md`. Builds on #129
(squeeze), #131 (ideal-membership), the g3 scoping memo (risk #1 now resolved by the squeeze), and the
r1-cover-and-decomposition design (R1.6 = the cover/completeness piece).
