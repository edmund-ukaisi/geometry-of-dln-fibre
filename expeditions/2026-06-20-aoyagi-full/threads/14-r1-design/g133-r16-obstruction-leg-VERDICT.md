# g133 — R1.6 obstruction leg (pp3, decorrelated) — VERDICT

- **Seat:** `pp3`, OBSTRUCTION direction, R1.6 (the single open gate of the hero task). Task #17.
- **Question:** is the tree atlas (per-node: pivot blow-up → Schur-squeeze descend) EXHAUSTIVE and
  WELL-FOUNDED, so `rlctAtOn(coreLoss) 0 = lambdaCore`? Equivalently, does the pivot-tree's `⨅` over
  paths equal `½·min_t Mval(t)` over admissible rank strata?
- **Method:** independent exact reconstruction (the design memo `r1-general-atlas-design.md` read for
  the node operation, NOT for a verdict; pp2's g129/g132 verdict certs NOT read). Exact integer
  arithmetic for Mval/Adm; sympy for the chart algebra; a decorrelated Codex consult with the
  conclusion withheld. Monte-Carlo used only as a search guide, never as a result.

## VERDICT: ROUTE-HOLDS (no obstruction found), with scoped conditions

All three attack directions (i) missed-branch, (ii) multiplicity-2 undershoot, (iii) stuck descent —
find **no obstruction** across an exhaustive exact scan of 9324 width vectors (L ∈ 1..4, widths 1..6)
plus targeted symbolic chart computations. The atlas `⨅` equals `2·lambdaCore` on every probed chain.
The route holds **under named structural conditions** (listed below); the residual risk is the
general-`m×k` squeeze-constant existence (verified by mechanism, not yet exhaustively symbolic) and a
Lean-structuring nuance in the termination measure.

The decorrelated Codex (xhigh, conclusion withheld) independently adjudicated Q1/Q2/Q3 all **FACT** —
no counterexample — by reasoning that matches my own derivation (artifact:
`codex/g133-r16-obstruction-{prompt,answer}.md`).

---

## Ground truth (reproduced exactly from Lean `Foundations/Lambda.lean`)

`Mval`, `admPred`, `Adm`, `lambdaCore` reimplemented in `g133-scripts/mval.py` and cross-checked
against the Lean `#eval`/`#guard_msgs` block: `(2,2,2)→3/2`, `(2,1,2)→1`, `(2,2,2,2)→3/2`,
`(3,3,3,3)→3` — all reproduce exactly. This is the target set the atlas must hit as a codim-min.

`Mval(M,t) = (M[0]−t₁)(M[1]−t₁) + ∑_{j=2}^{L}(t_{j−1}−t_j)(M[j+1]−t_j)`; admissible = weakly-decreasing,
`t_L=0`, per-block bounds.

---

## (i) MISSED BRANCH — no obstruction. admPred = exactly the realizable rank strata.

**The attack:** an admissible stratum `t` with `Mval(M,t) < min over realized paths` (atlas
over-estimates RLCT); equivalently, paths ↛ admissible strata not surjective.

**Independent reconstruction.** The pivot-tree path that records rank-kept vector `t` (`t_j =
rank(A^(1)…A^(j))`) is constrained by pure linear algebra: `rank(XY) ≤ min(rank X, rank Y)` ⟹
non-increasing `t_1 ≥ … ≥ t_L`; cumulative-min width bound `t_j ≤ min(M[0],…,M[j])`; and on the
zero-locus `{∏C=0}`, `t_L = rank(full product) = 0`. I enumerated this **realizable** set independently
(`recursion_model.py`) and compared to `admPred`:

- **Exhaustive: `admPred == realizable` on all 9324 chains (L∈1..4, widths 1..6), 0 mismatches**
  (`admbound_vs_cummin.py`, `broad_stress.py`). Neither a `t` in admPred with no geometric path, nor a
  realizable chain outside admPred. The path↔admissible-stratum correspondence is the identity, and the
  per-step residual block `(t_{j-1}−t_j)(M[j]−t_j)` sums to `Mval(M,t)` — so a path's accumulated
  exceptional codim is exactly `Mval(t)`. **Path codim-min == 2·lambdaCore on all 9324 chains.**

**The genuine sub-worry (and why it does not bite).** There ARE weakly-decreasing vectors with
`t_L ≠ 0` whose Mval is STRICTLY SMALLER than `minMval` — 320 such cases over L∈2..3, widths 1..4
(e.g. `M=(1,2,1)`, t=(1,1), Mval=0 < minMval=1). IF the resolution blew up such a center, its
exceptional ratio `½·0 = 0` would shatter the lower bound. The defense is **geometric and airtight**:
`t_L ≠ 0 ⟺ rank(full product) ≠ 0 ⟺ ∏C ≠ 0`, so these strata lie OFF `{∏C=0}`. The resolution
resolves `{∏C=0}`; every blow-up center is contained in `{∏C=0}` (centers ⊆ the variety being
resolved), and the blow-down image of every exceptional divisor is contained in `{∏C=0}`. So no
divisor sits over a `t_L≠0` center. `admPred`'s `t_L=0` clause IS exactly "lies in the zero-locus".

**Concrete witness of the defense** (`case121.py`): `M=(1,2,1)`, `F=(a₁b₁+a₂b₂)²`. The forbidden
t=(1,1) (Mval=0) requires `a·b ≠ 0`, off `{F=0}`. Exact vertex-blow-up gives `rlct₀(F)=½` =
lambdaCore(1,2,1); the Mval=0 center is never a resolution center. (MC guide consistent: the integral
diverges as c↑½.)

**Scoped condition (i):** the resolution blows up ONLY centers contained in `{∏C=0}` (⟺ `t_L=0` ⟺
admissible). This is structural to "resolve `{∏C=0}`", not an extra hypothesis.

---

## (ii) MULTIPLICITY-2 UNDERSHOOT — no obstruction. k_E = 1 on every faithful divisor.

**The attack:** an exceptional divisor with loss-multiplicity `k_E ≥ 2` (the trap: `x^{2k}` →
threshold `1/(2k)`; `(x²+y²)²` → `½ < 1`), giving ratio `(h+1)/(2k) < codim/2`.

**Mechanism, verified exactly (`multiplicity.py`, `faithful_222.py`, `case313_depth3.py`).**
- `F = ‖∏C‖²` is MULTILINEAR: scaling one factor `A^(s)` by `u` scales `∏C` by `u`, hence `F` by `u²`
  — order exactly 2. Confirmed: scaling factor A by u gives `ord_u(F) = 2` exactly for (3,1,3),
  (2,3,2), (2,2,2,2); the pivot-blow-up chart `A = x·Âhat` (pivot a unit) gives `ord_x(F) = 2` and the
  residual `F/x²` is **x-FREE** (the exceptional factors out cleanly).
- Because the residual is x-free, a subsequent blow-up introduces a FRESH coordinate independent of x.
  The faithful (2,2,2) leaf is `x²·s²·unit` — a NORMAL CROSSING of two `k=1` divisors (x-divisor ratio
  2, s-divisor ratio 3/2), **NOT a single `k=2` divisor**. binding = min = 3/2 = lambdaCore.

**The shared-u danger (the only way k≥2 could arise) and the squeeze's role.**
- A single exceptional `u` scaling MULTIPLE factors does give `ord_u(F) = 2k` (verified: scale A&B by
  the same u → order 4; scale A,B,C → order 6). But the faithful atlas never creates such a divisor —
  each blow-up scales ONE factor's residual block. AND even if it did, it would not undershoot:
- **Robustness theorem (exact, `naive_undershoot_search.py`, `shared_u_ratio.py`):** the worst
  hypothetical shared-u "cone" divisor (scale `k` contiguous factors by one u, Jacobian compensating)
  has ratio = (entries scaled)/(2k) ≥ lambdaCore on **all 9324 chains, 0 undershoots**; the naive
  all-origin divisor `N/(2L)` never undershoots (`N < L·minMval` has 0 solutions). The Jacobian
  exponent `h` grows in lockstep with `k`, so the ratio is robust.
- **Why k_E(F)=k_E(Φ) (`squeeze_c1.py`, `general_node_squeeze.py`):** the per-node squeeze
  `c₁·Φ ≤ F ≤ c₂·Φ` has lower constant `c₁ = σ_min(pivot minor)² > 0` BECAUSE the blow-up made the
  pivot a UNIT (invertible minor, `σ_min²=1` at the chart base — verified for rank r=1,2,3). The
  two-sided squeeze with `c₁,c₂>0` forces `ord_γ(F) = ord_γ(Φ)` along every curve γ→0, so
  `k_E(F) = k_E(Φ)` on every divisor; Φ is the smooth-block normal form (each block a FIRST-power cone
  `∑y²`, ratio block-dim/2, `k=1`). The `(x²+y²)²` trap would require `c₁=0` (F vanishing faster than
  Φ) — excluded by the unit pivot. The residual smooth block's ratio = `Mval/2 = lambdaCore` at the
  binding leaf (block dim = residual-entry count Mval), never below.

**Scoped condition (ii):** each blow-up is at a rank defect of ONE factor/partial-product, and the
post-blow-up pivot minor is a UNIT (so `c₁ = σ_min² > 0`). The unit pivot is exactly what the blow-up
restores (at the bare origin A=0 the pivot is 0 and `c₁=0`, which is WHY the blow-up runs first).

---

## (iii) STUCK / NON-TERMINATING DESCENT — no obstruction. The descent is well-founded.

**The attack:** a nonzero singular core with NO minor to blow up (stuck), so the tree never reaches the
smooth `L=1` leaf.

**Verified exactly (`termination.py`).** Every admissible chain's descent has length exactly L and
reaches the terminal `t_L=0`; all per-step block sizes ≥ 0 (no Nat underflow). At each layer either:
(a) a genuine rank defect (`t_j < t_{j-1}` and `t_j < M[j]`) ⟹ residual block size ≥ 1 ⟹ a minor to
blow up ⟹ width drops; or (b) a no-drop / full-rank layer (block size 0) ⟹ the layer is consumed ⟹
chain length drops. The lexicographic measure **(chain length, then ∑ widths)** strictly decreases at
every nonterminal node ⟹ termination. No nonzero singular core is stuck: a genuine defect always has a
minor; a no-defect layer is consumed.

**A Lean-grade nuance (NOT a math obstruction) — flag for the formaliser (`hdrops_gap.py`).** The
design's `ChainDimSplit.hdrops : 0 < ∑ drop` is a **width-sum** guard. It is NOT strictly decreasing at
a full-rank / no-drop layer — e.g. `M=(3,2,1)`, t=(2,0): layer-1 has `t_1 = 2 = min(3,2)` (full rank),
width-drop 0; `M=(2,2,2)` t=(2,0) layer-1 width-drop 0; and several depth-4 cases. The descent still
terminates via chain length. **Scoped condition (iii):** `hdrops` (width-only) is sufficient ONLY if
each recursion node coincides with a genuine rank-defect blow-up (block ≥ 1); for full-rank/no-drop
layers either fold them into the next genuine-drop node, or carry the lexicographic (chain-length)
measure. A Lean structuring choice, not a refutation.

---

## Scoped sufficient conditions under which the claim HOLDS (the catalogue)

1. **(i) Centers ⊆ `{∏C=0}`** ⟺ `t_L = 0` ⟺ admissible. Structural to resolving `{∏C=0}`. Then
   {paths} ↔ {admissible strata} is the identity and path codim = Mval; `⨅ = 2·lambdaCore`. (Verified
   exhaustively, 9324 chains.)
2. **(ii) One-factor blow-ups with unit pivot.** Each blow-up resolves ONE factor's rank defect; the
   post-blow-up pivot minor is a unit ⟹ squeeze `c₁ = σ_min² > 0` ⟹ `k_E(F) = k_E(Φ) = 1` on every
   divisor (residual x-free ⟹ normal crossing, no shared-u). Robust even against hypothetical shared-u
   (ratio ≥ lambdaCore always).
3. **(iii) Well-founded lexicographic measure (chain length, ∑ widths).** Strictly drops at every
   nonterminal node ⟹ terminates at the `L=1` smooth leaf. `hdrops` (width-only) needs the genuine-drop
   structuring caveat.

## The most likely thing to break it (residual risk — the next thing to settle)

- **The general-`m×k` squeeze-constant `c₁>0` end-to-end.** I verified `c₁ = σ_min(pivot minor)² > 0`
  by mechanism (invertible unit pivot) and exactly at rank r=1,2,3 at the chart base, and the full
  (2,2,2) node. The general claim — that for ANY admissible `m×k` node the Schur residual
  `flatCore − Φ ∈ ideal(regular gens)` with the squeeze holding uniformly with `c₁>0` on a whole
  neighbourhood (not just the chart base point) — is the existence obligation pp2 is certifying. This
  is the load-bearing analytic content; my finite/symbolic checks support it but do not constitute the
  general proof. **Next:** a symbolic certificate that the Schur residual's leading form is positive
  definite on the unit-pivot chart for general `(m,k,r)`, giving `c₁ > 0` on a neighbourhood.
- **The G3 strict-transform / G5 gluing infra** (the named research-wall for general M) is orthogonal
  to this verdict — it is the CONSTRUCTION, not the value. The VALUE identity `⨅ = 2·lambdaCore` is what
  I adjudicated, and it holds.

## Artifacts
- Scripts: `g133-scripts/` (mval, recursion_model, admbound_vs_cummin, multiplicity, shared_u_ratio,
  naive_undershoot_search, faithful_222, case121, case313_depth3, squeeze_c1, general_node_squeeze,
  termination, hdrops_gap, broad_stress). All exact-integer / sympy; MC only as a guide.
- Decorrelated Codex (xhigh, conclusion withheld): `codex/g133-r16-obstruction-{prompt,answer}.md`.
