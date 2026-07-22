# Faithful N_p certificate (pnp-transport) — WITNESS + ELABORATION

**Charge:** the elder stage-frame brief `faithful-npivot-brief.md` — construct the faithful per-chart
normalization `N_p` (fixes the chart pivot, clears its row+column, recoordinatizes the deeper factor),
elaborate it on the coupled witnesses in `canonFlatten` coords, and run every acceptance test +
kill-condition. worked.tex-anchored (443–458 the clear + deeper recoord; 562–630 the block-blow-up
recursion, b-chain, `M'`). No Lean; exact algebra.

**Verdict: the faithful `N_p` is RATIFIABLE.** It is the block-elim peel `Q₁·C·Q₂ = diag(1, Δ)` (the
`(3,3,4)` battery's verified, unipotent, exact peel) FANNED to an arbitrary pivot via the
pivot-centered Schur reduction, WITH the deeper-factor recoordinatization that `canonShearOf` omits.
**Every acceptance test passes and NO kill-condition fires:** interior-pivot charts monomialise, the
deeper recoord is per-layer-(S+1)-linear, boost-readiness reproduces `honest_clear_2222`
`(True,True,True)`, and the b-chain / `M_{s,k}` are preserved (the block-blow-up Jacobian is
`u^{|center|−1} = u^{M'−1}` and `N_p` is det 1, so it adds nothing to Aoyagi's exponent ledger).

Scripts (all re-run fresh, exit 0): `verify/npivot_monomialise.py` (interior-pivot kill-condition),
`verify/npivot_bchain_M.py` (b-chain/M structural), `verify/npivot_consolidate.py` (recoord linearity +
explicit-peel boost-readiness + double-boost), `verify/honest_clear_2222.py` (the (2,2,2,2) faithful
residual). Decorrelation: the banked `theory/aoyagi-2023-reproduction/g-coupled-334-diagb.py` independently
verifies the peel `= N_p` (its header: "Codex reached the same b-vector by its own route").

---

## 1. The object — `N_p` explicit, per chart (Deliverable 1)

At state `(S,J)`, `δ = [cleared=0]`, chart pivot `p = (a,b) ∈ canonCenterOf(state)` (flat coord decoding
to layer `S`, row `a`, col `b`), the faithful per-edge step map is `blockBlowupMap(center, p) ∘ N_p`:

- **`blockBlowupMap(center, p)` (KEEP — spectator-free, correct).** In the `p`-chart, the block entry at
  `p` is the exceptional coordinate `u`, and every other center entry `d_ij` reads `u · w_ij` (`w` the
  chart coords). Spectators (off-center coords) pass through.

- **`N_p` = the Schur reduction PIVOTED AT `(a,b)`** (worked.tex:453–457 `Q,U`; the `(3,3,4)` battery's
  `Q₁ = [[1,0],[−C21,E]]`, `Q₂ = [[1,−C12],[0,E]]`):
  - `Q₁` clears the pivot **column** `b` (a row-op); `Q₂` clears the pivot **row** `a` (a col-op).
  - `Q₁ · C · Q₂ = ` (pivot `(a,b) → 1`; pivot row `a` and column `b` → `0`; and the Schur residual
    `D'_{ij} = w_ij − w_ib · w_aj` for `i ≠ a, j ≠ b`). Both `Q₁, Q₂` are **unipotent (det 1)**.
  - After factoring the common `u`, the block is `u · P^T [[1, O],[O, D']] P` (`P` the permutation bringing
    `(a,b)` to the corner) — a coordinate monomial times a unit-triangular matrix. **Monomialised.**

- **Deeper recoordinatization (the piece `canonShearOf` omits).** The adjacent deeper factor is
  recoordinatized by the pivot-column-clearing unipotent: in the Lean `coreGen` order
  `mult = A_{N-1}···A_1·A_0` (layer `S` cleared, layer `S+1` the next-left factor),
  **`A_{S+1} → A_{S+1} · Q₁⁻¹`** (right-multiplication, unipotent column-mix). This is Aoyagi's
  `A'^{(S+1)} = Q_2'^{-1} A^{(S+1)}` (worked.tex:445) read in the Lean product order (transpose-dual: her
  left-by-col-op-inverse ↔ the Lean right-by-row-op-inverse; same operation, opposite ends of the product).

- **Corner vs interior (the fan).** For a **corner** pivot (`a = cleared` or `b = cleared`), `N_p`'s Schur
  reduction is exactly `canonShearOf`'s interior cross-term `−u_γ·u_β` PLUS the deeper recoord — i.e.
  `canonShearOf` is the corner-pivot instance of `N_p` with the deeper recoord missing. For a
  **strict-interior** pivot (`a,b > cleared`), `N_p` is the pivot-SHIFTED Schur reduction (Gaussian
  elimination pivoting on the interior entry). `N_p` is the family `p ↦ (pivot-fixing Schur reduction at p
  + deeper recoord)` — one normalization per affine chart, the standard resolution picture (pnp-fan's
  "(pivot, pivot-fixing normalization) pairs").

---

## 2. Deeper-recoord bookkeeping (Deliverable 2) — per-layer-(S+1)-linear ✓

`A_{S+1} → A_{S+1} · Q₁⁻¹` with `Q₁⁻¹ = [[1,0],[γ,1]]`, `γ` the below-pivot layer-`S` coordinate. Verified
(`npivot_consolidate.py` §1):

    A_{S+1}·Q₁⁻¹ = [[a00 + a01·γ, a01], [a10 + a11·γ, a11]]

Each entry is **total degree ≤ 1 in the layer-(S+1) coords** `a··` (a right column-mix: col 0 gains
`γ·(col 1)`, col 1 unchanged), with coefficients in `{1, γ}` drawn **only from layer `S`**. So the recoord
(a) keeps degree-1 in layer `S+1`, (b) leaves layers `> S+1` untouched, (c) pushes added degree only into
layers `≤ S` — exactly the case the `PerLayerDeg1From` `fromLayer = S+1` threshold excludes. **The
Gap-B homogeneity stability (elder ruling §6) holds; kill-condition "recoord not per-(S+1)-linear" does not
fire.**

---

## 3. b-chain / M_{s,k} preservation (Deliverable 3) — THE DECISIVE CHECK ✓

`N_p` reproduces Aoyagi's b-chain `b_i = ∏_{t̃<i} u` and exponents `M_{s,k}`, so the banked Object-B↔D
bridge (`min M_{s,k} = minAdm = cCodim`) is **unchanged**. The argument has three parts, all verified:

**(A) `M_{s,k}` are combinatorial (the oracle's `divExp`), not touched by the normalization.** The oracle's
`stepUpdate` sets `case2 → resRows·resCols = (widthMinUpto−cleared)·(d(layer+1)−cleared) =
(M(S)−J)(M^{(S+1)}−J)` and `case1(1) → += runLen·resCols = J₁·(M^{(S+1)}−J)` — **exactly Aoyagi's
worked.tex:626 / :616**. `N_p` is a coordinate normalization; it does not modify `divExp`.

**(B) The Jacobian is Aoyagi's `u^{M'−1}`, pivot-independent.** `blockBlowupMap` (kept) has Jacobian
`u^{|center|−1}`, and `|canonCenterOf| = M'` — verified for every case-2 step of `(2,2,2,2)`, `(3,3,4)`,
`(3,3,2,2)` (`npivot_bchain_M.py`: `|center| == (M(S)−J)(M^{(S+1)}−J)` all True). `N_p` (the Schur `Q₁,Q₂`
+ the deeper recoord) is **unipotent (det 1)**, so it adds **nothing** to the Jacobian. Hence the
exceptional coordinate's exponent is `M'−1` regardless of which pivot the chart uses — Aoyagi's
`M_{s,k}−1` (worked.tex:589). A **composite** of hypersurface blow-ups would instead introduce many
exceptional coords with different exponents; the **block** blow-up + unipotent `N_p` gives Aoyagi's.

**(C) The b-chain `b_i = ∏_{t̃<i} u` is determined by `t̃` + birth coords (combinatorial), unchanged.**
Unrolled from the oracle trace (`npivot_bchain_M.py`); the sequence of Schur clears factors out one `u`
per clear at the rows with `t̃ < i`, giving the dominant `diag(b)`. **The `(3,3,4)` coupled binding divisor
`minAdm = 8` is realized ON this peel:** `g-coupled-334-diagb.py` (banked, decorrelated) verifies the peel
`Q₁·C₁·Q₂ = diag(1, Δ)` (`= N_p`), the b-vector `(E, E·α·v, E·α·v·δ·w)` with divisibility chain
`b₁|b₂|b₃`, the JOIN of the coupled exceptional coords into the single `E`-divisor of exponent 8
(`h_E = 7`, ratio `(7+1)/2 = 4 = ½·8`). So `N_p` is the exact geometric operation the coupled bridge sits
on. **Preserved; the decisive check passes; the composite fallback is NOT forced.**

---

## 4. Per-fan-chart checks (Deliverable 4)

**(a) Monomialisation — EVERY chart, corner AND strict-interior** (`npivot_monomialise.py`). For all pivots
of `2×2`, `3×3`, `2×3` blocks, the pivot-centered Schur reduction gives `block = u · (pivot→1, row/col→0,
Schur residual `w_ij − w_ib·w_aj`)`: `u`-factor exact, Schur exact, pivot→1 — **all True**. In particular
the strict-interior pivots (`(1,1)` for `2×2`; `(1,1),(1,2),(2,1),(2,2)` for `3×3`) monomialise. **The
kill-condition "interior-pivot chart cannot monomialise" does NOT fire** — so the composite fallback is not
forced by the fan (this is the point pnp-fan flagged: `canonShearOf` can't fix an interior pivot, but the
pivot-SHIFTED `N_p` can).

**(b) Boost-readiness `Deg1SupportedOn ed.center`** — `(2,2,2,2)` case11, via the explicit peel `N_p`
(`npivot_consolidate.py` §2, `honest_clear_2222.py`): with the deeper recoord `A_1 → A_1·Q₁⁻¹` and the
Schur pivot `e2 = u₀₁₁ − u₀₁₀·u₀₀₁`, the residual
`M[1] = e2·(u₂₀₀·w₁₀₁ + u₂₀₁·w₁₁₁) + s·(u₂₀₀·w₁₀₀ + u₂₀₁·w₁₁₀)` has the extra-block (col-1) coords carrying
the pivot `e2`. **A1/A2/A3 = (True, True, True)** — reproduces `honest_clear_2222`. (Contrast the current
`canonShearOf` fold: `(False, True, False)`, the `F = x + yz` countermodel — see the durable
`transport-table-certificate.md`.)

---

## 5. Acceptance tests (pre-committed) — all PASS

| test | result |
|---|---|
| `honest_clear_2222` numbers reproduce (`A1,A2,A3` True at (2,2,2,2)) | **PASS** (§4b) |
| pnp-fan escape witness `{x_{p_root}=0, x_q≠0}` COVERED by the fan | **PASS** — the `q`-pivot chart reaches it (pnp-fan §2/§4; the fan is over `canonCenterOf`) |
| …AND MONOMIALISED in each fan chart | **PASS** — every pivot (incl. the interior `q`) monomialises via `N_p` (§4a) |
| boost-readiness TRUE at every fan chart | **PASS** — each chart's block reduces to `u·[[1,O],[O,D']]`; the residual is degree-1 on the center (§4) |
| b-chain / `M_{s,k}` MATCH Aoyagi (worked.tex:571/616/626) | **PASS** — `|center| = M'`, `N_p` det 1, b-chain combinatorial (§3) |

## 6. Kill-conditions — NONE fire

- interior-pivot chart that cannot monomialise → **does not fire** (§4a: the pivot-shifted Schur reduction
  monomialises every interior pivot; the composite fallback is not forced).
- a witness where the deeper recoord does not restore boost-readiness → **does not fire** (§4b: it does,
  reproducing `honest_clear`).
- b-chain / `M_{s,k}` not preserved → **does not fire** (§3: preserved; `N_p` det 1, `|center| = M'`).
- deeper recoord not per-(S+1)-linear → **does not fire** (§2: it is linear, coefficients from layer `S`).

---

## 7. The four-case ε-transport table, RESTATED under `N_p` (the original task, faithful object)

On the faithful fold (`blockBlowupMap ∘ N_p`), `foldResid` is boost-ready, so the ε-transport now holds.
Weight `chainWeight(col) = ∏_{k active} u_{birth(k)}^{ε_k(col)}`, `ε_k(col) = [divTilde(k) ≤ col]`
(**non-strict** — the pinned boundary; the reused pivot appears on `extraBlock = {col ≥ runLen =
divTilde(f)}`, the `col = runLen` boundary included).

- **base (root):** `birthCoords = ∅`, `chainWeight ≡ 1`; `foldResid = coreGen` degree-1 on
  `blockCoords d 0` (`widthMinUpto d 0 = d_0`, full first-layer block). Sound as stated.
- **case2 / case12 (append, advance `cleared`):** a new divisor born at corner `(layer, cleared)`,
  `divTilde = cleared`, exponent `M' = |center| = (M(S)−J)(M^{(S+1)}−J)`. δ=0: `blockBlowupMap` multiplies
  each selected center coord by `u_pivot` ⟹ `ε` gains `[col ≥ divTilde(d_new)]`. δ=1: the SAME increment
  is supplied by `N_p`'s deeper recoord (the piece `canonShearOf` omitted) + the Schur pivot.
- **case11 (merge, keep `cleared`):** reused divisor `f`, `divTilde(f) → cleared`, exponent
  `+= runLen·resCols`. Its pivot `u_{birth(f)}` factors out of every extra-block coord `col ≥ runLen =
  divTilde(f)` (non-strict) — the boost split `∑_{partial} α·u_i + u_pivot·∑_{extra} β·u_i` that
  `deg1SupportedOn_boostForm` consumes.
- **rollover (relabel):** `edgeShear = id`, `center = ∅`, `blockBlowupMap = id`; `foldResid` unchanged, all
  `ε` carried verbatim across the layer shift.

Master rule: `ε_{s',d}(τ') = ε_{s,d}(τ) + #(center entries selected)` at δ=0, **with the deeper-layer
recoordinatization of `N_p` supplying the same increment at δ=1** (the currently-missing piece), and the
δ=1 reset (pivot → 1) on the merged divisor.

---

## 8. Structure / ideas / firmest result

- **The whole fix is one object: the deeper-layer recoordinatization.** `canonShearOf` already computes the
  Schur pivot; what it omits is `A_{S+1} → A_{S+1}·Q₁⁻¹`. Adding it (as the pivot-fixing `N_p`) simultaneously
  (i) restores boost-readiness, (ii) monomialises the interior-pivot charts the fan needs, (iii) keeps the
  Jacobian/`M_{s,k}` (det-1), (iv) stays per-(S+1)-linear (Gap-B stable). One coupled re-author, L1⊥L3
  resolved as coupled.
- **`N_p` is the `(3,3,4)`-battery peel, fanned.** The corner-pivot peel is already banked and
  decorrelated-verified (`g-coupled-334-diagb.py`); the only genuinely new content is (a) the deeper recoord
  as an explicit fold operation and (b) the pivot-SHIFT to interior pivots (a permutation-conjugate of the
  corner peel — no new algebra, verified on 3×3).
- **Speculation (registered, not adjudicated):** pnp-fan's §"idea for the coupling lane" — that the block
  blow-up's interior charts are corners of a finer composite — is **not needed**: the pivot-shifted Schur
  reduction monomialises the interior pivots directly, as a unipotent normalization, without refining the
  block into a composite. So the faithful block-blow-up + pivot-parametric `N_p` is complete on its own.
- **Firmest result:** `N_p` (pivot-centered Schur peel + deeper recoord) monomialises every fan chart,
  preserves Aoyagi's b-chain/`M_{s,k}` (det-1 + `|center|=M'`), is per-(S+1)-linear, and reproduces
  boost-readiness — exact algebra on all three witnesses, no kill-condition fires.
- **The coupled corank-2 stress — CHECKED** (`npivot_334_interior.py`, belt-and-braces). The interior-pivot
  chart `(1,1)` of the coupled `(3,3,4)` 3×3 block peels exactly like the banked corner peel: pivot → `u`,
  its row/col → 0, Schur residual `w_ij − w_ib·w_aj`, `Q₁,Q₂` unipotent (A); the deeper recoord `Q₂⁻¹·C₂` is
  unipotent and linear-in-`C₂` (B); the block ideal is preserved by the unipotent peel `d = Q₁⁻¹·peeled·Q₂⁻¹`
  (C); and the exponent `M' = |block| = 9` is pivot-independent with Jacobian `u^8` (D). So the coupled
  `minAdm = 8` JOIN is reached from the interior chart too (the exponent, hence the QIP minimum, is
  chart-invariant). No obstruction at the interior pivot of the coupled block.
- **Most likely to break it (residual):** a corank-≥3 instance whose block chart is genuinely
  rank-deficient in a way the 2- and 3-block checks do not exercise. I see no mechanism (the peel is
  Gaussian elimination on the exceptional pivot, which is nonzero on its chart), but the deepest banked
  coupled witness (`g-coupled-33322-separated.py`, corank-3) would be the next stress if the elder wants it.
- **Next construction / consult:** if fuller assurance is wanted, run the corank-3 `(3,3,3,2,2)` interior
  charts through `N_p`. Fresh Codex on this round was inconclusive (a `codex exec` output-extraction tooling
  failure in the workspace-write sandbox, 3 attempts, no math produced) — the decorrelation is carried by the
  banked `(3,3,4)` battery (which its own header records as Codex-corroborated by an independent route).
