# T-Obl3b Route-A on WAISTS — the deep-layer-SVD → qPeel direct resolution: **CLOSES (LABOUR)**

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.** Exact integer/rational
arithmetic for the load-bearing charge budget (`minAdm`, SVD-Jacobian monomial powers, per-block codim
gate); numeric MC only as a guide. Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD —
prompt framed "adjudicate either direction"): `codex/tobl3b-routeA-waist-{prompt,answer}.md`. Scripts
(this dispatch, banked at `scripts/routeA/`): `waist_charge_budget.py` (exact identity + per-shell gate),
`svd_model_rlct.py` (numeric CoV-identity validation).

**The ONE truth-value.** For the WAIST regime (nondegenerate 3-width chains `(x,s,z)` with a strict waist
`s < min(x,z)`, minimal `(2,1,2)`) where the head-split route has a genuine PIVOT wall
(`u·ρ < minAdm(redChain u M)`, ρ = min tail width, not rescued by the co-minimizer): does ROUTE A (a
finer deep-layer-direct stratification) CLOSE the finiteness bound (LABOUR), or hit a genuinely-new WALL?

---

## ★ HEADLINE VERDICT — **CLOSES (LABOUR).** Route A discharges every waist; no new wall.

The 3-width waist box-integral `I(c) = ∫_box ‖A₀A₁‖_F^{−2c}` (`A₀` is `x×s`, `A₁` is `s×z`, `s≤z`) is
finite for every `c < ½·minAdm(x,s,z)` via a DIRECT resolution: **spectrally decompose the deep layer
`A₁`, turning the loss into the banked qPeel corner-slice form**, no head-split, no pivot wall.

- **The mechanism (exact identity).** SVD `A₁ = UΣVᵀ` (`U∈O(s)`, `Σ=[diag σ | 0]`, `V∈V_s(ℝ^z)` Stiefel).
  Since `V` has orthonormal columns, `‖A₀A₁‖_F² = ‖A₀UΣ‖_F² = Σ_{j=1}^s σ_j²·‖A₀u_j‖²`. Setting
  `X_j := A₀u_j ∈ ℝ^x`, the map `A₀ ↦ (X_1,…,X_s)` is a linear isometry `ℝ^{xs} → (ℝ^x)^s` for the
  orthonormal frame `U`; and `U,V` integrate out over the COMPACT groups to finite constants (the
  A₀-integral is `U`-independent, being O(s)-invariant). So

      I(c)  =  const(O(s),Stiefel) · ∫_{σ, X}  (Σ_j σ_j²‖X_j‖²)^{−c} · J(σ) dσ dX,

  which is **exactly `qCornerSliceAtUnits` / `qPeelIntegral`** (`RouteMSJCorankQ`) with radial `u_j = σ_j`,
  units `U_j = ‖X_j‖²`, deep blocks `X_j ∈ ℝ^x` (`m_j = x−1`). NUMERIC (machine precision, `svd_model_rlct.py`):
  `‖A₀A₁‖² = Σσ_j²‖A₀u_j‖²` to rel-err `≤ 2.7e−15` on `(2,1,2),(3,1,3),(3,2,3),(4,3,4)` — the CoV is faithful.

- **The Jacobian is a monomial on the ordered chamber (Weyl majorant).** The rectangular-SVD Jacobian is
  `J(σ) ∝ ∏_{i<j}|σ_i²−σ_j²| · ∏_j σ_j^{z−s}`. On the ordered chamber `σ_1≥…≥σ_s`,
  `∏_{i<j}|σ_i²−σ_j²| ≤ ∏_{i<j}σ_i² = ∏_j σ_j^{2(s−j)}`, an UPPER bound in the SAFE direction (Jacobian in
  the numerator), so `J(σ) ≤ ∏_j σ_j^{h_j}`, `h_j = (z−s) + 2(s−j) = z+s−2j`. The Vandermonde coupling
  among small singular values is thus **dominated away** — no residual coupling.

- **The charge budget adds to `minAdm` EXACTLY.** Each block `j` is finite for `2·w_j·c < min(h_j+1, x)`
  (the `σ_j`-marginal `∫σ_j^{h_j−2w_jc}` gives `h_j+1`; the deep `X_j∈ℝ^x` Morse gives `x`). Weighted-AM-GM
  (qPeel) at the balancing weights reaches `c < ½·Σ_j min(x, h_j+1)`. And **[FACT, exact, 0 violations over
  405 chains widths 1..9]**

      Σ_{j=1}^s min(x, z+s+1−2j)  =  minAdm(x,s,z)   for every 3-width chain.

  So the single ordered-chamber qPeel gives finiteness for `c < ½·minAdm` — TIGHT, no undershoot.

- **Why the head-split walled but this does not.** The head-split routes the whole reduced-chain charge
  `minAdm(redChain u M) = t·z` through the `u×u` pivot `P`-block, whose map `(P,B₁₂)↦[P|B₁₂]·A₁`
  factors through `rank(A₁)=min(s,z)=s`, delivering only `u·s` and losing the `t·(z−s)` extra columns.
  Route A instead gives EACH singular mode `j` its own FULL `ℝ^x` Morse block `X_j = A₀u_j` — capturing the
  whole `x`-direction of `A₀` per mode — which is exactly the charge the pivot missed. The bottleneck layer
  `A₁` is DIAGONALISED rather than peeled through a rank-collapsing corner.

- **Decorrelated Codex CONCURS** (CLOSES-WITH-CAVEAT; caveat = only non-binding shells need the exponent
  truncation). Independently derived the SAME resolution and SHARPENED it (below). Caught my prompt's
  `minAdm(4,2,4)` typo (correctly 7, not 8; my scripts had 7).

---

## Part 1 — The exact route-A stratification and per-stratum reduction (task item 1)

### 1.1 The stratification IS the deep-layer spectrum; L=0 makes `Z_deep = I`, so `Z = A₁`

For a 3-width chain, `L = 0`: the deep-tail product `Z_deep = I` (constant, full rank — S1/M2gtM1 certs). So
the brief's route-A verb "finer `Z_deep`-stratification" is, at `L=0`, a **stratification of the single deep
layer `A₁` itself** (`Z = prod(tailChain M) A' = A'₀ = A₁` at `L=0`), by its singular values / rank. The
banked shell cover applies verbatim: `singularShell ε r j` = `{weakEigCount ε A₁ = j}` (eigenvalues of
`A₁A₁ᵀ` below `ε²`), `singularShell_iUnion` covers the box, `lintegral_le_sum_finCover` assembles.

### 1.2 Per-shell reduction — the pivot wall does NOT recur; the direct/spectral treatment avoids it

On shell `k` (`k` large singular values of `A₁`, `s−k` small), Codex's clean per-shell chart (pivot the
`k×k` invertible block of `A₁`, Schur-complement out the corank block `W ∈ ℝ^{r×q}`, `r=s−k`, `q=z−k`):

    ‖A₀A₁‖²  ≍  ‖C‖²  +  ‖D·W‖²  =  ‖C‖²  +  Σ_{i=1}^r σ_i(W)²·‖X_i‖²,   X_i = D·(left-sing-vec of W) ∈ ℝ^x.

- The `k` large directions give a CLEAN `ℝ^{xk}` Morse block (`C`), charge `xk` — **`x·k` genuine
  independent linear equations `A₀|_{colspace}=0`, NOT the rank-collapsing pivot map**. This is the crux
  reversal of the wall: the head-split delivered `t·s` (through `rank A₁`); the direct route delivers `x·k`
  (through the full front, capped only by the ambient `x`).
- The `r = s−k` small directions give an `r`-block qPeel corner (`RouteMSJOnePeel334`'s general form,
  `qPeelIntegral_lt_top`) with radial `σ_i(W)`, deep blocks `X_i∈ℝ^x`, Jacobian powers
  `h_i = q−r+2(r−i)`.

The head-split's PIVOT wall does not recur per-stratum: on the binding shell the qPeel gate holds exactly
(§2). The saturated shells (`k` small, `A₁≈0`) are the multi-radial qPeel with the truncation — also finite.

### 1.3 The banked corner engine (`RouteMSJOnePeel334` → `qPeelIntegral_lt_top`), exactly

`qPeelIntegral_lt_top` (`RouteMSJCorankQ`, sorry-free): for `c < ½·Σ_i(h_i+1)` UNDER the per-block gate
`h_i ≤ m_i`, `∫_X qCornerSlice(u; ‖X_i‖²)·∏|u_i|^{h_i} < ⊤` via `q`-ary weighted AM-GM at
`w_i=(h_i+1)/Σ` + `q`-fold Tonelli into the `X_i` Morse integrals (`sumSqND_box_lt_top`) and the
`u`-monomial box. This IS the saturated-shell rescue the brief names, in its width-general form
(`onePeel334` is its `q=2, (3,3,3,4)` anchor). Route A consumes it directly per shell.

---

## Part 2 — Stratified additivity: the charge budget adds to `minAdm`, no divergence (task item 2)

### 2.1 The load-bearing identity (exact, exhaustive)

`waist_charge_budget.py` [1]: `Σ_{j=1}^s min(x, z+s+1−2j) = minAdm(x,s,z)` for ALL 405 chains
(widths 1..9, `s≤z`), **0 violations**. This is the bridge from the SVD/monomial charges to `minAdm`.

### 2.2 Per-shell charge ≥ ½·minAdm on EVERY shell (so the finite cover closes)

`waist_charge_budget.py` [3]: `2·c'_max(shell k) = kx + Σ_{j>k} min(x, z+s+1−2j) ≥ minAdm` for **every**
`k∈[0,s]` on every tested waist (widths ≤ 6). Codex's closed form:
`kx + Σ_{i=1}^r min(x, q+r+1−2i) = min_{j≥k} f(j) ≥ min_j f(j) = minAdm`, where `f(k)=(s−k)(z−k)+xk`. So
the shell-cover sum (`lintegral_le_sum_finCover`) reconstructs finiteness for `c<½·minAdm` — every shell
converges, the binding shells (where `f(k)=minAdm`) at exactly `½·minAdm`. Worked anchors:

    (2,1,2) minAdm 2  shells[2,2]        binding k∈{0,1}   (rank-1: literal PRODUCT of two ℝ²-Morse)
    (3,1,3) minAdm 3  shells[3,3]        binding k∈{0,1}
    (3,2,3) minAdm 5  shells[5,5,6]      binding k∈{0,1}   (k=1: xk=3 clean + W∈ℝ^{1×2} radial h=1)
    (4,2,4) minAdm 7  shells[7,7,8]      binding k∈{0,1}
    (4,3,4) minAdm 10 shells[10,10,10,12] binding k∈{0,1,2} (s=3: multi-small-σ, Vandermonde dominated)

### 2.3 The gate `h_i ≤ m_i`: holds on binding shells; benign truncation elsewhere

[FACT, Codex-proved, script-confirmed] The raw gate on the leading small block is `h_1+1 ≤ x ⟺ x ≥ q+r−1`,
which is `f(k+1)−f(k) ≥ 0`. At a binding `k` (`f(k)=min`), `f(k+1)≥f(k)`, so the gate **holds on every
binding shell** — the qPeel applies raw, no truncation, reaching `½·minAdm`. On NON-binding shells the raw
gate can fail (`h_i+1 > x`, exactly when `x < q+r−1`); it is dissolved by the monomial truncation
`σ^{h_i} ≤ σ^{min(h_i, x−1)}` on `[0,1]` (a valid one-line majorant), giving effective powers
`h̃_i = min(h_i, x−1)` with all gates `≤ x−1`. This is the `min(x, ·)` cap in the identity §2.1 — it never
drops a shell below `minAdm` (§2.2). The charge budget adds with `peelCharge`/co-minimizer NOT needed:
at `L=0` there is no deep tail, so `minAdm_backPeel_cominimizer_ge` is vacuous here (correcting the brief's
route-A sketch, which invoked the co-minimizer — that piece is for the `L≥1` corank wall, not the waist).

---

## Part 3 — The genuinely-new hard core (task item 3): what is NOT banked

The only genuinely-new content is a single, standard-matrix-analysis lemma family (Codex item F): the
**uniform rectangular-SVD (equivalently Gram-spectral) change-of-variables for the deep layer**, with:

1. **The loss identity** `‖A₀A₁‖² = Σ_j σ_j²‖A₀u_j‖²` from `A₁ = UΣVᵀ` (elementary; `‖MVᵀ‖=‖M‖` for `V`
   Stiefel). — small, builds on `frobSq` API.
2. **The SVD/eigenvalue CoV + Weyl-Jacobian majorant.** Change variables `A₁ ↦ (σ, U, V)` with
   `dA₁ ∝ ∏|σ_i²−σ_j²|∏σ_i^{z−s} dσ dU dV`, then bound `∏|σ_i²−σ_j²| ≤ ∏σ_i^{2(s−j)}` on the ordered
   chamber. — the main new analytic piece. **Mathlib has the Gram spectral theorem** (`IsHermitian.eigenvalues`,
   used already by `weakEigCount` / the S1 `U_sf` frame / `RouteMSJDetMono`), so the eigenvalues of `A₁A₁ᵀ`
   and their frame are banked; the DENSITY/Jacobian of the map is the extension. NOT in Mathlib off-the-shelf;
   LABOUR (a known Wishart/Weyl result), possibly the heaviest single piece.
3. **Rotated-box control** for `X = A₀U` (the frame `U` is A₁-dependent, but the A₀-integral is
   `O(s)`-invariant, so `U`/`V` integrate to compact-group constants — no measurable frame SELECTION needed,
   unlike the S1 `U_sf` residual; cleaner). — labour.
4. **The exponent truncation** `h_i ↦ min(h_i,x−1)` and **the charge identity**
   `Σ min(x, q+r−2i+1) = min_l((r−l)(q−l)+xl)`. — elementary (`decide`-checkable per chain).
5. **The corner qPeel** `qPeelIntegral_lt_top`, the shell cover, the Gram/PSD toolkit
   (`det_le_det_of_posSemidef_sub`) — all **BANKED**.

**The determinantal sub-question (does `{rank A₁=k}` codim `(s−k)(z−k)` need a nested resolution?):
NO.** [FACT] The exact-rank-`k` stratum is smooth; its normal slice is `W=0` (`W` the `r×q` Schur block),
of dimension `rq`, delivered by ONE multi-radial SVD corner (`Σ_i(h_i+1)=rq`). No recursive determinantal
peel is analytically necessary. Codex: if polynomial blow-up charts are demanded instead of SVD
integration, it becomes a rank-flag recursion of depth `≤ r` that TERMINATES, and the same truncated-gate
identity prevents a new waist wall at any depth. So there is NO hidden non-normal-crossings / nested-waist
obstruction — the `s≥3` waists (multiple small singular values, `(4,3,4)`, `(5,4,6)`, …) close identically
(Vandermonde dominated, not obstructive: it is a positive numerator factor, bounded above by a monomial).

---

## Part 4 — VERDICT + build-path

### **CLOSES (LABOUR).** The waist regime is dischargeable via route A. No genuinely-new WALL.

The head-split's PIVOT wall is an artifact of routing the deep charge through the rank-`s`-collapsing `u×u`
pivot; the direct deep-layer-SVD → qPeel resolution routes each singular mode through its own full `ℝ^x`
Morse block, delivering `Σ_j min(x, z+s+1−2j) = minAdm` exactly. Decorrelated-confirmed.

**Build-path (dependency order):**
1. **Loss identity** `‖A₀A₁‖² = Σσ_j²‖A₀u_j‖²` via Gram spectral of `A₁A₁ᵀ` (or SVD). [new, small; banked
   spectral API]
2. **Deep-layer SVD/eigenvalue CoV + Weyl-Jacobian majorant** `J(σ) ≤ ∏σ_j^{z+s−2j}` on the ordered chamber
   (`s!` unordering constant). [new, main analytic piece; Wishart/Weyl density — heaviest]
3. **Frame integration** `U∈O(s)`, `V∈V_s(ℝ^z)` → finite compact-group constants (O(s)-invariance of the
   A₀-integral). [new, standard]
4. **Exponent truncation** `σ^{h}≤σ^{min(h,x−1)}` on `[0,1]` + the `decide`-checkable charge identity
   `Σ min(x, z+s+1−2j) = minAdm`. [new, elementary]
5. **`qPeelIntegral_lt_top`** per shell/chamber. [BANKED — `RouteMSJCorankQ`]
6. **Shell cover** `singularShell(_iUnion)` + `lintegral_le_sum_finCover` (or a single ordered-chamber
   qPeel — cleaner, no shell decomposition). [BANKED — `RouteMSJShellCover`]

**Banked vs new split.** BANKED: `qPeelIntegral_lt_top` (the Morse-corner engine, = general
`RouteMSJOnePeel334`), the shell cover, the Gram spectral theorem / `weakEigCount` / `det_le_det_of_posSemidef_sub`,
`sumSqND_box_lt_top`. NEW (labour): the deep-layer SVD/eigenvalue CoV with its Weyl-Jacobian majorant
(step 2, the one substantial piece), plus the elementary loss identity, frame constants, and truncation.
NOT USED for the waist (correcting the brief): `minAdm_backPeel_cominimizer_ge` (vacuous at `L=0`),
`deeperFlag_shell_core_le` (L1 — its `hconv : m≥a+b` hypothesis is exactly what fails on the waist; route A
BYPASSES L1 rather than consuming it).

**Architectural note for the controller (out of scope but load-bearing for ∀M).** This makes 3-width chains
a clean EXTENDED BASE CASE of the arity recursion (`routeMBoxThresholdFinite_of_decoratedPeel`), discharged
directly, not by the head-split peel. The deep-layer SVD is SPECIFICALLY a single-deep-layer (`L=0`) tool —
for `L≥1` the "deep layer" is a product and does not SVD into free blocks, so the recursion still peels
`≥4`-width chains down to a 3-width leaf. Since every `≥4`-width chain has a head-split-good END (routeB
cert), the natural wiring is: **route-B orientation (peel the good end) for `≥4`-width + the SVD-qPeel
3-width base case for the waist leaf** — the SVD-qPeel supplies exactly the leaf discharge route B lacked
(the routeB cert's `(2,1,2)`-has-no-good-end obstruction is dissolved: the leaf is a base case, not a peel
target). This resurrects the cheap cover; the controller decides whether to wire it that way or keep the
`M₂≤M₁`-scoped head-split for the step.

---

## Close

- **Firmest result.** The waist regime **CLOSES (LABOUR)**. Deep-layer SVD turns
  `‖A₀A₁‖² = Σσ_j²‖A₀u_j‖²` into the banked qPeel corner-slice; the ordered-chamber Weyl-Jacobian majorant
  gives monomial powers `h_j=z+s−2j`; the exact identity `Σ min(x,z+s+1−2j)=minAdm` (0/405 violations) makes
  the qPeel threshold `½·Σ min(x,h_j+1) = ½·minAdm` — TIGHT. The head-split pivot wall (route through
  `rank(A₁)=s`, deliver `u·s`) is dissolved by giving each singular mode its own full `ℝ^x` Morse block
  (deliver `Σ min(x,·)=minAdm`). Binding-shell gate holds exactly (`⟺ f` nondecreasing forward); non-binding
  shells use a benign truncation. Exact-arithmetic + machine-precision CoV-identity + decorrelated Codex
  concurrence.
- **Most likely to break it.** (i) The deep-layer SVD/eigenvalue CoV Jacobian (build-path step 2) is the
  one substantial new analytic piece; if Mathlib's Wishart/Weyl-density support is too thin, this is a
  heavy formalisation (labour, not a math wall — the result is classical). (ii) `s≥3` waists' multi-small-σ
  Vandermonde: harmless mathematically (dominated in the safe direction), but the ordered-chamber
  restriction + `s!` symmetrisation is fiddly bookkeeping. (iii) The architectural wiring of the 3-width
  base case into the `≥4`-width recursion (route-B orientation) is a separate, combinatorial task — if a
  `≥4`-width chain cannot be oriented to a head-split-good end within the decorated step, that is a NEW
  (but different, combinatorial not analytic) question.
- **Next construction / consult.** (a) Formaliser: scope the deep-layer Gram-spectral CoV + Weyl-Jacobian
  majorant as its own module (the heaviest new brick); confirm Mathlib's `IsHermitian.eigenvalues` +
  measure-CoV suffice or whether the Wishart density needs building. (b) Controller: adjudicate the
  base-case wiring (route-B orientation for `≥4`-width + SVD-qPeel 3-width leaf) — a `minAdm`-combinatorics
  question in this seat's instruments, recommend a short follow-on. On the WAIST itself: build.
