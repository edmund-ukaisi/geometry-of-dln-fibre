# Final-assembly design cert — the `DecoratedStepHyp adm` step leg (#5, the (□) step)

**Seat:** pen-and-paper WITNESS (design + adversarial stress-test), genm-sj5-domination. **Date:**
2026-07-12. **NO Lean, NO build.** Exact algebra (minAdm/QIP recursion, PSD-determinant monotonicity,
exact rationals). Decorrelated `local-codex-consult` (xhigh, conclusion withheld):
`codex/final-assembly-zunif-{prompt,answer}.md`.

**Consumed / read:** `genm-sj5-recon/s0-reduced-core-fidelity-cert.md` (§S0 domination + §S0.5 general
γ'-parent); `offsector-il-design-cert.md` (§Close + the flag arithmetic §3 + the two-brick split §2);
`borderline-statement-card.md` (the θ-interpolation + its Deferred #1 threshold-comparison); the LANDED
signatures `cornerComparator_adm` / `exists_cornerComparator_adm` (`RouteMSJCornerComparator`),
`corankOffSector_b1_le` (`RouteMSJOffSectorB1`), `corankOffSector_bpos_le` (`RouteMSJOffSectorBPos`),
`corankOffSector_borderline_atBorder_le` (`RouteMSJOffSectorBorderline`),
`freedSchurLoss_inner_peel_le` / `_bounded_le` (`RouteMSJInnerDescent`); the `DecoratedStepHyp adm`
contract + driver (`RouteMSJDecoratedRec:144`), the base `decoratedBaseHyp_faithful` (`RouteMSJBaseHyp`),
`carrierThreshold_shift` (`RouteMSJDecorated:71`), `minAdm_redChain_succ_ge` (`RouteMSJTransversality`),
`exists_binding_cut` (`RouteMSJDecoratedCharge`), the DEAD plain-IH skeleton
`RouteMSJDecoratedPeelStep.innerCorankDescent_lt_top` (Q2-superseded).

---

## ★ VERDICT — the assembly CLOSES; Obl-3 (Z-uniformity) RESOLVES as LABOUR, decorrelated-confirmed

The final assembly of the five LANDED pieces into a proof of `DecoratedStepHyp adm` is **structurally
sound and closes for `c' < carrierThreshold(M) = ½·minAdm(M)`**. The crux — the Z-uniformity Obl-3, the
`C₁(Z) = Cresid·Wenn(Z)` non-uniform constant with `Wenn(Z) → ∞` as `σ_min(Z) → 0` — **is NOT an
obstruction. It resolves by a FINITE singular-value-shell stratification of the deeper product `Z`, and the
charges ADD exactly (banked convexity, 0 undershoots / 3161 cuts).** The residual is measure-theoretic
LABOUR (the per-shell uniform-constant adapted-minor chart lemma), the same piece-A the sibling threads owe.

```
CLOSES (labour): DecoratedStepHyp adm = at a binding cut t★, Γ-first freed-corner peel → good/off split on
σ_min(Q_b) → off-sector estimates (banked, per-fixed-full-rank-Z, giving C₁(Z)=Cresid·Wenn(Z)) → Obl-3
Z-stratification by singular-value shells of Z: SHELL 0 {σ_min(Z)≥ε} uniform-Wenn (Wenn(Z)≤ε^{-ab}·Wenn(I),
PSD-det monotonicity) → t★-comparator IH; SHELLS j=1..r-1 {j small sv's} + SATURATED SHELL j=r=min(a,b)
{≥r small sv's} → (t★+j)-comparator on redChain@(t★+j), charge C_j=(a-j)(b-j)+minAdm(redChain@(t★+j))≥minAdm(M)
→ arity-(L+1) IH outright. Pointwise ≤ + lintegral_mono closes the parent. Charges add EXACTLY (tight at j=0,
binding). θ-borderline: θ chosen ADAPTIVELY (θ>1-(M-2c')/ab), nonempty interval; a FIXED θ<1 would be an
obstruction. Owed = the adapted-minor uniform-constant MEASURE assembly (piece A), LABOUR.
```

**One correction folded in (decorrelated-Codex, sharpening the offsector cert §2):** the Z-stratification
SATURATES at `r = min(a,b)`. Exact-`j` shells for `0 ≤ j < r`; ALL deeper degenerations (`≥ r` small
singular values, including genuine rank-drops) fall into ONE final shell handled by the **zero-freed-corner**
cut `t★+r` (where `(a−r)(b−r) = 0`). Cuts `t★+j` for `j > r` are unavailable (`t★+j > min(M₀,M₁)`), so the
saturated shell is essential — it is where the a·b-type 2nd-order points live, and the arity-(L+1) IH covers
them full-box (no rank-drop recursion; #118-safe).

---

## 1. THE CRUX — Obl-3 (Z-uniformity), EXACTLY what to formalise

**The two σ_min sectors are DISTINCT — keep them separate.** `σ_min(Q_b)` is the INNER good/off split
(item #2, per-fixed-`Z`); `σ_min(Z)` is the OUTER Obl-3 stratification (this section). `Q_b = A_cor·Z`
(`b×m` corank rows), `Z` = the deeper product (`M₂×m`, itself a product over deeper layers ranging in a
bounded box, so `rank Z ∈ 0..M₂`, full-rank generic/open-dense).

The LANDED off-sector lemmas are **per-fixed-full-rank-`Z`** and carry a **`Z`-dependent** constant:
`∫_{A_cor∈box}∫_Γ (w+‖Ccross+Γ·Q_b‖²)^{−c'} ≤ C₁(Z)·w^{−(c'−shift)}`, `C₁(Z)=Cresid·Wenn(Z)`,
`Wenn(Z)=∫_{A_cor∈box} det(Q_bQ_bᵀ)^{−a/2}dA_cor`, `w=frobSq(Γ'·Z)` the comparator loss. `Wenn(Z)<∞` for
full-rank `Z` when `a<M₂−b+1`, but `sup_{full-rank Z} Wenn(Z) = ∞` (blows up as `σ_min(Z)→0`). So the
per-`Z` bound does NOT integrate over the outer `Z` uniformly. **This is the sole genuinely-new soundness
surface; the value `½·minAdm` was already defended by QIP+Aoyagi.**

### Obl-3 spec — the two obligations the tide must discharge

**Stratify the outer `Z`-domain by SINGULAR-VALUE SHELLS** (a FINITE, compact, exhaustive partition of the
`Z`-box), `r := min(a,b)`, thresholds `ε_0 ≥ ε_1 ≥ … ≥ ε_r > 0`:

- [★ CORRECTED 2026-07-12 by the T-Obl3b pin (`tobl3b-pin-cert.md`, Codex Q4): the shells MUST use a
  SINGLE threshold `ε` (NOT distinct decreasing `ε_j`). Distinct `ε_j` leave a REAL intermediate-band gap
  `{σ_{M₂−j}∈(ε_{j+1},ε_j)}` — 76557/200000 `Z` uncovered in the sweep. With a single `ε`, `S_j = {exactly
  j singular values < ε}` partitions `Z` by the count of small singulars — 0/200000 gaps, EXHAUSTIVE. Use
  `ε_j := ε` throughout below.]
- **Shell 0** `S₀ = {σ_min(Z) ≥ ε}` (all `M₂` singular values `≥ ε`; `Z` full-rank, coercive).
- **Shell `j`** (`1 ≤ j ≤ r−1`) `S_j = {σ_{M₂−j}(Z) ≥ ε > σ_{M₂−j+1}(Z)}` (exactly `j` singular values
  `< ε`; the surviving `M₂−j` bounded below).
- **Saturated shell `S_r = {σ_{M₂−r+1}(Z) < ε_r}`** (`≥ r` small singular values — ALL remaining
  degeneracy, incl. genuine rank-drops). This is the ONE lumping shell; `j = r` has zero-width freed corner.

**Obl-3(a) — UNIFORM-WENN on the good shell `S₀`.** On `{ZZᵀ ⪰ ε₀²·I}` (⟺ `σ_min(Z) ≥ ε₀`),
`det((A_cor·Z)(A_cor·Z)ᵀ) ≥ ε₀^{2b}·det(A_cor·A_corᵀ)` (PSD-determinant monotonicity: `A_cor(ZZᵀ)A_corᵀ ⪰
ε₀²·A_cor A_corᵀ`, `det` monotone on PSD), hence
> `Wenn(Z) ≤ ε₀^{−ab}·Wenn(I_{M₂})`, and `Wenn(I_{M₂}) = ∫_{A_cor∈box} det(A_cor A_corᵀ)^{−a/2} < ∞`
> exactly under `a < M₂−b+1` (banked `detGram_lintegral_box_lt_top`).

This is a **`Z`-UNIFORM** bound (the `ε₀^{−ab}` factor is `Z`-independent). It upgrades the landed per-`Z`
`C₁(Z)` to a uniform constant `C₀ := Cresid·ε₀^{−ab}·Wenn(I)` on `S₀`. Decorrelated-Codex-confirmed
(Q2: "Yes, the determinant-monotonicity bound is correct … no additional uniformity hole occurs on shell 0").
*For `b=1` this is nearly banked already:* `corankWeight_lt_top`'s internal reduction gives `Wenn(Z) ≤
(c₀²)^{−a/2}·∫frobSq(A)^{−a/2}` with the coercivity constant `c₀` explicit — the `ε₀^{−ab}=c₀^{−a}` bound
in that lemma's proof body; the tide re-exposes it as a returned uniform constant.

**Obl-3(b) — RANK-DROP DEEPER FLAG on `S_j` (`j ≥ 1`).** On shell `j`, `Z` has exactly `j` weak directions
(`< ε_j`) and `M₂−j` strong directions (`≥ ε_j`). Peel at the DEEPER binding cut `t★+j`:
- The freed corner shrinks to `(a−j)×(b−j)`, charging `½·(a−j)(b−j)`.
- The remainder reduces to a **reduced comparator on `redChain (t★+j) M`** at exponent `c'−½(a−j)(b−j)`.
- The `j` weak directions are eliminated by a **uniformly-invertible `(M₂−j)`-coordinate-minor chart**
  (Cauchy–Binet: `σ_{M₂−j}(Z) ≥ ε_j` gives a minor with `|det| ≥ ε_j^{M₂−j}`), leaving the weak directions
  INSIDE the deeper comparator's own parameter space; the shell indicator is then **discarded** (the IH is
  full-box, so restricting to `S_j` only decreases the integral) before invoking the IH.

The `(t★+j)`-comparator is `cornerComparator (redChain (t★+j) M) k jc` (LANDED `cornerComparator_adm`,
`exists_cornerComparator_adm`), an arity-`(L+1)` admissible decoration, so `DecoratedBoxThresholdFinite`
of it is given **DIRECTLY by the step's decorated IH** — NOT re-derived. **Codex Q4 warning (fold into the
tide):** invoke the full-box IH outright; *"reapplying the non-uniform conditional estimate instead of
invoking the IH would recreate the gap — that is a proof-assembly error."* There is **no infinite regress**:
`j` is a finite local branch index (`0..r`), arity strictly decreases at the IH call, the saturated shell
`j=r` has zero freed corner.

**The genuine formalisation risk (piece A, the one place a hidden non-uniformity can bite):** the adapted-
minor chart lemma for `S_j` (`j ≥ 1`) — uniform constants, box distortion, and measure/Jacobian control
while identifying the residual EXACTLY with a `cornerComparator` on `redChain (t★+j) M`. Codex Q5 verdict:
**LABOUR**, this is the riskiest spot; the mathematics is credible but not formally closed until the lemma
is supplied. Shell 0 (Obl-3(a)) is clean and near-banked; the labour concentrates on shells `j ≥ 1`.

---

## 2. THE CHARGE ARITHMETIC — charges ADD across the stratification (exact, banked)

Flag charge `C_j := (a−j)(b−j) + minAdm(redChain (t★+j) M)`, `j = 0..r`, `r = min(a,b)`, `a=M₀−t★`,
`b=M₁−t★`. Binding identity (banked `exists_binding_cut`): `minAdm(M) = ab + minAdm(redChain t★ M) = C_0`.

**`C_j ≥ minAdm(M)` for every `j`, TIGHT at `j=0`** (proof, exact `ℕ`, banked convexity):
- Convexity `minAdm_redChain_succ_ge` at each cut `t★+i` (`i ≤ r−1`): `minAdm(redChain (t★+i+1) M) −
  minAdm(redChain (t★+i) M) ≥ (a−i)+(b−i)−1`.
- Telescope `i=0..j−1`: `minAdm(redChain (t★+j) M) − minAdm(redChain t★ M) ≥ j(a+b) − j²`.
- `C_j − minAdm(M) = [(a−j)(b−j) − ab] + [minAdm(redChain (t★+j) M) − minAdm(redChain t★ M)]
  ≥ [−(a+b)j + j²] + [j(a+b) − j²] = 0`. ∎ (Codex Q3 independently: `k_j + R_j ≥ M`.)

**The IH fires on every shell.** On shell `j` the comparator exponent is `e_j := c' − ½(a−j)(b−j)`. Need
`e_j < carrierThreshold(redChain (t★+j) M) = ½·minAdm(redChain (t★+j) M) = ½(C_j − (a−j)(b−j))`, i.e.
`c' < ½·C_j`. Since `c' < carrierThreshold(M) = ½·minAdm(M) = ½·C_0 ≤ ½·C_j` (STRICT), the IH fires at every
`j` with strict margin (`j=0` margin `= carrierThreshold(M) − c' > 0`, the hypothesis; `j>0` extra slack
`½(C_j − C_0)`). At `j=0` this is exactly `carrierThreshold_shift` at `u = t★`, binding equality
`carrierThreshold(M) − ½·ab = carrierThreshold(redChain t★ M)`. Charges ADD to EXACTLY `½·minAdm(M)`.

**The freed-corner charge is the shift; the reduced chain carries the rest.** `½·(a−j)(b−j)` (freed corner,
via the atom/bounded bricks) + `½·minAdm(redChain (t★+j) M)` (reduced chain, via the IH) = `½·C_j ≥
½·minAdm(M)`. The saturating log at the `a=M₂` / `a=M₂−b+1` borderline is subdominant to the STRICT margin
`c' < carrierThreshold(M)` (never absorbed by slack — the binding cut is zero-slack at `j=0`).

---

## 3. THE GOOD/OFF `σ_min(Q_b)` SPLIT + Γ-FIRST PEEL (item #2 — exhaustive, both → `w^{−shift}`)

At a binding cut `t★` of the FaithfulSJAt γ'-parent `D` (`decLoss(u,z) = commonDivisor(u)²·frobSq(Γ_D·
prod(dropHead M))`, `Γ_D` the free front block, `a_D = M₀` forced — S0.5), block-partition `Γ_D` and free
the `a×b` corner `Γ`. **Γ-first peel:** integrate `Γ` by the banked Gaussian corner lemma; the freed corner
couples to the tail only through `Γ·Q_b`, `Q_b = A_cor·Z` the `b` corank rows (`A_cor` = the peeled layer's
free corank block).

**Split on `σ_min(Q_b)` (exhaustive `{≥ε} ∪ {<ε}` per fixed `Z`):**
- **GOOD `{σ_min(Q_b) ≥ ε}`** (S0/S0.5 domination, DESIGNED): the atom brick `freedSchurLoss_inner_peel_le`
  applies (`Q_bQ_bᵀ` PosDef), and `det(Q_bQ_bᵀ)^{−a/2} ≤ ε^{−ab}` is a bounded CONSTANT (NOT a monomial —
  must NOT ride into `jac'`). Drop the nonneg residual: `Base^{−(c'−½ab)} ≤ w^{−(c'−½ab)}`. Parent
  integrand ≤ `const · [commonDivisor²·w]^{−(c'−½ab)}` = `const · (t★-comparator integrand)`. Cheap.
- **OFF `{σ_min(Q_b) < ε}`** (the banked estimates): the atom's `det^{−a/2}` is unbounded, so use the
  off-sector lemmas which integrate `A_cor` over the box and clip the anisotropic singularity, giving
  `C₁(Z)·w^{−(c'−shift)}` with the `Z`-dependent `C₁(Z)=Cresid·Wenn(Z)` — handed to Obl-3 (§1).

Both branches reduce to the `w^{−shift}` form (`w = frobSq(Γ'·Z)`, `Γ' = [P|B₁₂]·A₂` the reduced-product
front block, tail `Z` TIED), i.e. the reduced comparator loss. The residual is nonneg and dropped (safe
upper-bound direction); the absorption CoV `(P,B₁₂,A₂)↦Γ'` (Jacobian `|det P|^{−M₂}`, bounded on the pivot
chart `|det P|≥δ`) and the corner-cross rows `C` (integrate out as a bounded box factor) are bounded chart
units, bounded EXTERNALLY — NOT threaded into `jac'` (S0.5 §2, decorrelated-confirmed).

---

## 4. THE ARITY-IH THREADING (item #3) + the θ-BORDERLINE PICK (item #4)

**Item #3 — arity IH.** The `D'` the IH fires on is `cornerComparator (redChain (t★+j) M) k jc`, with
`decLoss = commonDivisor(u)²·frobSq(prod(redChain (t★+j) M)) = commonDivisor²·frobSq(Γ'·Z)` — this IS the
`w`-form of §3 (mod the radial). The accumulated radial `commonDivisor² = |u₀|^{2k}` rides through as the
monomial `jac'₀ = jac₀ − k·peelCharge` (S0.5 §3, monomial + threshold-exact — NO non-monomial weight enters
`jac'`); `exists_cornerComparator_adm` supplies `(k,jc)` meeting the β threshold. `carrierThreshold_shift`
(binding) puts the shifted exponent `c'−½(a−j)(b−j)` strictly inside the reduced IH range (§2). The
step's decorated IH gives `DecoratedBoxThresholdFinite (cornerComparator (redChain (t★+j) M) k jc)`
outright; the pointwise `≤` + `lintegral_mono` closes the parent per shell; `ENNReal`-subadditivity sums the
finitely many shells (and the finitely many binding-cut terms of the front cover).

**Item #4 — the θ-borderline pick.** At the borderline (`a=M₂` for `b=1`; `a=M₂−b+1` for `b>1`) the
convergent det-weight LOG-diverges at `θ=1`; use `corankOffSector_borderline_atBorder_le` with `θ<1`, giving
`w^{−(c'−½θab)}`. For the IH: need `c'−½θab < carrierThreshold(redChain t★ M) = ½·minAdm(redChain t★ M)`.
Since `c' < carrierThreshold(M)` gives `c'−½ab < ½·minAdm(redChain t★ M)` (strict), any
`θ ∈ ((2c'−minAdm(redChain t★ M))/(ab), 1)` works; the interval is NONEMPTY iff `2c' < ab + minAdm(redChain
t★ M) = minAdm(M)`, i.e. `c' < carrierThreshold(M)` — the hypothesis. **Codex Q3 caution (fold in):** `θ`
must be chosen ADAPTIVELY close to 1 (`θ > 1 − (minAdm(M) − 2c')/(ab)`, the SAME interval); a FIXED
non-adjustable `θ<1` would be a **genuine exponent obstruction**. Also need `θ·a < M₂−b+1` (integrability of
`Wθ`) — at the borderline this is exactly `θ<1`, consistent. The `θ`-pick is `c'`-dependent; the tide picks
`θ = θ(c')` inside the peel, not a global constant.

---

## 5. LEAN BUILD-ORDER (what to formalise, which banked pieces consumed)

The target theorem: `theorem stepHyp_faithful : DecoratedStepHyp adm` (a new module, e.g.
`RouteMSJDecoratedStep.lean`), which with the LANDED `decoratedBaseHyp_faithful` (#4) and the trivial-
admissibility `htriv` feeds `routeMBoxThresholdFinite_of_decoratedStep` → `(□)`. The DEAD plain-IH
`RouteMSJDecoratedPeelStep` (`innerCorankDescent_lt_top` sorry, plain `hIH`) is superseded — do NOT revive
it; its `hIH : ∀M', RouteMBoxThresholdFinite M'` is the Q2-unprovable plain IH.

**Build tiles (bottom-up):**

1. **T-Obl3a `uniformWenn_le` (NEW, small).** `ZZᵀ ⪰ ε²·I → Wenn(Z) ≤ ε^{−ab}·Wenn(I_{M₂})`, i.e. the
   `Z`-uniform version of `Wenn`. Consumes: PSD-det monotonicity (Mathlib `Matrix.PosSemidef.det_le`-family
   / `det_mono` on PSD; confirm the exact lemma name), `detGram_lintegral_box_lt_top` (banked, for
   `Wenn(I)<∞`). For `b=1` re-expose the `c₀`-explicit bound already inside `corankWeight_lt_top`.

2. **T-Obl3b `deeperFlag_shell_le` (NEW, the MOUNTAIN — piece A).** On shell `S_j` (`j≥1`), the adapted
   `(M₂−j)`-minor chart: `σ_{M₂−j}(Z) ≥ ε_j` ⟹ a uniformly-invertible minor (Cauchy–Binet), CoV eliminating
   the `j` weak directions into the deeper comparator, uniform Jacobian/box-distortion constant, residual
   `= cornerComparator (redChain (t★+j) M) k jc`-integrand. Consumes: `corankOffSector_bpos_le` /
   `_borderline_atBorder_le` at the reduced ambient, the banked atom/bounded bricks, a Noetherian finite
   singular-value-shell cover (`Core.RankLocusClosed` + `RouteMSJSigMin`), `corank_survival_ae`. **This is
   the residual soundness LABOUR** — the one place a hidden non-uniformity can bite (Codex Q5).

3. **T-charge `flagCharge_ge` (mostly banked).** `C_j ≥ minAdm(M)`, tight at `j=0`, via the telescoped
   `minAdm_redChain_succ_ge` (banked convexity) + `exists_binding_cut` (binding identity). Exact `ℕ`/`omega`.
   The `c' < ½C_j ⟹ e_j < carrierThreshold(redChain (t★+j) M)` step via `carrierThreshold_shift`.

4. **T-good `goodSector_le` (S0.5, DESIGNED).** `{σ_min(Q_b)≥ε}`: atom brick + `det≤ε^{−ab}` constant +
   drop residual → `const·(t★-comparator integrand)`. Consumes `freedSchurLoss_inner_peel_le`,
   `posDef_gram_of_rank_eq`, `cornerComparator_decLoss`.

5. **T-peel `faithfulParent_peel` (the assembly spine).** Given FaithfulSJAt `D` on `M`: at `t★` (binding
   cut), Γ-first peel → good/off `σ_min(Q_b)` split (T-good + the off-sector lemmas) → Obl-3 shell
   stratification of `Z` (T-Obl3a + T-Obl3b) → per-shell pointwise `≤ const·(cornerComparator (redChain
   (t★+j) M) k jc)`-integrand at `e_j` → `lintegral_mono` + `ENNReal.sum_lt_top` → IH. Consumes the absorption
   CoV (`mulLeftₚ`/`lintegral_comp_mulLeftₚ` measure work, `RouteMSJDecoratedPeelMeas`), `carrierThreshold_shift`.
   Handle the degenerate `adm` disjuncts `admCorankA M = 0` / `admCorankB M = 0` (empty freed corner)
   trivially before the FaithfulSJAt branch.

6. **T-step `stepHyp_faithful : DecoratedStepHyp adm`.** `intro L M hIH D hD`; `rcases hD.2` on the 3-way
   `adm` disjunction; the FaithfulSJAt branch is T-peel; feed `hIH` at each `redChain (t★+j) M` via the
   `cornerComparator`.

**Banked pieces consumed (all clean-three, at `@0f098c59`):** `cornerComparator_adm`,
`exists_cornerComparator_adm`, `cornerComparator_decLoss`, `freedSchurLoss_inner_peel_le`, `_bounded_le`,
`corankOffSector_b1_le`, `corankOffSector_bpos_le`, `corankOffSector_borderline_atBorder_le`,
`corankWeight_lt_top`, `corankWeight_bpos_lt_top`, `detGram_lintegral_box_lt_top`, `corank_survival_ae`,
`posDef_gram_of_rank_eq`, `minAdm_redChain_succ_ge`, `exists_binding_cut`, `carrierThreshold_shift`,
`decoratedBaseHyp_faithful`, `decoratedBoxThresholdFinite_of_decoratedStep` (driver),
`decoratedBoxThresholdFinite_trivial_iff`. **NEW obligations:** T-Obl3a (small), T-Obl3b (the mountain),
plus the T-peel measure spine (absorption CoV + shell subadditivity).

---

## 6. Decorrelated Codex verdict (conclusion withheld in the prompt)

`codex/final-assembly-zunif-{prompt,answer}.md` (xhigh; exact objects + the Wenn non-uniformity + the banked
charge fact supplied; my resolve/labour conclusion WITHHELD). **Codex CONCURS on all five and SHARPENS three:**
- **Q1** singular-value shells ARE the right decomposition, FINITE, but **saturate at `r=min(a,b)`** (exact-`j`
  shells `j<r` + one final shell for `≥r` small sv's using the zero-corner cut `t★+r`); use
  **coordinate-minor charts (Cauchy–Binet), NOT a global SVD basis**; discard the shell indicator before the
  full-box IH.
- **Q2** the PSD-det-monotonicity bound `Wenn(Z) ≤ ε^{−ab}·Wenn(I)` is **correct, no hole**; finite iff
  `a<M₂−b+1`.
- **Q3** the full-shift charge closes every `j` (`k_j+R_j ≥ M`, exact); BUT the **θ-borderline needs `θ`
  adaptively close to 1** (`(1−θ)ab < minAdm(M)−2c'`) — a fixed `θ<1` is a separate obstruction (folded into §4).
- **Q4** NO infinite regress: invoke the full-box IH outright; arity decreases per call; `j` is a finite local
  branch index; reapplying the conditional per-`Z` estimate instead of the IH would recreate the gap (a
  proof-assembly error, not a math gap).
- **Q5** **LABOUR** — riskiest spot = the adapted-minor chart lemma (uniform constants, box distortion,
  measure/Jacobian control, exact residual = IH comparator); no degenerate `Z` missed; charges add. A fixed
  non-adjustable `θ<1` would be the one genuine obstruction. No inference of mine was fed in; decorrelated.

---

## Close

- **Firmest.** `DecoratedStepHyp adm` CLOSES for `c' < carrierThreshold(M)` by: Γ-first freed-corner peel →
  good/off `σ_min(Q_b)` split → off-sector estimates (banked, per-fixed-full-rank-`Z`) → **Obl-3
  Z-stratification by FINITE singular-value shells** (shell 0 uniform-Wenn `≤ε^{−ab}·Wenn(I)` via PSD-det
  monotonicity → `t★`-comparator IH; shells `j≥1` + saturated `j=r=min(a,b)` → `(t★+j)`-comparator on
  `redChain (t★+j) M`, arity-`(L+1)` IH outright) → per-shell pointwise `≤` + `lintegral_mono`. **Charges ADD
  EXACTLY** (`C_j = (a−j)(b−j)+minAdm(redChain (t★+j) M) ≥ minAdm(M)`, tight at `j=0`, banked convexity, 0
  undershoots). Decorrelated Codex concurs and sharpens (saturate at `r`, minor charts not SVD, θ adaptive).
- **Most likely to break (the owed residual).** The **adapted-minor uniform-constant chart lemma** for shells
  `j≥1` (T-Obl3b, piece A) — the ONE place a hidden non-uniformity can bite (uniform Jacobian/box-distortion
  while identifying the residual EXACTLY with a `cornerComparator` at the deeper cut). And the **θ must be
  chosen `c'`-adaptively close to 1** at the borderline — a fixed `θ<1` would genuinely obstruct the exponent.
  Neither is a wall; both are LABOUR named with their exact discharge.
- **Next.** Hand this to the step tide as the `DecoratedStepHyp adm` build-order (§5). If a pen-and-paper
  check is wanted before the mountain: a fully-worked `b=2` shell-`j=1` adapted-minor CoV at a genuine binding
  cut (e.g. `(3,3,3)@t★=1`, `a=b=2`, `r=2`) — pin the uniform Jacobian constant + the exact residual
  identification `= cornerComparator (redChain 2 (3,3,3)) k jc`-integrand, the T-Obl3b core the tide formalises.
