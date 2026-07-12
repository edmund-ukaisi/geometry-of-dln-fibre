# T-Obl3b pin cert — the adapted-minor CoV for shells j≥1 (the "mountain" of the #5 step leg)

**Seat:** pen-and-paper WITNESS (pin + adversarial stress-test), genm-sj5-domination. **Date:**
2026-07-12. **NO Lean, NO build.** Exact algebra (Cauchy–Binet, sympy factorisation, exact-`ℕ`
minAdm/QIP recursion) + MC only as a guide. Decorrelated `local-codex-consult` (xhigh, conclusions
withheld): `codex/tobl3b-pin-{prompt,answer}.md`. Reproducible scripts under `scripts/tobl3b/`.

**Anchor:** `(3,3,3)@t★=1` — `a=b=2`, `r=min(a,b)=2`, `M₂=3`, deep tied product `Z=A₂∈box(3×3)`,
free corank block `A_cor∈box(2×3)`, freed corner `Γ∈box(2×2)`, `Q_b=A_cor·Z`, pivot energy
`w=frobSq(Γ'·Z)`. Shell `j=1` is the worked case; `j=0` (borderline) and `j=2` (saturated) mapped too.

**Consumed / read:** `final-assembly-design-cert.md` (§Obl-3b + §5 build-order + §Most-likely-to-break);
`offsector-il-design-cert.md` (§2b flag arithmetic + `scripts/verify_flag.py`); `s0-reduced-core-
fidelity-cert.md` (§S0.5 domination, the RATIONAL-`Base` refutation of exact-equality); the LANDED
`corankOffSector_bpos_le` / `_borderline_atBorder_le` (`RouteMSJOffSectorBPos`/`Borderline`),
`detGram_lintegral_box_lt_top`, `corankWeight_bpos_lt_top`, `freedSchurLoss_inner_peel_le` / `_bounded_le`
(`RouteMSJInnerDescent`), `cornerComparator_adm` / `exists_cornerComparator_adm` / `_decLoss`
(`RouteMSJCornerComparator`), `minStretch_comp_ge` (`RouteMSJSigMin`), `minAdm_redChain_succ_ge`
(`RouteMSJTransversality`), `posDef_gram_of_rank_eq`, `corank_survival_ae`; **the LANDED sorry-free
sibling `RouteMSJOnePeel334`** (`cornerSliceAtUnits_le` + `sumSqND_box_lt_top` — a worked shell-`j=1`
codim-rescue on the `(3,3,3,4)` chain).

---

## ★ VERDICT — the uniform constant + the residual identification PIN. One SHARPENING (Codex-caught, real).

**T-Obl3b closes as LABOUR for `c' < carrierThreshold(M) = ½·minAdm(M)`.** The adapted-minor CoV for
shells `1 ≤ j ≤ r−1` has a **uniform Jacobian** (the only ε-dependent factor is `|strong minor|^{−a} ≤
ε^{−a(M₂−j)}`, weak-singular-value-FREE — no hidden non-uniformity) and reduces the shell-`j` off-sector
integrand to the deeper `cornerComparator(redChain(t★+j) M)` integrand **by DOMINATION (a clean `≤`, NOT
an exact equality)** — matching the S0 refutation of exact-equality. The load-bearing exact facts:

```
PINS (labour): shell-j CoV (1<=j<=r-1) = Cauchy-Binet (M2-j)-minor chart (|det|>=eps^{M2-j}/√N,
weak-SV-free) -> Gram divisor det^{-a/2} = |strong minor|^{-a}·(strong SV prod)^{-a}·(1+O(σ_weak^2))^{-a/2}
(exact, sympy) -> STRICTLY-CONVERGENT reduced det-Gram weight (a-j < M2-b+1, 0/3161 violations) -> drop
nonneg residual (Base >= w_j >= 0, neg exponent) -> shell-j integrand <= const(eps)·(cornerComparator
(redChain(t★+j)) integrand at c'-½(a-j)(b-j)) -> arity-(L+1) IH.  Charge C_j=(a-j)(b-j)+minAdm(redChain
(t★+j)) >= minAdm(M), TIGHT at j=0 AND j=1 at the anchor (both binding).  Borderline a=M2-b+1 confined
to j=0 (theta, banked).  Saturated shell j=r: NO minor CoV (freed corner empty) -> deeper comparator's
OWN Morse codim-rescue (minAdm(redChain(t★+r)) charges the full codim; landed OnePeel334 pattern).
```

**The one thing that WOULD have been an obstruction — patched by the SHARPENING (Codex Q4, decorrelated):
the shell cover must be EXHAUSTIVE.** The design's "`ε₀ ≥ ε₁ ≥ … ≥ ε_r` (distinct decreasing)" leaves a
**real intermediate-band gap** `{σ_{M₂−j}(Z) ∈ (ε_{j+1}, ε_j)}` (swept: 76557/200000 uncovered `Z` for
`ε=[0.7,0.5,0.3]`; explicit escaper `σ=(0.9,0.4,0.1)`). **The tide MUST use a SINGLE threshold `ε`
(ε₀=ε₁=…=ε_r=ε): then the cover is exhaustive (0/200000 gaps).** Codex's specific witness `Z_δ=δI` (all
`σ_k=δ<min ε_j`) is actually caught by the saturated shell `S_r={σ_{M₂−r+1}<ε_r}` (`σ_2=δ<ε_2`) — an
arithmetic slip on its part — but the *category* it flagged (cover exhaustiveness + the all-small-`Z`
branch) is a genuine required check. Not a wall; a green-gate the tide must not skip.

---

## 1. THE ADAPTED-MINOR CoV — explicit, with the EXACT Jacobian (task deliverable #1)

**The object.** On shell `j` the LANDED per-fixed-full-rank-`Z` off-sector bound
(`corankOffSector_bpos_le`) is NOT integrable over the outer `Z` (its `Wenn(Z)=∫_box
det((A_cor Z)(A_cor Z)ᵀ)^{−a/2}` blows up as `σ_min(Z)→0`; MC guide `scripts/tobl3b/wenn_blowup.py`
gives `p_W→1` for `j=1`, `p_W→2` for `j=2` — matching the Cauchy–Binet derivation below). So we re-peel.

**The chart.** `Z=UΣVᵀ`, shell `j` = the top `M₂−j` singular values `≥ ε`, the bottom `j` weak (`<ε`,
`→0`). Write `B := A_cor·U` (`b×M₂`). **Cauchy–Binet (`scripts/tobl3b/jacobian_factor.py`, exact sympy):**

> `det((A_cor Z)(A_cor Z)ᵀ) = det(BDBᵀ) = Σ_{|S|=b} det(B_{:,S})² ∏_{k∈S} σ_k²`   (identity CONFIRMED)

For the anchor (`a=b=2, M₂=3`), split by whether `S` contains the weak index `3` (`σ₃=t`):

> `det = det(B_{:,12})²·σ₁²σ₂²  +  t²·[det(B_{:,13})²σ₁² + det(B_{:,23})²σ₂²]  =  (strong) + O(t²)`

and `lim_{t→0} det / [det(B_{:,12})²σ₁²σ₂²] = 1` (sympy). Since `det ≥ (strong term)`, the Gram divisor is
DOMINATED (safe direction) by the **weak-SV-free** strong expression:

> **`det((A_cor Z)(A_cor Z)ᵀ)^{−a/2} ≤ |det(B_{:,12})|^{−a} · (σ₁σ₂)^{−a}`,   `det(B_{:,12}) = b₁₁b₂₂ − b₁₂b₂₁`.**

`det(B_{:,12})` is the **strong `(M₂−j)`-minor of `A_cor·U`**: it contains NO `σ₃`/`t` (weak SV) —
confirmed symbolically. So the ONLY ε-dependent factor of the CoV Jacobian is `|strong minor|^{−a}`.

**The uniform bound (the "no hidden non-uniformity" check — task #1).** By Cauchy–Binet the sum of
squares of all `(M₂−j)`-minors of `Z` is `Σ (∏σ_strong)² ≥ σ₁²…σ_{M₂−j}² ≥ ε^{2(M₂−j)}`, so the **maximal**
minor `Δ` satisfies (`scripts/tobl3b/minor_jacobian.py`, exact + confirmed):

> `ε^{M₂−j}/√N ≤ |Δ| ≤ (M₂−j)^{(M₂−j)/2}·B^{M₂−j}`,   `N = C(M₂,M₂−j)·C(n,M₂−j)`,   `B` = box radius,

both **independent of the weak singular values** (`σ_{M₂−j+1},…,σ_{M₂}`). Numerically the minor is flat in
the weak SV `t` to 6 significant figures and scales `~C·σ_{M₂−j}` (better than the `ε^{M₂−j}` floor).
Anchor `j=1`: `|Δ| ≥ ε²/3`, so the Jacobian factor `|Δ|^{−a} = |Δ|^{−2} ≤ (3/ε²)² = 9ε^{−4}` — a fixed
ε-power, uniform on the shell interior AND at the shell boundary (the boundary between `S_j` and `S_{j-1}`
approaches `σ_{M₂−j+1}→ε` from below, still weak, minor unaffected). **PIN: the CoV Jacobian is bounded
above (`9ε^{−4}`) and below (box radius) by ε-powers, with NO dependence on the vanishing weak SVs.**
Codex Q1 concurs (UNIFORM): `|Δ|^{−q} ≤ N^{q/2}ε^{−(M₂−j)q}`, independent of the weak SVs; the exact
overall power `q` awaits the explicit peel formula (`q=a` here, from the Gram-divisor exponent).

**Banked pieces the CoV consumes:** `RouteMSJSigMin` (`minStretch` = smallest singular value, the shell
predicate), Cauchy–Binet (Mathlib `Matrix.det`-minor / `sum_sq`), `detGram_lintegral_box_lt_top` +
`corankWeight_bpos_lt_top` (the reduced weight, §2), `posDef_gram_of_rank_eq`, `corank_survival_ae`.

## 2. THE REDUCED WEIGHT IS STRICTLY CONVERGENT ON j≥1 — the crux that makes the mountain clean

**The KEY new exact fact.** After the minor eliminates the `j` weak directions, the leftover det-Gram
weight is over `(b−j)` corank rows in the `(M₂−j)`-strong subspace with exponent `(a−j)/2`. It is FINITE
(`detGram_lintegral_box_lt_top` at reduced dims) **iff**

> **`a−j < (M₂−j) − (b−j) + 1 = M₂−b+1`,   i.e.   `a < M₂−b+1+j`.**

At a binding cut `a ≤ M₂−b+1` (banked convexity + rank incidence). **Swept 3161 genuine binding cuts
(`scripts/tobl3b/shell_convergence.py`): 0 violations of `a ≤ M₂−b+1`.** Hence **for every shell `j≥1`
the reduced weight is STRICTLY convergent (no log, no θ-interpolation)** — the borderline equality
`a=M₂−b+1` bites ONLY at `j=0` (595/3161 cuts, handled by the banked `corankOffSector_borderline_
atBorder_le` with `θ<1`). The deeper shells are cleaner than shell 0: the freed corner `(a−j)(b−j)`
shrinks faster than the ambient `(M₂−j)`, so the reduced convergence MARGIN grows with `j`. Anchor `j=1`:
`a−j=1 < M₂−b+1 = 2` (strict). Codex Q2 concurs (STRICTLY-CONVERGENT, exact inequality `a−j<M₂−b+1`).

This is exactly the **codim-rescue** already LANDED sorry-free in `RouteMSJOnePeel334` for the sibling
`(3,3,3,4)`: a vanishing deep unit `‖X‖²→0` is closed because the Morse integral `∫_box(∑X²)^{−w·c'}`
CONVERGES near the origin (`sumSqND_box_lt_top`, finite `⟺` codim large enough), NOT because the
integrand is bounded there. T-Obl3b generalises `OnePeel334` from (i) coordinate-aligned test directions
to the **Cauchy–Binet minor** (arbitrary weak direction) and (ii) `j=1` to general `j`.

## 3. THE EXACT RESIDUAL IDENTIFICATION — a clean `≤` (DOMINATION), not equality (task #2)

**It is a DOMINATION, not an exact equality** — and this is the correct, honest answer (task asked which).
The corner-minimised base `Base = w_j + ‖Ccross·(I − P_{Q_b})‖²_F`, `P_{Q_b} = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`, is a
RATIONAL function of the deeper parameters (it carries the Gram-inverse projection) — NOT the polynomial
`cornerComparator` loss `commonDivisor(u)²·frobSq(prod(redChain(t★+j)))`. The S0 cert already REFUTED
exact-equality at `j=0`; the same holds at `j≥1`. The valid target (safe upper-bound direction):

> `(w_j + R)^{−e} ≤ w_j^{−e}` for `R ≥ 0`, `e = c'−½(a−j)(b−j) > 0`  (sympy-confirmed monotonicity),

with `w_j = frobSq(Γ'_{t★+j}·Z_strong)` the deeper comparator loss (`cornerComparator_decLoss`, exact).
So, assembling §1+§2+§3:

> **`(shell-j off-sector integrand) ≤ const(ε) · (cornerComparator(redChain(t★+j) M) k jc integrand at
> exponent c'−½(a−j)(b−j))`**,   `const(ε) = Cresid · [reduced-Wenn on the ε-sector] · ε^{−a(M₂−j)}`,

a pointwise `≤` closed by `lintegral_mono`. The shell indicator is DISCARDED before the IH (full-box only
decreases the integral; Codex Q4-design warning: invoke the full-box IH outright, do NOT reapply the
per-`Z` conditional estimate). The comparator is admissible (`cornerComparator_adm` / `exists_cornerComparator
_adm`) and its `DecoratedBoxThresholdFinite` is given by the step's arity-`(L+1)` decorated IH. Codex Q3
concurs (DOMINATION, clean `≤`, the reduced base carries `‖C(I−P_Q)‖²` — rational, not the comparator).

## 4. CHARGE CHECK AT THE ANCHOR (task #3) — charges add EXACTLY, TIGHT at j=0 AND j=1

`minAdm(3,3,3)=7`, `carrierThreshold=7/2`. `t★=1`: `a=b=2`, `r=2`. Both `t=1` and `t=2` are binding cuts.

| shell `j` | freed corner | charge `½(a−j)(b−j)` | `redChain(t★+j)` | `minAdm` | comparator charge | `C_j` | `½C_j` | reduced-conv `a−j<M₂−b+1` |
|---|---|---|---|---|---|---|---|---|
| 0 | 2×2 | 2 | `(1,3)` | 3 | 3/2 | **7** | 3.5 | borderline `a=M₂−b+1=2` (θ) |
| 1 | 1×1 | 1/2 | `(2,3)` | 6 | 3 | **7** | 3.5 | `1<2` ✓ strict |
| 2 | 0×0 | 0 | `(3,3)` | 9 | 9/2 | **9** | 4.5 | saturated (no minor CoV) |

**Task #3 confirmed:** `C₁ = (a−1)(b−1) + minAdm(redChain 2 (3,3,3)) = 1 + minAdm(2,3) = 1 + 6 = 7 =
minAdm(3,3,3)` — TIGHT (equality), zero slack, since `t★+1=2` is also binding. The shell-`1` budget
exactly saturates `carrierThreshold(M)=7/2`; `c' < 7/2 ⟹ c'−½ < 3 = carrierThreshold(2,3)` STRICTLY, so
the arity-`(L+1)` IH on `(2,3)` (arity 2 < arity 3) fires. Charges add via `carrierThreshold_shift` +
`minAdm_redChain_succ_ge`. Swept: `C_j ≥ minAdm(M)`, 0 undershoots / 3161 cuts (banked `verify_flag`).

## 5. ADVERSARIAL — hunted for the uniform-constant break (task #4)

- **Jacobian degenerates in the shell interior?** NO. The Jacobian factor `|strong minor|^{−a}` is bounded
  `[box^{−a(M₂−j)}, (√N/ε^{M₂−j})^{a}]`, weak-SV-free (§1, sympy + sweep). No interior/boundary blow-up.
- **Residual fails to be dominated by the deeper comparator?** NO. Drop-the-nonneg-residual is unconditional
  (`R≥0`); `w_j` is the genuine `cornerComparator` loss (`cornerComparator_decLoss`).
- **The pivot energy `w=frobSq(Γ'Z)` ALSO degenerates as `Z→0` and breaks the const?** NO. The domination
  needs NO pointwise lower bound on `w_j`; the `{w_j→0}` locus is inside the comparator's own box and closed
  by the IH (the comparator is admissible; its finiteness is the IH), matching the S0.5 "drop residual, IH
  on the clean comparator" pattern.
- **★ Cover gap / all-small-`Z` escape (Codex Q4 — the ONE real find).** With **distinct decreasing** `ε_j`
  the shells leave a genuine intermediate-band gap `{σ_{M₂−j}∈(ε_{j+1},ε_j)}` (76557/200000 `Z` uncovered,
  `scripts/tobl3b/exhaustiveness.py`; explicit `σ=(0.9,0.4,0.1)`, `ε=[0.7,0.5,0.3]`). **FIX: single
  threshold `ε` — then exhaustive (0/200000 gaps).** The all-small-`Z` region (`Z→0`, incl. genuine
  rank-drops) is the **saturated shell** `S_r`, where the freed corner is empty (`(a−r)(b−r)=0`, at the
  anchor `a=b=2` BOTH `a−r=b−r=0`, so `A_cor` and `Γ` fully absorb) and there is **NO minor CoV / no Gram
  divisor** — Codex's "the `(M₂−r)`-minor can be `≤δ`, no uniform inverse-Jacobian" is CORRECT and is
  precisely WHY `S_r` needs a different mechanism: the deeper comparator `redChain(t★+r)` reads the full `Z`
  and its `minAdm` charges the FULL codimension, so `Z→0` is covered by that comparator's own Morse
  codim-rescue (landed `sumSqND_box_lt_top`), NOT by the minor chart. Saturation at `r=min(a,b)` is
  ESSENTIAL: cuts `t★+j` for `j>r` are illegal (`t★+r=min(M₀,M₁)`).

**No obstruction survived. One required green-gate: the exhaustive single-`ε` cover.**

## 6. DECORRELATED CODEX VERDICT (conclusions withheld in the prompt)

`codex/tobl3b-pin-{prompt,answer}.md` (xhigh; F1–F5 supplied — the banked off-sector bound, the `Wenn`
blow-up, the Cauchy–Binet minor, the charge fact — my four conclusions WITHHELD). **Codex CONCURS on the
three load-bearing points and SHARPENS the fourth:**
- **Q1 UNIFORM** — `ε^{M₂−j}/√N ≤ |Δ| ≤ (M₂−j)^{(M₂−j)/2}B^{M₂−j}`, weak-SV-independent; Jacobian `|Δ|^{−q}
  ≤ N^{q/2}ε^{−(M₂−j)q}` (independently re-derived).
- **Q2 STRICTLY-CONVERGENT** — exact `a−j < M₂−b+1`; shell-0 borderline becomes strict for every `j≥1`,
  no new `θ` (independently re-derived).
- **Q3 DOMINATION** — the reduced base carries `‖C(I−P_Q)‖²_F` (rational), so a clean `≤`, not equality;
  independently flagged the "explicit shell-`j` algebra still owed."
- **Q4 (its BREAK claim, adjudicated)** — its `Z_δ=δI` witness is actually caught by `S_r` (arithmetic
  slip: `σ_2=δ<ε_2`), so NOT a genuine escape; but its *category* (cover exhaustiveness + the all-small-`Z`
  branch) is real — verified as the distinct-`ε` intermediate-band gap, patched by single-`ε`. Its
  suggested fixes ("normalised annulus / dyadic radial shells / a terminal no-minor domination lemma") are
  exactly the single-`ε` exhaustive cover + the saturated-shell Morse rescue. No inference of mine was fed
  in; the concurrence is decorrelated.

---

## 7. FOR THE T-Obl3b TIDE — banked pieces consumed + owed obligations (Lean build-order)

**Target:** `deeperFlag_shell_le` (build tile #2 of `final-assembly-design-cert.md` §5). Statement shape:
for `1 ≤ j ≤ r−1`, on the shell `S_j` (single-`ε` cover),
`(shell-j off-sector integrand) ≤ const(ε)·(cornerComparator(redChain(t★+j) M) k jc integrand at
c'−½(a−j)(b−j))`, closed by the step's decorated IH; the saturated `S_r` via the deeper comparator's Morse
codim-rescue; `S_0` via the banked borderline `θ`.

**BANKED (consume as black boxes):**
- `RouteMSJSigMin.minStretch` / `minStretch_comp_ge` — the singular-value shell predicate `{σ_{M₂−j}≥ε}`.
- Cauchy–Binet (Mathlib `Matrix` minor / `det` expansion) — the `(M₂−j)`-minor `Δ`, `|Δ|≥ε^{M₂−j}/√N`.
- `detGram_lintegral_box_lt_top` (`hrn : r≤n`, `a < n−r+1`) + `corankWeight_bpos_lt_top` — the reduced
  STRICTLY-convergent weight at reduced dims `(a−j, b−j, M₂−j)`.
- `corankOffSector_bpos_le` (convergent regime) / `corankOffSector_borderline_atBorder_le` (`j=0`, `θ<1`).
- `freedSchurLoss_inner_peel_le` (atom, `Q_bQ_bᵀ` PosDef) / `_bounded_le` (bounded, `w>0`) — the two bricks.
- `cornerComparator_adm` / `exists_cornerComparator_adm` / `cornerComparator_decLoss` — the deeper `D'`.
- `minAdm_redChain_succ_ge` (convexity) + `exists_binding_cut` + `carrierThreshold_shift` — charges add.
- `posDef_gram_of_rank_eq`, `corank_survival_ae`, `Core.RankLocusClosed` — a.e. full-rank + finite strata.
- **`RouteMSJOnePeel334.cornerSliceAtUnits_le` + `sumSqND_box_lt_top`** — the LANDED codim-rescue template
  for the SATURATED shell (Morse, no minor CoV) and the domination pattern for `j≥1`.

**OWED (the T-Obl3b LABOUR):**
1. **The minor-CoV lemma** (`1≤j≤r−1`): the Cauchy–Binet `(M₂−j)`-minor chart, the Gram-divisor
   factorisation `det^{−a/2} ≤ |Δ|^{−a}·(reduced weight)` (§1, exact), the `const(ε)` assembly. The uniform
   Jacobian and the exact factorisation are PINNED here; the Lean labour is the measure/CoV plumbing.
2. **The single-`ε` EXHAUSTIVE cover** (`RankLocusClosed` + `RouteMSJSigMin`) — **do NOT use distinct
   decreasing `ε_j`** (proven gap, §5). Finite (`r+1` pieces), measurable, summed by `ENNReal` subadditivity.
3. **The saturated-shell domination** via the deeper comparator's Morse codim-rescue (no minor CoV) — clean
   at `a=b` (`S_r` fully absorbs `A_cor`,`Γ`); the `a≠b` `S_r` (surviving `(b−a)` corank rows, exponent-0
   Gram) is a further check the tide should green-gate (the anchor `a=b=2` is the clean case).

---

## Close

- **Firmest result (pin cert, decorrelated-confirmed).** The adapted-minor CoV for shells `1≤j≤r−1`
  **PINS**: (i) uniform Jacobian — the only ε-dependent factor is `|strong minor|^{−a} ≤ ε^{−a(M₂−j)}`,
  weak-SV-FREE (exact sympy factorisation `det^{−a/2}=|Δ|^{−a}(σ_strong)^{−a}(1+O(σ_weak²))^{−a/2}`); (ii)
  the reduced weight is STRICTLY convergent (`a−j<M₂−b+1`, 0/3161 violations — the deeper shells are
  cleaner than the `j=0` borderline); (iii) the residual is a clean `≤` DOMINATION (not equality — the base
  is rational, S0-consistent); (iv) charges add, TIGHT at `j=0` and `j=1` at the anchor (`C₁=1+6=7=minAdm`).
  The mechanism is a LANDED sorry-free reality (`OnePeel334` codim-rescue) generalised to the minor chart.
- **Most likely to break it (the ONE required gate).** The **exhaustive single-`ε` cover** — the design's
  distinct decreasing `ε_j` leaves a real intermediate-band gap (Codex-caught, 76557/200000). Fix: single
  `ε`. And the **saturated shell** must go via the deeper comparator's Morse codim-rescue (no minor CoV —
  the minor genuinely fails at all-small-`Z`, which is why saturation at `r` is essential), with the `a≠b`
  `S_r` a further green-gate. Neither is a wall; both are named with their exact discharge.
- **Next.** Hand this to the T-Obl3b tide as build tile #2 (§7): the minor-CoV lemma + the single-`ε`
  exhaustive cover + the saturated-shell Morse rescue. The uniform constant and the exact residual `≤` are
  PINNED; the residual is Lean measure/CoV LABOUR, not new math. If a further pen-and-paper is wanted before
  the build: the `a≠b` saturated shell (e.g. `(3,4,4)@t★` with `a≠b`) to pin the surviving-`(b−a)`-corank
  domination — the one anchor-untested corner of the saturation mechanism.
