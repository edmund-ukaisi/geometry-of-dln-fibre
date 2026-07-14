# T-Obl3b `s≥3`-large-`x` waist — recovering the Vandermonde charge: **MODERATE (rational, no SVD density)**

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.** Exact symbolic / exact-rational
algebra for every load-bearing identity (scripts banked at `scripts/routeC/vand/`; reproduce the same steps);
Monte-Carlo only as a guide. Decorrelated `local-codex-consult` (xhigh, my Cayley conclusion WITHHELD — prompt
framed "adjudicate either direction, is it recoverable or is the SVD density forced?"):
`codex/tobl3b-s3largex-vandermonde-{prompt,answer}.md`.

**The ONE truth-value.** For `s≥3` waists with large `x`, where route C's rational triangular Gram–Schmidt
chart UNDERSHOOTS `minAdm` (misses the inter-singular-value repulsion `∏_{i<j}|σᵢ²−σⱼ²|`; `(4,3,4)`: charge
`9 < 10`; `(5,4,6)`: `17 < 18`): does a rational construction (nested blow-up of the collision locus
`σᵢ=σⱼ`, or another rational device) RECOVER the missing Vandermonde charge — so route C's methodology
EXTENDS, MODERATE, no SVD density — or is the orthogonal SVD/Weyl density GENUINELY FORCED (HEAVY,
research-level Mathlib build)?

---

## ★ HEADLINE VERDICT — **MODERATE (RATIONAL-RECOVERABLE). The orthogonal SVD/Weyl DENSITY is NOT forced.**

The missing repulsion charge `∏_{i<j}|σᵢ²−σⱼ²|` is recovered by an **explicit RATIONAL chart** — the
**Cayley (stereographic) parametrisation of the eigen-frame** — in which the Vandermonde appears as a
**polynomial Jacobian factor** in the eigenvalue coordinates, and the frame integrates against a **rational,
integrable density**. This chart feeds the banked `MeasureTheory.Function.Jacobian` CoV directly. **No abstract
Haar-on-`O(s)`, no abstract Stiefel manifold `V_s(ℝ^z)`, no coarea, no transcendental Weyl density** — the very
machinery the recon (`svd-density-mathlib-recon.md`) found absent from Mathlib v4.29 is **not needed**. So the
"HEAVY = the Vandermonde forces the research-level orthogonal-density build" hypothesis is **FALSE**.

**Two precisions that keep the label honest:**
- **It is heavier than pure route C.** Route C's *methodology* (rational charts, `det`-power Jacobians, banked
  general CoV + banked qPeel, no abstract density) extends, but the *specific chart* upgrades from the
  triangular Cholesky flag to the **Cayley spectral chart**, whose Jacobian is `∏|λᵢ−λⱼ|·det(I+K)^{−(s−1)}`.
  For a **fixed** small `s` this is an explicit `ring`/`det`-checkable identity (like route C's 6×6 det at
  `(3,2,3)`, but larger — a 12×12 det at `(4,3,4)`). For **general `s`** it is the classical real-symmetric
  spectral (β=1 SVD) Vandermonde Jacobian — **rational, closed-form, mathematically proved, but not banked in
  Mathlib**; that identity is the one genuinely-new brick. It is *moderate-heavy labour, not research-level*:
  no missing measure-theoretic primitive, only an algebraic determinant identity + the banked CoV.
- **The "nested blow-up" framing is a red herring.** No blow-up of the discriminant / collision locus
  `{σᵢ=σⱼ}` is needed for **finiteness**. The Vandermonde is a **numerator** factor that **vanishes** on the
  collision locus (codim 2 in `Sym(s)`, order-1 zero); it *helps* convergence. Route A's one-line
  ordered-chamber monomial bound `∏_{i<j}|σᵢ²−σⱼ²| ≤ ∏σᵢ^{2(s−i)}` (each factor bounded, safe direction)
  suffices. Resolving `{σᵢ=σⱼ}` to normal crossings (the braid-arrangement blow-up) would only be needed to
  read off the *exact* RLCT as a monomial — not for the finiteness target here.

---

## Part 1 — The exact charge accounting: what is missing, and where (`scripts/routeC/vand/s3_vand_charge.py`)

The Lebesgue measure of the deep layer, in singular-value form, is (classical; route A):

    dA₁  ~  ∏_j σ_j^{z−s} · ∏_{i<j}|σ_i²−σ_j²| · dσ · dU · dV,   U∈O(s), V∈V_s(ℝ^z).

Per-mode radial power on the ordered chamber: route C's triangular chart gives `h_j^C = z−j = (z−s)+(s−j)`;
the SVD/Weyl gives `h_j^{SVD} = z+s−2j = (z−s)+2(s−j)`. **The difference is exactly one staircase `(s−j)`
per mode** — the "second half" of the Vandermonde that the Cholesky pivots (which are NOT the eigenvalues)
miss. After the ambient cap `min(x, h_j+1)`:

| `(x,s,z)` | routeC `2c` | `minAdm` | undershoot | where |
|---|---|---|---|---|
| `(3,2,3)` | 5 | 5 | 0 | (repulsion wasted by cap) |
| `(4,3,4)` | 9 | 10 | **1** | **mode 2** (`cap 3→4`; needs `|σ₂²−σ₃²|`) |
| `(5,4,6)` | 17 | 18 | **1** | **mode 3** |
| `(3,3,4)`, `(4,3,5)` | = | = | 0 | (cap wastes it) |

At `(4,3,4)`: `h^{SVD}+1 = (6,4,2) →min(4,·)→ (4,4,2)`, `Σ=10=minAdm`, `c*=5`. Mode 1's repulsion is capped
(wasted), mode 3 has no deficit; **only mode 2 needs it, and needs exactly 1** — the repulsion `|σ₂²−σ₃²|` of
the two smallest singular values.

---

## Part 2 — The rational device: Cayley spectral chart (EXACT certificates)

**Claim.** The eigen-frame `Q∈SO(s)` — the "transcendental" part of the spectral decomposition
`G = QΛQᵀ` (`Λ=diag(λ_j)`, `λ_j=σ_j²`) — admits a **rational** Cayley parametrisation `Q(K)=(I−K)(I+K)^{−1}`,
`Kᵀ=−K` (`s(s−1)/2` free skew entries), under which the map `Φ:(Λ,K)↦G` is **rational** with a **rational
Jacobian** carrying the Vandermonde as a **polynomial** factor:

    |det DΦ| = 2^{s(s−1)/2} · ∏_{i<j}|λ_i−λ_j| · det(I+K)^{−(s−1)}.

**Exact verifications (banked scripts):**
- **`s=2` (`s2_stereo_vandermonde.py`, exact sympy).** Tangent-half-angle chart on `Sym(2)`,
  `(μ₁,μ₂,t)↦(p,q,r)`:  `det = (μ₁−μ₂)/(1+t²)`. Trace and det of the matrix are preserved exactly. The
  Vandermonde `(μ₁−μ₂)` is the polynomial factor; the frame factor `1/(1+t²)` is the SO(2) stereographic Haar
  density, `∫_ℝ dt/(1+t²)=π` (finite).
- **`s=3` (`s3_cayley_exact_points.py`, EXACT rational, 4 points, `MATCH=True`).**
  `det DΦ = −8·(λ₁−λ₂)(λ₁−λ₃)(λ₂−λ₃)/(1+a²+b²+c²)²`. The `−8 = −2^{s(s−1)/2}` constant and the
  `det(I+K)^{−(s−1)} = (1+a²+b²+c²)^{−2}` density are exact; the ratio `detJ/Vandermonde` is
  `λ`-**independent** (confirmed by varying only `λ`, `s3_cayley_numeric.py`).
- **General density form (`cayley_haar_density_form.py`, exact).** `det(I+K)=1+‖K‖²` for `s≤3`; for `s=4`,
  `det(I+K)=1+‖K‖²+Pf(K)²` (Pfaffian) — in all cases `det(I+K)^{−(s−1)}` is the **rational** Cayley–Haar
  density. `∫_{SO(3)}` version `∫_{ℝ³} 8/(1+‖K‖²)² dK = 8π²` (finite) — the frame integrates to a **constant**
  (`frame_density_integrability.py`).
- **Rectangular part is also rational (`rect_svd_rational_chart.py`, exact-numeric).** Full rational SVD chart
  `A₁ = U(t)ΣV(flag)ᵀ` at `(s,z)=(2,3)` — `U` stereographic `O(2)`, `V` iterated rational sphere-flag (route
  C's dominant-coordinate mechanism for the row-space in `ℝ^z`), `Σ` radials. The σ-Jacobian is exactly
  `σ₁σ₂·|σ₁²−σ₂²|` = `∏σ^{z−s}∏|σ_i²−σ_j²|` (`z−s=1`); the frame factor is σ-independent (integrates to a
  constant). **So the rectangular/Stiefel part is handled by rational sphere-flags — no abstract Stiefel.**

**The loss reduces to the qPeel form, rationally.** With `B = A₀Q(K)` (orthogonal right-mult, `|det|=1`,
banked measure-preserving CoV), `tr(MG)=Σ_j λ_j‖B_j‖²`, `B_j∈ℝ^x`. This is exactly the banked
`qPeelIntegral` corner-slice (radial `σ_j` power `h_j`, deep Morse block `B_j∈ℝ^x`, `m_j=x−1`).

---

## Part 3 — Anchor `(4,3,4)` reaches `½·minAdm` TIGHT; the recursion is trivial (task items 1–2)

- **Charge recovered (task item 2).** With the Cayley spectral chart the per-mode radial power is the full
  `h_j^{SVD}=z+s−2j=(6,4,2)−1`; on the ordered chamber `∏|σ_i²−σ_j²|≤∏σ_i^{2(s−i)}` (elementary), the qPeel
  threshold is `½·Σ_j min(x,h_j^{SVD}+1) = ½·minAdm(4,3,4) = 5`. **Mode 2 gains exactly the missing 1**
  (`cap 3→4`). TIGHT.
- **Collision locus (task item 1), literally.** `{σ_i=σ_j}` = `{disc(G)=0}` has **codim 2** in `Sym(s)`
  (`s=2`: `{p=q, r=0}`; the Vandermonde `√((p−q)²+4r²)` is a distance-to-locus, order-1 zero). Because it is a
  **vanishing numerator** on a codim-2 set, it is trivially integrable — **no blow-up delivers charge here;
  the chart already carries the Vandermonde as its Jacobian.** The blow-up would only monomialise the braid
  arrangement `∏(λ_i−λ_j)` for an *exact* RLCT readout, which the finiteness target does not require.
- **Termination / atlas (task item 3, first half).** The device does **not** recurse into a deepening
  blow-up tree. `SO(s)` is covered by a **single** Cayley chart minus a measure-zero set (rotations with
  `det(I+K)=0`); `O(s)` needs one extra reflection sheet; the ordered chamber needs an `s!` symmetrisation
  constant and a finite sign/permutation cover. The row-space `V_s(ℝ^z)` is a **finite** iterated
  rational-sphere-flag atlas (route C's dominant-coordinate cover). Finite depth, finite chart count.

---

## Part 4 — VERDICT + build-path

### **MODERATE — RATIONAL-RECOVERABLE. Route C's methodology extends; the SVD/Weyl DENSITY is NOT forced.**

The uniform `∀M` waist base case is buildable **without** the absent Mathlib manifold machinery. The one
genuinely-new brick is the **rational spectral-Jacobian identity** (Vandermonde × Cayley–Haar), classical and
closed-form — heavier than pure route C, but elementary in kind (a determinant identity + the banked CoV), not
research-level.

**Build-path (dependency order). BANKED unless flagged NEW.**
1. Rational SVD chart on `A₁` (per fixed `s`, or general via the spectral-Jacobian identity):
   `A₁=U(K)ΣV(flag)ᵀ`, `U` Cayley on `SO(s)`, `V` iterated rational sphere-flag on the row-space, `Σ` radials.
   **[NEW]** Jacobian `|det| = ∏σ^{z−s}∏|σ_i²−σ_j²|·det(I+K)^{−(s−1)}·w_V(flag)`.
   For fixed `s` a `ring`/`Matrix.det` computation (12×12 at `(4,3,4)`); general `s` = the classical spectral
   (β=1 SVD) Vandermonde Jacobian.
2. Reduce the loss `tr(MG)=Σλ_j‖B_j‖²` via `B=A₀Q(K)` (orthogonal CoV, `|det|=1`). **[BANKED]** pattern
   (`RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ`; here `Q(K)` is the explicit rational frame).
3. Ordered-chamber monomial bound `∏|σ_i²−σ_j²|≤∏σ_i^{2(s−i)}` + `s!` symmetrisation. **[NEW, elementary]**
   (per-factor `|σ_i²−σ_j²|≤σ_i²` on the chamber).
4. Frame-density finiteness `∫det(I+K)^{−(s−1)}dK<∞` + bounded sphere-flag factors → frame integrates to a
   constant. **[NEW, elementary rational integral]** (`8π²` for `SO(3)`).
5. `MeasureTheory.Function.Jacobian.lintegral_image_eq_lintegral_abs_det_fderiv_mul` on each chart. **[BANKED]**
6. `qPeelIntegral_lt_top` with `h_j=z+s−2j` (truncated `min(h_j,x−1)`), `m_j=x−1`; `c<½·minAdm`. **[BANKED,
   sorry-free]** (`RouteMSJCorankQ`).
7. Finite rational-chart atlas (dominant-coord × sign × permutation/chamber × Cayley sheet), a.e. exhaustive.
   **[NEW, measurable-cover pattern]** (analogous to banked `RouteMSJShellCover.lintegral_le_sum_finCover`).

**Banked vs new.** BANKED: general Jacobian CoV, orthogonal-CoV `B=A₀Q`, `qPeelIntegral_lt_top`, shell/cover
assembly, `frobSq`/`tr(MG)` API, the `Σmin(x,z+s+1−2j)=minAdm` identity (405 chains, route A).
NEW (all rational, no new Mathlib primitive): the spectral-Jacobian identity (item 1, the substantial one —
`ring`-checkable per fixed `s`, classical closed-form for general `s`), the chamber bound + `s!` (item 3),
frame-density finiteness (item 4), the rational-chart atlas (item 7). **Strictly cheaper than the SVD/Weyl
density** (no Stiefel manifold, no Haar-on-`O(s)`, no coarea, no Wishart).

---

## Part 5 — Decorrelated Codex (independent concurrence)

Codex (xhigh, conclusion withheld, "adjudicate either direction") **independently reached the SAME device**
and verdict:
- **VERDICT: RATIONAL-RECOVERABLE** — "Cayley spectral charts algebraically reproduce Vandermonde using
  ordinary change-of-variables."
- Independently wrote `Q=(I−K)(I+K)^{−1}`, `G=QΛQᵀ`, and the **same closed form**
  `|J|=2^{s(s−1)/2}det(I+K)^{−(s−1)}∏|λ_i−λ_j|`, combining with the rectangular factor
  `det(G)^{(z−s−1)/2}` to give `∏σ^{z−s}∏|σ_i²−σ_j²|`, and `B=A₀Q`, `tr(MG)=Σλ_j‖B_j‖²`, `|J_B|=1`.
  Its own sympy prediction (radials `=σ`) **matched my exact-rational Jacobian up to the orientation sign**
  (`codex_cayley_sigma_check.py`: `|det| = 64·∏σ·∏(σ_i²−σ_j²)/det(I+K)²`, exact — I RAN it, did not trust it).
- **`(4,3,4)`**: "mode 2 gains exactly the required 1", reaches `minAdm=10`, `c*=5` — matches Part 1.
- **General `s`**: "Yes, for all `s`. The classical real-symmetric spectral / β=1 SVD Vandermonde Jacobian…
  mathematically proved, though not banked in Mathlib." **"No discriminant blow-up is needed: collisions make
  the numerator vanish; chamber monomial bounds suffice"** — matches the red-herring finding.
- **Shared residual risk (its item 5, preserved as inference).** "The vulnerability is formal-global:
  constructing finite injective sign/permutation Cayley charts and proving their complements null using only
  banked CoV." Cheapest test it names: formalise the `s=3, z=4` rational chart, compute its 12×12 Jacobian,
  prove the chart partition a.e. exhaustive. (In an earlier, wider-scoped run Codex flagged that "`D_q` is the
  actual measure exponent" is *an inference, not a consequence of the corner algebra* without the pushforward
  identity — i.e. the spectral-Jacobian identity of build-item 1 is the load-bearing obligation; consistent
  with this cert.)

---

## Close

- **Firmest result.** The missing Vandermonde repulsion charge **IS recovered by an explicit RATIONAL chart**
  (Cayley/stereographic eigen-frame), with the Vandermonde as a **polynomial Jacobian factor**
  (`s=2`: `(μ₁−μ₂)/(1+t²)` exact; `s=3`: `−8∏(λ_i−λ_j)/(1+‖K‖²)²` exact-rational, `MATCH=True`) and the frame
  a rational integrable density (`det(I+K)^{−(s−1)}`, `∫<∞`). Feeds the banked general CoV + banked qPeel to
  `½·minAdm` TIGHT at `(4,3,4)`. **The transcendental orthogonal SVD/Weyl density / abstract
  Stiefel–Haar–coarea is NOT forced.** No blow-up of the collision locus is needed. Decorrelated Codex derived
  the identical device, formula, and no-blow-up conclusion, and its exact Jacobian matched mine (I ran it).
- **Most likely to break it.** (i) The **general-`s`** spectral-Jacobian identity `∏|λ_i−λ_j|det(I+K)^{−(s−1)}`
  — proved for `s≤3` here (exact), classical for all `s`, but a real (rational, non-research-level) Lean brick;
  if only fixed-`s` anchors are needed it is `ring`-checkable, if the base case must be uniform in `s` it is
  the substantial piece. (ii) The **a.e.-exhaustive finite atlas** (sign/permutation/chamber × Cayley sheet ×
  dominant-coordinate row-flag) — standard, but must be discharged, not waved (the same obligation route C
  carries, with more sheets). (iii) The `Q(K)`-dependence of the `B=A₀Q` box after rotation (bounded via
  `Q`'s entries) — a frame-constant step, benign.
- **Next construction / consult.** Formaliser: prototype the `(4,3,4)` module — the `s=3` Cayley Jacobian is
  done here (exact); the new labour is the 12×12 composite chart det and the rational-atlas exhaustiveness.
  If the controller needs uniform-`s`, scope the general spectral-Jacobian identity as its own module
  (classical, rational). The `s≤2` waists stay on pure route C (cheaper); this Cayley extension is only for
  the `s≥3`-large-`x` widths where route C undershoots.
