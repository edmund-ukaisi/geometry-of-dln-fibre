# §5 cover-seam de-risk — the det-inverse dominant-minor cover on `(3,3,3,4)`, `q∈{1,2}`

**Seat:** pen-and-paper (obstruction — adjudicate one truth-value: does a Beta-divergence survive on the
dominant-minor cover seam?). **Date:** 2026-07-11. **NO Lean.** **Charge (team-lead):** de-risk the §5
lane's single flagged risk (`peel-buildplan.md` §4.4) — the det-inverse dominant-minor cover seam of the
decorated inner induction (B5-desc), on the contracting-tail slice `M=(3,3,3,4)`, `q∈{1,2}`. Run the
composed inner descent END-TO-END and adjudicate whether the seam WALLS.

**Exact algebra (mine):** `/tmp/seam/{acct,seam_algebra,atomtrap_and_corner,majorant_center,bartlett_singleminor,center_theta}.py`
(sympy exact identities + Gamma-pole thresholds; MC only as a guide). **Decorrelated:** own
`local-codex-consult` (xhigh, my conclusion WITHHELD — I asked the open "does it wall?" hunting for the
divergence): `codex/coverseam-{prompt,answer}.md`. Codex reached the same verdict term-for-term and
supplied two sharpenings, both adopted.

---

## VERDICT (headline): the seam does NOT wall. NO Beta-divergence survives.

**No Beta/boundary/seam divergence survives on the dominant-minor cover seam.** The seam is a
Lebesgue-null set across which (i) partitioning creates no boundary term (it is multiplication by
indicator functions, not integration-by-parts), (ii) the integrand `det(Q_b Q_bᵀ)^{−a/2}` is `O(1)`
(singular only on `{rank Q_b < b}`, which sits at `σ_min = O(1)`, off the seam), and (iii) the per-chart
transition Jacobian is **exactly `1`** on the seam. The `⅟→⁻¹` det-inverse `|det A_S|^{−b}` is genuinely
cancelled by the shrinking image (`vol(A_S·box) = 2^{bm}|det A_S|^{b}`); the atom's `s⁻¹` pole is a
**full-space** artifact the box never has.

The **only** genuine divergence is the endpoint `a = a_c = min(tail)−b+1` (a true logarithmic divergence
from `Y` dropping rank by one, correctly excluded by the strict `c' < ½·minAdm`), and the **only** false
wall is a *crude* per-chart bound that extends the shrinking image to a fixed box — a divergence of the
BOUND, not of the integral, and avoidable.

Sharper still: **the det-inverse cover is not needed for Level-A finiteness at all.** The corank-Gram box
integral is bounded up to the exact threshold by the single **`m`-column Cauchy–Binet lower bound**
`det(Q_b Q_bᵀ) ≥ det(Q_S Q_Sᵀ)` (`|S|=m`, task #112 banked) — reducing to a **square-middle `(b,m,m)`
base** with matched threshold and NO det-inverse, NO cover, NO seam — or, decorrelated, by the
Gaussian/Bartlett two-Wishart moment. So the seam is de-risked twice over: it does not wall, and it is
side-steppable.

The composed slice runs end-to-end: exponent accounting **sums to `7 = minAdm(3,3,3,4)`** (charges ADD via
the shared corner, `7/2` threshold), and the strict `<` is preserved through the descent-ℕ / log-borderline.

---

## 0. Framing note — the slice, honestly (one shorthand reconciled)

`M = (3,3,3,4)` is depth `L=3`: `A₀:3×3`, `A₁:3×3`, `A₂:3×4`, product `3×4`. `minAdm(3,3,3,4)=7`
(re-verified via the banked layer-peel recursion), binding front cuts `t∈{1,2}` (values
`{t:0→9,1→7,2→7,3→8}`). At the binding corank-2 cut `t=1` the Schur split emits corank block `Γ:2×2` and a
deeper `Q_b = Y·A₂`, `Y:(3−t)×3`, `A₂:3×4`. So `q ∈ {1,2}` in the charge is the **corank block width
`b = M₁−t = 3−t`**, and the corank-Gram chain is `𝒞 = (b, M₂, M_last) = (b, 3, 4)` — a **contracting
tail** (`M₂=3 < M_last=4`, so `min(tail) = 3 < 4`, the twist bites: threshold `3−b+1` vs free `4−b+1`).

The charge's shorthand "tail `(1,2) ⟹ reduced chain `(q,1,2)`" I could not reconcile to a literal
corank-Gram chain (`(q,1,2)` with `q=2` is degenerate: `b>min(m,q)` ⟹ `det Q_b ≡ 0`). It is immaterial to
the seam mechanism, which is identical for any `m<q` contracting tail. I therefore ran the **honest**
`(3,3,3,4)` chains `(b,3,4)`, `b∈{1,2}` (`M₂=3<M_last=4` IS the twist), plus narrow-internal toys
`(1,1,2)`, `(2,2,3)`, `(1,2,3)` where the twist is starkest, and the square base `(b,3,3)`. All agree.
For `(3,3,3,4)` the tail `A_{≥2}=A₂` is a **single** matrix, so the chain-length descent bottoms out in
one step (no deeper-product recursion) — this makes it the cleanest possible test of the det-inverse cover
seam in the pure `m<q` injective regime.

---

## 1. The cover-seam adjudication — Beta-divergence: **NO** + exact mechanism

**Object.** `I(a) = ∫_box det(Q_b Q_bᵀ)^{−a/2} d(Y,A)`, `Q_b = Y·A`, `Y:b×m`, `A:m×q`, `m<q`. The
det-inverse route: fix `A` (row rank `m`), change `Y ↦ Q_S = Y·A_S` (`A_S` = `m` columns `S`),
Jacobian `dY = |det A_S|^{−b} dQ_S`, on the dominant-minor cover `{S : |det A_S| maximal}`. Seam =
`{|det A_S| = |det A_{S'}|}`.

### The exact seam identity (verified, `seam_algebra.py`)

On chart-`S`, with `A_S` invertible, the CoV is **exact**:
> `Q Qᵀ = Q_S W Q_Sᵀ`, `W = A_S^{−1}(A Aᵀ)A_S^{−ᵀ}` — verified `sp.simplify == 0` for
> `(b,m,q) ∈ {(1,1,2),(1,2,3),(2,2,3),(2,3,4),(1,3,4)}`; for `b=m`,
> `det(Q Qᵀ) = det(Q_S)²·det(AAᵀ)/det(A_S)²`.

**Cauchy–Binet dominance (exact bracket, 0 violations / 20000 random `A` per shape).** On the dominant
chart `det(AAᵀ)/det(A_S)² = Σ_{S'}det(A_{S'})²/det(A_S)² ∈ [1, C(q,m)]`, and `W ≽ I` (Loewner, since
`AAᵀ ≽ A_SA_Sᵀ`) with **every** eigenvalue of `W` in `[1, det(AAᵀ)/det(A_S)²] ⊆ [1, C(q,m)]`. So `W`
is a **genuine unit** on the dominant chart (`min_eig W = 1.0`, `max_eig W ≤ C(q,m)` measured; e.g.
`(m,q)=(3,4)`: `worst_ratio 3.879 ≤ C(4,3)=4`).

### Why the seam carries no divergence (mine; PROVED, Codex-concurred)

1. **No boundary term exists.** Partitioning `∫_box = Σ_S ∫_{chart-S}` is multiplication by indicator
   functions `𝟙_{E_S}`, NOT integration by parts — there is no surface flux. The seam
   `{Δ_S² − Δ_{S'}² = 0}` is the zero set of a nonzero polynomial, hence Lebesgue-null; assigning it to
   either chart leaves `I(a)` unchanged.

2. **The transition Jacobian is `1` on the seam.** `Q_T = Q_S·(A_S^{−1}A_T)`,
   `|det(A_S^{−1}A_T)| = |Δ_T|/|Δ_S|`, which **equals `1` exactly on the seam** `|Δ_S|=|Δ_T|`. Rowwise
   Jacobian `1^b = 1` — **no Beta factor is created at the switch.**

3. **The integrand is `O(1)` on the seam.** `det(Q_b Q_bᵀ)` vanishes iff `rank Q_b < b`; for full-row-rank
   `A`, `rank(YA) = rank Y`, so the singularity locus is `{rank Y < b}` — geometric, chart-label-blind, and
   sitting at `σ_min = O(1)` (near-seam mean `σ_min ≈` overall mean; deep-corner fraction `< 0.4%`,
   `atomtrap_and_corner.py` Part B). A nonzero seam point is not singular. **A finite sum of finite terms
   over a null seam is finite.**

### The shrinking-image cancellation (verified exact)

The exact chart integral (Codex's clean form, matching mine) is
> `∫ |det A_S|^{r−b} ∫_{D_M} det(X(I+BBᵀ)Xᵀ)^{−a/2} dX dM dB`, `r=q−m`, `X=Y A_S`,
> `vol(D_M) = 2^{bm}|det A_S|^{b}`.

The image volume `|det A_S|^{b}` cancels the Jacobian `|det A_S|^{−b}` (net power `|det A_S|^{r}` at
`a=0`, **not** `|det A_S|^{r−b}` — cancellation confirmed). The residual `|det A_S|^{−a}`-type scaling in
witnesses (e.g. `(1,1,2)`: `|s|^{−1}∫_{−|s|}^{|s|}|x|^{−a}dx = C_a|s|^{−a}`) is the **genuine `Q`-scaling**,
NOT a seam pole. The full-space enlargement would instead give the atom's
`∫_ℝ(s²z²+w)^{−c}dz = K_c·s^{−1}·w^{½−c}` — the `s^{−1}` pole — but the **box limit**
`∫_{−1}^1(s²z²+w)^{−c}dz → 2·w^{−c}` is bounded, **no `s^{−1}`** (`atomtrap_and_corner.py` Part A, sympy
exact). This is the entire mechanism in one line: **box caps the collapsing direction; full space does not.**

### The genuine false-wall (a BOUND divergence, avoidable — and where it bites)

If a formaliser replaces the shrinking image `D_M` by a **fixed** box, the outer majorant contains
`∫|det A_S|^{r−b}dA_S`, which **diverges when `r < b`** (`r−b ≤ −1`; `det A_S` a smooth transverse
coordinate near `{rank=m−1}`): for `(2,3,4)` `r−b=−1` (false log `∫dt/|t|`), for `(2,2,3)` `r−b=−1` — and
this false divergence fires **inside** the dominant chart, even at `a=0`, NOT at the seam. It is a
divergence of the *bound*, not of `I(a)`. **This is the only real trap, it is a Lean-labor trap (keep the
shrinking image / the coupled `D_M`), not a math wall.** (Same phenomenon as `covdesign §CONCESSION` /
`pivchg §SEAM`'s "bare-invertibility over-charge".)

### Decorrelated Codex (my conclusion withheld) — CONCUR + two sharpenings adopted

Codex (`codex/coverseam-answer.md`), asked the open "does it wall?", independently returned: *"Beta/seam
divergence in `I(a)`: **NO**. Residual determinant divergence in a crude chart majorant: **YES**. True
finiteness: exactly `a<m−b+1`. Endpoint `a=a_c`: true logarithmic divergence. Dominant-minor cover needed
for the clean proof: **NO**."* Its Q1–Q4 derive the transition-Jacobian-`=1`-on-seam, the
volume-cancels-`|det M|^{−b}`, the `r−b<0` false-bound divergence, and the Gaussian/Bartlett threshold —
matching my exact algebra term-for-term. **Two sharpenings I adopt:**
- *(rank language)* "two maximal minors vanishing does **not** imply `rank A ≤ m−2`; **all** maximal minors
  vanish iff `rank A ≤ m−1`." (Corrects a loose phrasing; the deep stratum is `{rank A ≤ m−1}`.)
- *(tight majorant)* a **single `b×b` minor** `det(Q[:,T])²` is **lossy** (threshold only `a<1`); the sharp
  lower bound is the **`m`-column block** `Q Qᵀ ≽ Q_S Q_Sᵀ`, `|S|=m`, giving the two-Wishart threshold
  `a<m−b+1`. (I had used the `m`-column block; this pins why `b×b` alone is insufficient.)

---

## 2. The composed-slice accounting — does it sum to `7`? YES (the ledger)

`minAdm(3,3,3,4)=7`; binding branch `T=(1,0,0)`, per-boundary charges `[4,3,0]` (`acct.py`).

**Anchor the "sums to 7" to the banked `frontCharge` / `frontPeel_binding_cut`, NOT raw min-tail
(team-lead directive, RouteMSJDescNat #117).** The composition of the B5-desc per-step corank-Gram
thresholds into `minAdm` is the **front-peel**, an ADD-not-MIN:
`frontPeel_binding_cut : ∃ q ≤ tailMin M, minAdm M = frontCharge M q`,
`frontCharge M q = M₀·q + minAdm(M₁−q,…,M_L−q)`. For `(3,3,3,4)` the binding cut is `q∈{1,2}`:
> `q=1: frontCharge = 3·1 + minAdm(2,2,3) = 3 + 4 = 7`;  `q=2: 3·2 + minAdm(1,1,2) = 6 + 1 = 7`.

**Anti-trap (documented, RouteMSJDescNat):** the raw per-step corank-Gram threshold `min(tail)−b+1` is
**NOT** `minAdm` — for the `(b,3,4)` chain it is `3−b+1 = 2` (`b=2`) / `3` (`b=1`), a *single* step's
budget, not the total. The total `7` is the front-peel SUM (the `M₀·q` pivot/Morse charge ADDED to the
reduced-tail `minAdm`). A formaliser must compose via `frontCharge`, never equate the per-step
`min(tail)−b+1` with `minAdm`.

**Front-peel — pure-radial (layer-peel) view (banked `minAdmRec`), cross-check.**
`minAdm(3,3,3,4) = (M₀−t)(M₁−t) + minAdm(t,3,4)` at `t=1`: `4 + minAdm(1,3,4) = 4 + 3 = 7`;
`minAdm(1,3,4) = 3 + minAdm(0,4) = 3 + 0` — branch charges `[4, 3, 0]`, `Σ = 7`. Same `7` by a different
split (Γ-block `4` + deeper `3`, realised **geometrically** by the corner blow-up below) as `frontCharge`
(pivot `3` + reduced tail `4`, realised **arithmetically**). Both banked; bind at the same cuts
`t=1,2 ↔ q=2,1`.

**Corner accumulation (geometric, charges ADD not MIN).** The two active boundary charges `4` and `3` are
two radial blocks of dims `4` and `3`, radial Jacobian powers `(4−1)=3` and `(3−1)=2`, sharing the corner
`u₀=u₁=0`. Local model `G ≃ u₀²U₀ + u₁²U₁`, measure `|u₀|³|u₁|²`. Corner blow-up `u₁=u₀τ`:
`|u₀|^{3+2+1}=|u₀|^{6}` (the `+1` is `du₁=u₀dτ`), loss order `2`, threshold `(6+1)/2 = 7/2`. And
`6+1 = (4−1)+(3−1)+1+1 = 4+3 = Σcharges = 7`. So `threshold = ½·Σcharges = ½·minAdm = 7/2`.

- **MIN undershoot rejected:** independent divisors give `min((3+1)/2,(2+1)/2)=min(2,3/2)=3/2` — WRONG,
  a factor-2 undershoot; the shared corner is the fix (`atomtrap_and_corner.py` Part D: `E[integrand]`
  modest for `c'<3.5`, abscissa `≈7/2`, `1.6e0 @3.49 → 3.7e0 @3.6 → 1.7e2 @4.0`).
- Exact corner leg: `∫₀¹ u₀^{6−2c'} du₀ = 1/(7−2c')` finite iff `c' < 7/2` (`bartlett_singleminor.py`).

**Level discipline.** This certifies **FINITENESS** (`rlct ≥ ½·minAdm`, the R1-UPPER direction). The
matching `rlct ≤ ½·codim` is the separately-Cited Watanabe/Aoyagi interface; `codim = minAdm = 7` is
banked (`minAdmRec_eq_minAdm`).

---

## 3. Strict `<` preservation through the descent / log-borderline: PRESERVED

The corank-Gram exponent at the binding cut sits **exactly on** its threshold (zero slack): at `t=1`,
`p=M₀−t=2`, corank width `b=M₁−t=2`, `Q_b=Y·A₂` (`Y:2×3`, `A₂:3×4`), weight `det(Q_bQ_bᵀ)^{−p/2}` has
exponent `a=p=2`, and `min(3,4)−2+1 = 2` — so `a = threshold` (`bartlett_singleminor.py` Part G). The
det-Gram atom alone is log-borderline here.

Strictness is recovered and preserved by the strict `c' < ½·minAdm`:
- **Endpoint is the only true divergence.** `∫₀^ε r^{m−b−a}dr` diverges iff `a ≥ m−b+1`; at equality it is
  the logarithm `∫dr/r` (Codex Q4 + `seam_algebra.py` Part A). Strict `a < a_c` ⟹ strict convergence.
- **Linchpin, tight.** Front-first box bound `g(P) ≍ σ_q^{−α}`, `α = max{0, 2c'−m₀(q−1)}`, integrated
  against the product-rank tube codim `D`, converges iff `α < D`. The linchpin
  `minAdm(M) ≤ D + m₀(q−1)` is the `j=q−1` term of `minAdm_eq_frontPeel` (tautological, banked, 0
  violations); for `(3,3,3,4)` tight at `q=2,3` (`acct.py`: `7 ≤ 4+3`, `7 ≤ 1+6`). So `c' < ½·minAdm`
  ⟹ `α < D` **strictly**; `c' = ½·minAdm` ⟹ `α = D` (log-borderline, excluded).
- **The θ-tie log is harmless to strictness.** At the binding `q=2` stratum the two dominant codim-4
  components tie (`pivchg §PRODUCT-D`, exact Jacobian-codim, 3 ways), giving a `t⁴·log(1/t)` tube. Against
  `σ^{−α}` this still converges iff `α < D` strictly — the log only makes the borderline `α=D` diverge. It
  is the **θ-count (Level-B) multiplicity**, not a Level-A threat.

The descent-ℕ step (`min(tail)−b+1` composed = `minAdm`, B5-desc-ℕ, task #117) transports the strict
inequality intact: each per-stratum charge is `< D` strictly for `c' < ½·minAdm`.

---

## 4. Center-list completion verdict — LEVEL-SEPARATED

The incidence-center list `{A=0}, {Y=0}, {im A ⊆ ker Y}` and the extra **proportionality center
`(x₂,p₂)∥(x₃,p₃)`** (cornrev FOLLOW-UP-2's `5/2` carrier in `(2,3,3,4)`) are centers of an **explicit
blow-up resolution**. Their necessity is **level-dependent**:

- **For the B5-desc / majorant FINITENESS route (Level-A, my charge): the proportionality center is NOT
  needed.** The Cauchy–Binet `m`-column majorant (→ square base) and the Gaussian/Bartlett bound are
  **upper bounds, not resolutions** — they carry no blow-up centers. Finiteness up to `½·minAdm` holds
  with none of them.

- **For an explicit normal-crossing resolution (Level-B exact RLCT / θ-count): YES, `(3,3,3,4)` needs the
  proportionality center — identically to `(2,3,3,4)`.** Both have twist-gap `0.5`
  (`½minAdm(M)` vs `½minAdm(remove M₁)`: `(2,3,3,4): 2.5 vs 3.0`; `(3,3,3,4): 3.5 vs 4.0`), the same
  contracting tail `3<4`, and a corank-2 binding branch. The proportionality center **is** the θ-count
  tie: at the binding `q=2` corank cut the two dominant codim-4 components `(1,3,1)` and `(2,2,1)` tie
  (`pivchg §PRODUCT-D`, exact), the geometric shadow of `(x₂,p₂)∥(x₃,p₃)`. The vslice cert's §8 "named
  brick" (the resolved cores `U₀,U₁,U″` simultaneously bounded below) is the **same** condition in disguise
  — it fails precisely on the proportionality/alignment locus, which is where an explicit resolution must
  place the extra center.

**Actionable:** the center IS present in `(3,3,3,4)` and carries the binding `7/2` (twist lowers to the
GLOBAL value, not below — the `x⁴+y⁶` fear is absent; the tie is a *log multiplicity*, threshold-preserving,
per `pivchg §PRODUCT-D` + `cornrev FOLLOW-UP-2`). **Recommendation:** for Level-A, take the majorant route
and sidestep the center-completeness obligation entirely; add the proportionality center **only** if the
lane pursues an explicit resolution (Level-B or a resolution-based Level-A).

---

## 5. Close

- **Firmest result.** The det-inverse dominant-minor cover seam does **NOT** wall. No Beta/boundary
  divergence survives: the partition creates no surface term (indicator multiplication), the seam is
  Lebesgue-null with transition Jacobian **exactly `1`**, the integrand is `O(1)` there, and the
  `|det A_S|^{−b}` is exactly cancelled by the shrinking image (`vol = 2^{bm}|det A_S|^b`). Confirmed by my
  exact algebra (CoV identity + Cauchy–Binet dominance, 0 violations) and a fully decorrelated Codex.
  Accounting sums to `7 = minAdm` via the shared corner (`7/2`), strict `<` preserved (endpoint-only
  log-borderline). **Stronger:** Level-A finiteness needs neither the cover nor the seam — the `m`-column
  Cauchy–Binet lower bound `det(Q_bQ_bᵀ) ≥ det(Q_SQ_Sᵀ)` (task #112) → square-`(b,m,m)` base, matched
  threshold `m−b+1`; or the Gaussian/Bartlett two-Wishart moment, both cover-free.

- **Most likely to break it (a BOUND, not the integral).** A formaliser who extends the shrinking image
  `D_M` to a fixed box reintroduces `∫|det A_S|^{r−b}dA_S = ∞` for `r < b` (`(2,3,4)`, `(2,2,3)`: `r−b=−1`,
  even at `a=0`). This is a per-chart bound artifact inside the dominant chart, NOT a seam and NOT a wall —
  keep the shrinking image (the coupled `D_M`), or route through the `m`-column majorant / Gaussian bound
  and the issue never arises.

- **Next construction / consult that settles the open part.** The seam is settled. The remaining Level-A
  residual is the one `pivchg §PRODUCT-D` already named: for a **deeper product** tail (`A_{≥2}` a genuine
  product, unlike `(3,3,3,4)`'s single `A₂`), confirm the product-rank tube codim `D` has leading power
  `= codim` (the tie contributes only a log). For `(3,3,3,4)` this is banked (`D_prod=(8,4,1)`, 3 ways).
  The controller's decision is a **route choice**, not a wall: commission the B5-desc formaliser on the
  cover route knowing the seam is clean **provided the reduced-core step retains the shrinking image**, OR
  commission the strictly cheaper cover-free majorant (`m`-column Cauchy–Binet → square base) for Level-A
  finiteness and reserve the cover/centers for a Level-B resolution.
