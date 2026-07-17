# svd-chart-design — the Lean-friendly certificate for `corankSVD_chartFamily_lt_top`

**Seat:** pen-and-paper (design), aoyagi-full `genm-l2svd`. **Date:** 2026-07-17.
**NO Lean edits, NO build.** Exact algebra (sympy symbolic rank of the quadratic form + exact 1-D
radial reduction + numeric divergence witness) + decorrelated `local-codex-consult` (gpt-5.x xhigh,
my conclusion WITHHELD): `codex/svd-{prompt,answer}.md`. Reproducible: `svd_verify.py` (+ `svd_verify.out`).

**Task.** PIN the math for the §H deepest hole
`corankSVD_chartFamily_lt_top` (`RouteMSJProductCorankEngine.lean`, origin/genm-l2engine) so l2engine
formalises against a certificate — **EXTENDED** (l2engine hole-#2 sanity-check) to also cover the
**pivot-tail analogue** (`corankStratum_lt_top`'s pivot-Gram disposal): (obligation 1) the
`(P,B₁₂) → Q̃ₚ` CoV so `qbox_lintegral_lt_top` fires, and (obligation 2) the `A_r = (b−r)²`
transverse-Jacobian repair on deeper strata. Both designed as ONE resolution over the shared
`measurableEigendecomp` substrate + the `A_r` budget (§§8–10 below; read alongside l2engine's
`corankStratum_lt_top` design note @c90352f1f). The hole (verbatim signature):

    theorem corankSVD_chartFamily_lt_top {a b q : ℕ} (hab : 2 ≤ min a b)
        (S : Matrix (Fin b) (Fin q) ℝ) (c' : NNReal)
        (hthr : 2 * (c' : ℝ) < (a : ℝ) * (S.rank : ℝ))
        (box : Set (Fin a → Fin b → ℝ)) (hbox : volume box < ⊤) :
        ∫⁻ Γ in box, ENNReal.ofReal ((frobSq (Matrix.of Γ * S)) ^ (-(c' : ℝ))) < ⊤

---

## ★ VERDICT (firm, two decorrelated lines converge)

**EXPENSIVE-TRANSCRIPTION — and MUCH simpler than the §H framing.** With `S` FIXED and only `Γ`
integrated, this integrand is a **Morse (smooth-linear-center) singularity**, not a determinantal
blow-up. `frobSq(Γ·S)` is a positive-semidefinite quadratic form in the entries of `Γ` of rank
**exactly `a·rank(S)`**, whose zero locus `{Γ·S = 0}` is a *linear subspace* of codimension `a·rank(S)`.
It is resolved by **one orthogonal (spectral) change of variables + one radial engine call on the
`a·rank(S)`-dimensional active block** — the banked `corner_block_cube_lintegral_lt_top`. There is **no
recursion, no `d = c` exceptional-divisor determinantal blow-up, no transverse-Jacobian sign repair**
needed for THIS statement. Nothing in the source is ABSENT: the construction is elementary real
analysis + linear algebra on banked bricks.

**★ ONE SPEC CORRECTION TO ESCALATE (load-bearing, the one thing that must change).** The hypothesis
`hbox : volume box < ⊤` is **INSUFFICIENT — the statement as typed is FALSE.** Finiteness needs `box`
to be **bounded** (`Bornology.IsBounded box`, or `box ⊆ Metric.closedBall 0 R`), not merely of finite
volume. Explicit counterexample below (verified, exact + numeric; Codex reproduced it independently).
The real call site (`corankStratum_lt_top`: `{Γ | Γ + schurShift x ∈ genBox …}`, a translate of a
genuine product box) IS bounded, so the fix is safe and cost-free — but the isolated lemma must carry
the bounded hypothesis or it cannot be proved.

**★ LEVEL SEPARATION (the framing correction the engine must carry).** The recon-map / skeleton
docstring language for this hole — "the FULL multi-singular-value blow-up, `d = c` exceptional
coordinates, NOT a single radial (which resolves only Γ=0, not the rank-`1..c−1` cone; DEAD for c≥2),
transverse-Jacobian `>−1` sign repair uniform across shared-tail rank strata" — is **mis-imported from
the JOINT problem**, where `S = Q_b(I−P)` ALSO varies (is a deeper matrix product) and
`{(Γ,S) : Γ·S = 0}` is a determinantal variety stratified by rank drops. That difficulty is genuine and
lives ENTIRELY in the OTHER hole `corankStratum_lt_top` (S varies with `x, A'`). For the ISOLATED
`corankSVD_chartFamily_lt_top` (S fixed), the singular set is *linear*, there is no rank-`1..c−1` cone,
the Jacobian of the orthogonal CoV is *exactly ±1*, and `rank(S)` (not `b`) is the operative count
*automatically* — it is the rank of the quadratic form, no "sign repair" required. Both prodcorank-cert
and decstep round-3 §3's "single-radial DEAD" refuters are about the joint/varying-S incidence; they do
NOT apply here (Codex Q4 independently: "The objection is invalid for fixed S … plain Morse–Bott").

---

## 1. The math, pinned (the certificate l2engine formalises against)

Fix `a,b,q`, `min(a,b) ≥ 2`, a fixed real `S : Fin b → Fin q`, `c' ≥ 0`, and `r := rank S`.

### 1.1 The integrand is a rank-`a·r` PSD quadratic form in `Γ` (PROVEN, exact)

Let `G := S·Sᵀ` (the `b×b` Gram, PSD, `rank G = rank S = r`). Then, row-wise,

    frobSq(Γ·S) = ∑_{i=1}^{a} (Γ_i) · G · (Γ_i)ᵀ = tr(Γ · G · Γᵀ),   Γ_i = row i of Γ.

As a quadratic form in the `a·b` entries of `Γ`, its symmetric matrix is `I_a ⊗ G`, of rank
`a·rank(G) = a·r`. Its zero locus is the **linear subspace** `{Γ : Γ·S = 0} = (leftnull S)^{a}`, of
dimension `a·(b−r)`, i.e. codimension `a·r`.
(sympy-verified: `frobSq(ΓS) = ∑_i Γ_i(SSᵀ)Γ_iᵀ` and the quadratic-form matrix rank `= a·r`;
`svd_verify.py` Claim 1, `a=2,b=3,q=2,r=2 → rank 4 = a·r`.)

### 1.2 Diagonalise the FIXED Gram, separate active/free (the spectral CoV)

Spectral theorem for the single Hermitian `G`: `G = Q·D·Qᵀ`, `Q` orthogonal (`Matrix.IsHermitian`
`eigenvectorUnitary`), `D = diag(λ_1,…,λ_b)`, with `#{j : λ_j > 0} = r` (the positive eigenvalues are
the squared singular values `σ_j²`). The banked spectral identity gives, pointwise,

    frobSq(Γ·S) = ∑_{j} λ_j · ∑_{i} ((Γ·Q)_{ij})²        [frobSq_mul_eq_sum_eigenvalues, §E banked]

with `A₀ := Matrix.of Γ`, `P := S`, `λ = eigenvalues(S·Sᵀ)`, `Q = eigenvectorUnitary(S·Sᵀ)`.
In the coordinates `y := Γ·Q`, the `columns j with λ_j = 0` (there are `b−r` of them) **do not appear**;
the integrand depends only on the `a·r` **active** entries `{y_{ij} : λ_j > 0}`, on which it is the
**positive-definite** form `∑_{j:λ_j>0} λ_j ∑_i y_{ij}²`, with unit-sphere floor
`min_{j:λ_j>0} λ_j = σ_min² > 0`.

### 1.3 The radial engine on the active block (the finiteness)

On a bounded box, `∫ (positive-definite quadratic in `n = a·r` vars)^{−c'}` is finite iff `c' < n/2`.
This is exactly `corner_block_cube_lintegral_lt_top` (§C banked radial engine, `rlct = codim/2`
realized): `g(y_active) = ∑_{j:λ_j>0} λ_j ∑_i y_{ij}²` is degree-2 homogeneous (`hom`), measurable,
with sphere floor `a := σ_min² > 0` (`hlb`), for `c' < (a·r)/2` (`hc'`). The free `a·(b−r)` columns
integrate to a finite volume factor over the bounded box. **Threshold**: `c' < a·r/2 ⟺ 2c' < a·rank(S)`
— exactly `hthr`.

**Tightness (equality-at-binding-cell).** At `c' = a·r/2` the active radial integral is the log-boundary
`∫₀^ε ρ^{n−1−2c'}dρ = ∫₀^ε dρ/ρ = ∞`: the threshold is TIGHT, on any bounded full-dimensional box that
contains a transverse neighbourhood of the singular locus `{Γ·S=0}`. (`svd_verify.py` Claim 2; matches
`radial_ball_iff` critical-power dichotomy `−(m+1) < s`, here `m+1 = a·r`, `s = −2c'`.)

---

## 2. The Lean-friendly proof route (statement-shaped, banked pieces named)

Assume the corrected hypothesis `box ⊆ Metric.closedBall 0 R` (`R ≥ 0`), obtained from
`Bornology.IsBounded box` via `Metric.isBounded_iff_subset_closedBall`.

**Step 0 — dispatch `r = 0`.** If `rank S = 0` then `hthr : 2c' < 0`, impossible (`c' ≥ 0`, `a ≥ 2`) →
`exact absurd hthr (by positivity/omega)`. Hence `r ≥ 1`, and `a·r ≥ 2`, so `NeZero (a·r)` holds
(needed by `corner_block_cube_lintegral_lt_top`).

**Step 1 — monotone up to the ball.** `∫_box (frobSq ΓS)^{−c'} ≤ ∫_{closedBall 0 R} (frobSq ΓS)^{−c'}`
(`setLIntegral_mono_set` / `lintegral_mono_set`, integrand `≥ 0`; measurability of the integrand is
`fun_prop` + `frobSq` measurable).

**Step 2 — spectral rewrite of the integrand.** Rewrite `frobSq(Matrix.of Γ * S)` by
`frobSq_mul_eq_sum_eigenvalues (Matrix.of Γ) S` to `∑_j λ_j ∑_i ((Γ·Q)_{ij})²` under the integral
sign (`lintegral_congr` on the ball).

**Step 3 — the ball-preserving orthogonal CoV.** `Q` is orthogonal ⟹ `frobSq(Γ·Q) = frobSq(Γ)`, so the
ball `closedBall 0 R` (Frobenius norm) is **invariant** under `Γ ↦ Γ·Q`. Push the indicator inside and
apply `lintegral_comp_rightMulₚ a Q (hQdet : Q.det ≠ 0) g hg` (§B banked CoV): since `|det Q| = 1`
(`det_rightMulₚ`; `Q` orthogonal ⟹ `det Q = ±1`), the Jacobian factor is `1` and

    ∫_{ball} (∑_j λ_j ∑_i (Γ·Q)_{ij}²)^{−c'} dΓ = ∫_{ball} (∑_j λ_j ∑_i Γ_{ij}²)^{−c'} dΓ.

(The clean packaging: set `Gball(Γ) := indicator_{ball}(Γ) · (∑_j λ_j ∑_i Γ_{ij}²)^{−c'}`; use
`indicator_{ball}(Γ·Q) = indicator_{ball}(Γ)` from ball-invariance, then full-space
`lintegral_comp_rightMulₚ`.)

**Step 4 — split active × free, integrate.** `ball ⊆ cube [-R,R]^{a×b}` (monotone). The integrand
`(∑_{j:λ_j>0} λ_j ∑_i Γ_{ij}²)^{−c'}` depends only on the active columns. Tonelli factors the cube
`= [-R,R]^{active (a·r)} × [-R,R]^{free (a·(b−r))}`; the free factor is `(2R)^{a(b−r)} < ⊤`; the active
factor is `corner_block_cube_lintegral_lt_top` (rescaled from `[-1,1]` to `[-R,R]` by degree-2
homogeneity — see sub-lemma N3) with `g = ∑_{j:λ_j>0} λ_j ∑_i y_{ij}²`, `hlb = σ_min² > 0`,
`hc' : c' < (a·r)/2` from `hthr`.

---

## 3. Banked pieces CONSUMED (do NOT re-derive) — exact refs

| piece | file:line (origin/genm-integration) | role here |
|---|---|---|
| `frobSq_mul_eq_sum_eigenvalues` | `Validate/RouteMSJFrontSpectral.lean:94` | THE spectral rewrite `frobSq(Γ·S)=∑_j λ_j ∑_i((Γ·Q)_{ij})²` (Step 2) |
| `lintegral_comp_rightMulₚ` | `Validate/RouteMSJGammaAtom.lean:74` | orthogonal CoV `Γ↦Γ·Q`, reciprocal Jacobian `|det Q|^{−a}` (Step 3) |
| `det_rightMulₚ` | `…GammaAtom.lean:54` | `det(rightMulₚ a Q) = (det Q)^a` ⟹ `|·|=1` for orthogonal `Q` |
| `rightMulₚ` / `rightMulₚ_apply` | `…GammaAtom.lean:39/45` | the row-wise `Γ↦Γ·Q` map |
| `corner_block_cube_lintegral_lt_top` | `Validate/RouteMSJRadialPolar.lean:257` | radial engine: `∫_{[-1,1]ⁿ}(g z)^{−c'}<⊤`, `g` deg-2-homog + sphere floor `>0` + `c'<n/2` (Step 4, active block) |

**NOTE — `measurableEigendecomp` is NOT needed here.** The recon-map (§E) points at it, but that is the
*measurable family* frame, needed only when `S` varies (the OTHER hole). For a FIXED `S` the plain
`Matrix.IsHermitian.spectral_theorem` / `eigenvectorUnitary` + `frobSq_mul_eq_sum_eigenvalues` suffice;
no measurability of the frame is required.

## 4. Genuinely-new sub-lemmas to BUILD (each NAMED; small, elementary)

None is a monument; the deepest is a Fubini split + one radial call. Suggested names:

- **N1 `frobSq_rightMul_orthogonal`** : `Qᵀ*Q = 1 → frobSq (Matrix.of Γ * Q) = frobSq (Matrix.of Γ)`.
  (⟹ ball invariance for Step 3.) One line via `frobSq_eq_trace` + `Qᵀ Q = 1`. *(Check if already banked
  as a `frobSq`/`Matrix.frobenius_norm` orthogonal-invariance lemma — likely trivial or present.)*
- **N2 `eigenvectorUnitary_det_ne_zero`** : the orthogonal eigenframe `Q` has `Q.det ≠ 0` (indeed `±1`).
  From `Q` unitary/orthogonal (`Matrix.IsHermitian.eigenvectorUnitary`), `det Q` is a unit.
- **N3 `corner_block_rect_lintegral_lt_top`** (rescale of the cube radial to `[-R,R]ⁿ`): from
  `corner_block_cube_lintegral_lt_top` by degree-2 homogeneity `g(R•z)=R²·g z` and the linear rescale
  `z↦R·z` (Jacobian `Rⁿ`), `∫_{[-R,R]ⁿ}(g)^{−c'} = R^{n−2c'}·∫_{[-1,1]ⁿ}(g)^{−c'} < ⊤`.
  *(May be avoidable by keeping `R=1` if the call site's `genBox` uses radius 1; the socket uses
  `genBox … 1`, radius `1`, so the `R=1` cube may suffice directly — confirm at wire time.)*
- **N4 `diagWeightedSq_cube_lt_top`** (the reduction — the real new content, still small): for weights
  `λ : Fin b → ℝ` with `#{j : 0 < λ_j} = r` and `c' < a·r/2`,
  `∫_{[-R,R]^{a×b}} (∑_j λ_j ∑_i Γ_{ij}²)^{−c'} < ⊤`. Proof = Tonelli split active/free (Step 4) +
  `corner_block_(rect_)lintegral_lt_top` on active + finite free factor + the PD floor
  `∑_{j:λ_j>0} λ_j ∑_i y_{ij}² ≥ (min_{j:λ_j>0} λ_j)·‖y_active‖²`.
- **N5 `rank_eq_card_pos_eigenvalues`** : `rank S = #{j : 0 < eigenvalues(S·Sᵀ) j}` (so the active count
  is `a·rank(S)`, closing `hthr`). `rank S = rank(S·Sᵀ)` (banked `posSemidef_mul_transpose` / Gram-rank)
  `= #positive eigenvalues` of the PSD `S·Sᵀ`. *(The Gram-rank half is likely banked; the
  positive-eigenvalue count is `Matrix.IsHermitian.rank_eq_card_…` territory.)*

## 5. The SPEC FIX (the one escalation) — bounded box, with the counterexample

Change `hbox : volume box < ⊤` to **`hbox : Bornology.IsBounded box`** (or `box ⊆ Metric.closedBall 0 R`).

**Why `volume box < ⊤` is false (min(a,b)≥2, verified — `svd_verify.py` Claim 3, Codex reproduced):**
`a = b = 2, q = 1, S = (1,0)ᵀ` (so `r = rank S = 1`, `a·r = 2`, threshold `c' < 1`). Write
`Γ = ((x₁,z₁),(x₂,z₂))`, `frobSq(Γ·S) = x₁²+x₂² = |x|²` (`x` active, `z` free). Take
`c' = 0.9 < 1` (within threshold) and the finite-volume set

    E = ⋃_{m≥1} { |x| < 1/m , z ∈ (m, m+1)×(0,1) }   (or the polar wedge `0<z<|x|^{−β}`, β<2),

`vol(E) = ∑ π/m² < ∞`, yet `I(E) = ∑ 2π∫₀^{1/m} dρ = 2π ∑ 1/m = ∞`. So a **finite-volume** domain
**diverges** below threshold. (Numeric monotone divergence 20.8 → 145 → 1300 → ∞ as the cutoff → 0.)
A genuine full-dimensional *product box* of finite volume is automatically bounded (Codex nuance), so if
the socket only ever feeds product boxes the current form is "morally" fine — but the ARBITRARY
`Set … + volume < ⊤` signature admits the counterexample, so the lemma must state boundedness.

## 6. Kill-conditions / witness battery (W1–W4) — all PASS, and WHY they don't bite here

- **W1 (joint-center survival).** Guards against a *single-factor* claim to principalize the min-corank≥2
  **product** ideal `Γ·S` when **both** `Γ` and `S` drop rank (the alignment coord `b` survives). Here
  `S` is FIXED, so there is no joint incidence and no alignment coordinate — W1 is about the OTHER hole
  (`corankStratum_lt_top`). This certificate does NOT claim to principalize a varying product; it resolves
  a fixed-`S` linear-center singularity. **No W1 violation** (nothing single-factor is claimed about a
  varying product).
- **W2 (codim undershoot `C_m < m²`).** The `⌊m²/4⌋` gap is the non-submersiveness of `(P,Z)↦P·Z` with
  BOTH varying. With `S` fixed, `Γ↦Γ·S` is a *constant-rank linear* map; its image dimension is exactly
  `a·rank(S)` (submersive onto its image), no undershoot. The certificate charges exactly `a·rank(S)`
  (the true active count), never a naive `a·b`. **No W2 conflation.**
- **W3 (tightness, equality-at-binding-cell).** The threshold `c' < a·r/2` is exact and TIGHT: at
  equality the active radial integral is log-divergent (§1.3). Equality-at-binding certificate:
  `c' = a·r/2 ⟹ ∫ = ∞` on any bounded box meeting the center transversally. **Carried.**
- **W4 (block dispatch on `d = min(a,b)`).** This hole is the tool the `d ≥ 2` cover routes its inner
  pure-corank residual to, keyed on `min(a,b) ≥ 2` (`hab`). The certificate is `d`-agnostic in
  difficulty (Morse for any `d`); the `d≥2` transcribe-vs-native split is a property of the OUTER cover
  (`corankStratum_lt_top`), not of this fixed-`S` inner finiteness. **Consistent with W4's per-cut Prop.**

## 7. What this certificate does NOT settle (honest scope — hand-off to l2engine)

- **The isolated hole is a FINITENESS statement for fixed `S`.** The OUTER descent
  `corankStratum_lt_top` integrates over `A'` (so `S = Q_b·(I−P_{Q̃ₚ})` VARIES with `x, A'`). Feeding
  this fixed-`S` finiteness under an outer `∫ dA'` gives finiteness of the inner integral *a.e. in A'*,
  which is **not** the finiteness of the iterated integral — the outer integrability against the
  `A' → tail-rank-drop` / `x → pivot-rank-drop` degeneration (where `rank(S)` drops and the inner
  constant blows up) is the genuine joint content, and it is `corankStratum_lt_top`'s job. **Do not
  expect `corankSVD_chartFamily_lt_top` (fixed S) to carry a "uniform-across-strata sign repair"** — a
  fixed-`S` statement structurally cannot. If the engine's `corankStratum_lt_top` proof needs a
  *quantitative* inner bound (inner integral `≤ C(S)` with `C(S)` outer-integrable), that is a
  DIFFERENT, stronger lemma than the stated `corankSVD_chartFamily_lt_top`; flag it before wiring.
- **The determinantal / non-submersive / `C_m` wall (prodcorank-cert)** is real and lives in the OUTER
  integral. This certificate does not, and cannot, discharge it; it discharges exactly the inner
  fixed-`S` pure-corank finiteness the skeleton typed.

---

# EXTENSION — the pivot-tail analogue (hole #2's disposal), one resolution over the shared eigenframe

l2engine reduced `corankStratum_lt_top`'s inner-Γ part to my corank-tail SVD family (§§1–7) via
`gammaAtom_aniso_shifted_eq` (R := Q̃ₚ, S := Γ·Q_b, w := frobSq(P·Q̃ₚ)); that step also spits out the
**PIVOT Gram** `det(Q̃ₚ·Q̃ₚᵀ)^{−a/2}` (Q̃ₚ = `pivotTail x Q` = `Q_p + P⁻¹·B₁₂·Q_b`, `t×q̃`), the atom-trap-safe
weight (NEVER the corank Gram). Two pivot-side obligations were routed here.

## 8. Obligation 1 — the `(P,B₁₂) → free-Wishart` CoV so `qbox_lintegral_lt_top` fires (top stratum)

**Verdict: EXPENSIVE-TRANSCRIPTION.** `qbox_lintegral_lt_top` disposes a FREE `t×m` Gram over a ball
(`∫_{W∈ball^t} det(W·Wᵀ)^{−a/2} < ⊤`, gate `t ≤ m`, `a < m − t + 1`). `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b` is not
free; the CoV that frees it (all steps verified exactly, `pivot_verify.py`):

1. **B₁₂-shear** (P fixed): `B₁₂ ↦ B' := P⁻¹·B₁₂`, a linear CoV on `t×b` = `I_b ⊗ P⁻¹`, Jacobian
   `|det P|^{−b}` (so `dB₁₂ = |det P|^{b} dB'`). Kills `P⁻¹`: `Q̃ₚ = Q_p + B'·Q_b`. The factor `|det P|^{b}`
   is in the NUMERATOR and BOUNDED on the box (no singularity from it; on the dominant-minor chart
   `|det P|` is bounded above and below). CoV tool: `lintegral_comp_rightMulₚ`-style per-column left-mult
   (or a direct `Measure.map_linearMap_addHaar` with `det = (det P⁻¹)^b`).
2. **Right-orthogonal compress of Q_b** (top stratum `rank Q_b = b`): `det(Q̃ₚ·Q̃ₚᵀ)` is invariant under
   `Q̃ₚ ↦ Q̃ₚ·V` for any orthogonal `V` (`(Q̃ₚV)(Q̃ₚV)ᵀ = Q̃ₚQ̃ₚᵀ`). Pick `V` = the right-singular frame of
   `Q_b` (SVD / `measurableEigendecomp` of `Q_bᵀQ_b`) so `Q_b·V = [Ψ | 0]`, `Ψ` `b×b` invertible. Then
   `Q̃ₚ·V = [R₁ + B'·Ψ | R₂]`, `R₁ = (Q_p V)_{cols≤b}`, `R₂ = (Q_p V)_{cols>b}`.
3. **Affine W-shift**: `B' ↦ W := R₁ + B'·Ψ` (right-mult by invertible `Ψ`), Jacobian `|det Ψ|^{t}` (so
   `dB' = |det Ψ|^{−t} dW`). `W` is a FREE `t×b` matrix. And
   **`det(Q̃ₚ·Q̃ₚᵀ) = det(W·Wᵀ + C₀)`, `C₀ := R₂·R₂ᵀ ⪰ 0`.**
4. **PSD-shift dominance + qbox**: `det(W·Wᵀ + C₀) ≥ det(W·Wᵀ)` (Löwner/Minkowski monotonicity of `det`
   on the PSD cone) ⟹ `det(Q̃ₚ·Q̃ₚᵀ)^{−a/2} ≤ det(W·Wᵀ)^{−a/2}` — **the PSD shift only helps.** Bound the
   `W`-box by a ball (monotone, nonneg), apply `qbox_lintegral_lt_top` (`m = b`), gate `a < b − t + 1`.

The **structural parallel to the corank-tail** is exact: free-ify via a linear/affine CoV + a shared
right-orthogonal eigenframe, dominate by a banked FREE-matrix lemma (`corner_block` there, `qbox` here),
the coupling/shift only helping (`w>0 ⟹ (w+f)^{−d} ≤ f^{−d}` there; `C₀ ⪰ 0 ⟹ det(·+C₀) ≥ det(·)` here).

**New named sub-lemmas (obligation 1):**
- **P1 `det_addPSD_ge`** : `C₀.PosSemidef → (W·Wᵀ).det ≤ (W·Wᵀ + C₀).det`. (Löwner monotonicity of `det`;
  likely a short Mathlib composite via `Matrix.PosSemidef.det_le_…` / eigenvalue monotonicity.)
- **P2 `pivotGram_freeWishart_cov`** : the (1)+(2)+(3) chain — `∫_{(P,B₁₂)∈box} det(Q̃ₚQ̃ₚᵀ)^{−a/2}` `≤`
  `(bounded |det P|^{b} factor)·|det Ψ|^{−t}·∫_{W∈ball} det(WWᵀ)^{−a/2}`. The Jacobians are exactly
  `|det P|^{b}` and `|det Ψ|^{−t}` (both verified).
- **P3** consume `qbox_lintegral_lt_top` (§D banked) at `m = b`, gate `a < b − t + 1`.

**The gate `a < b − t + 1` is TOP-STRATUM only** — exactly the qbox one-shot regime (`2·(a/2) < q_eff − t + 1`
with `q_eff = b` at full tail rank). Below it → the reduced-chain recursion (`hIH`) / obligation 2.

## 9. Obligation 2 — the `A_r = (b−r)²` transverse-Jacobian repair on deeper strata (the ONE escalation)

Step 8(3)'s Jacobian `|det Ψ|^{−t}` is the load-bearing coupling: **`|det Ψ| = ∏_{j: μ_j>0} √μ_j`**, the
product of the nonzero singular values of `Q_b` (`μ_j` = eigenvalues of the SHARED Gram `Q_b·Q_bᵀ`). As the
OUTER parameter `A'` drives `Q_b(A')` toward rank `r < b`, `|det Ψ|^{−t} → ∞` (verified: 2nd singular value
`10⁻¹→10⁻²→10⁻³` gives `|det Ψ|^{−t} = 10→10³→10⁵`, `pivot_verify.py`). So the OUTER `∫_{A'}` of
`|det Ψ(A')|^{−t}·(qbox constant)` against the `A' → rank-drop` degeneration is where the difficulty
concentrates — the **pivot-side `GAP-IN-RELATIVE-JACOBIAN`** (decstep round-4 KILL-guard 4 / round-5).

**This is the SAME shared-tail rank degeneration as the corank-tail**, over the SAME eigenframe: the corank
count `rank(S) = rank(Q_b·Π)` (my §1 threshold `2c' < a·rank(S)`) and the pivot Jacobian `|det Ψ|^{−t}` are
BOTH functions of the eigenvalues `μ_j(A')` of `Q_b(A')·Q_b(A')ᵀ`, and both degenerate on
`{A' : rank Q_b(A') = r} = {μ_{r+1} = … = μ_b = 0}`. The repair is the transverse Jacobian of that stratum,
charged `A_r = (b−r)²` (= `peelCharge(M, deepened cut)`; round-5 care-point: `(corank at the deepened cut)²`,
**NOT** the mislabeled `(b−r)²` unless `r` is the rank-DROP — carry the consistent invariant
`charge = peelCharge(M,u')` as a kill-condition).

**The FREE-`Q_b` deeper-strata integral is STANDARD (submersive) — the baseline (decorrelated Codex, exact).**
If `Q_b` were a FREE `b×q` matrix, `∫_{A'} |det Ψ(A')|^{−t}` over the rank-drop is finite iff
**`t < q − b + 1`**: the rank-r stratum has codim `(b−r)(q−r)`, the transverse product of the `(b−r)`
vanishing singular values has radial (vanishing) order `(b−r)`, so the per-stratum threshold is
`t < (b−r)(q−r)/(b−r) = q − r`, and `min_{r<b}(q−r) = q−b+1` (thin-QR of `Q_bᵀ`,
`dQ_b = C∏ r_{ii}^{q−i}dR\,dU`, `F(Q_b) = ∏ r_{ii}`). **Care-point (load-bearing):** the operative exponent
is `codim / (vanishing order)`, NOT raw codim — so satred's `A_r = (b−r)²` (the DLN peelCharge at the
deepened cut) must be reconciled with this `codim/(order)` reading; the free-matrix codim `(b−r)(q−r)` and
the peelCharge `(b−r)²` coincide only at `q = b`, so the DLN-specific deepened-cut widths are what carry
the reconciliation (satred owns this; bake `charge = peelCharge(M,u')` as the kill-condition, round-5).

**Classification (honest, per the binding rule):**
- **The per-stratum REDUCTION, GIVEN the transverse Jacobian `= A_r`**, is TRANSCRIPTION: on the rank-r
  stratum the compression gives `W` free `t×r` (not `t×b`; the `(b−r)t` extra `B'`-directions integrate to a
  bounded volume factor), Gram `= W·Wᵀ + C₀ ≥ W·Wᵀ`, qbox at `m = r` gate `a < r − t + 1`, and the `A_r`
  transverse Jacobian supplies the codim that raises the (then-failing, `r − t + 1 ≤ 0` for small `r`)
  exponent above `−1`. The arithmetic `min_r[A_r + minAdm(reducedᵣ)] = minAdm` is AIRTIGHT and banked
  (satred; verified `(4,4,4,4)@t=2 A_r=[0,1,4]→min 11`, my n=3..15) — l2witness checks the ratios.
- **Establishing the transverse-Jacobian `= A_r` for the NON-SUBMERSIVE shared deeper product `Q_b(A')`**
  (that blowing up `{rank Q_b(A')=r}` through the product parametrization principalizes the joint incidence
  with all exponents `> −1`, no smaller-ratio divisor) is **the GAP** — genuinely ABSENT from Aoyagi's
  worked EXACT results. Aoyagi's Case-2 blow-up DOES carry the codim exponent `(M(S)−J)(M^{(S+1)}−J)` (the
  transverse-Jac-as-codim structure — so the STRUCTURE transcribes), but his general Theorem 5 gives only
  UPPER bounds and EXACT values only for `N=1`/small `H`; the general exact `rlct ≥ c*` (the finiteness
  direction) is his stated future work (prodcorank-cert §6). This is the same wall prodcorank adjudicated
  and decstep round-5 flagged (`RECONSIDER`, "deeper than standard-technique — the non-submersive
  product-corank resolution"). **★ This is the one thing to ESCALATE.** The circularity guard binds: one
  cannot use "rlct = c* (Aoyagi) ⟹ no smaller-ratio divisor" inside the native proof.

  **Concrete mechanism (decorrelated Codex, decisive — how the non-submersive pullback LOWERS the
  threshold).** Take the simplest product `Q_b = L·R` (`L` free `b×b`, `R` free `b×q`). Then
  `|det Ψ(Q_b)| = √det(Q_b Q_bᵀ) = |det L|·√det(R Rᵀ) = |det L|·|det Ψ(R)|`. So the pullback integrability
  requires SIMULTANEOUSLY `t < 1` (from the extra divisor `{det L = 0}`, codim 1, along which `|det Ψ|`
  vanishes linearly) AND `t < q−b+1` (from `R`) — threshold **`t < 1`**, STRICTLY worse than the
  free-`Q_b` baseline `t < q−b+1` when `q > b`. The preimage of the output corank-1 locus contains the
  factor divisor `{det L=0}` that the free-matrix computation never sees. This is exactly the
  `GAP-IN-RELATIVE-JACOBIAN`: the deeper-product transverse Jacobian is a genuine unresolved proof
  obligation, NOT an automatic determinantal substitution; the cokernel count alone (`⌊k²/4⌋`) does not
  determine the pullback discrepancy — one needs the codim AND the exact vanishing order along EVERY
  factor-rank incidence component. (Codex: "research-grade calculation … whether literally open depends on
  the precise product dimensions and rank patterns.") **⟹ Lane-2's native bet lives or dies here; this
  needs an explicit operator decision (build the multi-tide resolution vs consolidate at the cite).**

**A measure-level subtlety l2engine must resolve (surfaced here).** `tailRankStratum M t κ r` is the
EXACT-rank set `{A' : rank Q_b(A') = r}`. For `r < ` the generic rank this is a determinantal subvariety of
`A'`-space, **Lebesgue-null**, so `∫_{tailRankStratum r}(…) = 0` trivially (integral over a null set) — the
finite-cover glue is then vacuously satisfied off the top stratum, and the whole difficulty sits in the
**TOP stratum's** OUTER integrability against `A' → (lower-rank boundary)` (the boundary is null but the
integrand `|det Ψ(A')|^{−t}` blows up approaching it). So the `A_r` repair is not "handle a separate
positive-measure deep stratum"; it is "prove the top-stratum outer integral is finite by resolving
(blowing up) the null rank-drop boundary" — and that resolution's transverse-Jac `= A_r` validity for the
non-submersive product is exactly the gap above. **Flag:** the exact-rank-strata cover, as literally typed,
routes all content to `r = ` generic; confirm the intended decomposition is a BLOW-UP of the rank-drop
boundary (positive-codim exceptional divisors with the `A_r` weights), not a partition into null exact-rank
pieces — otherwise the cover proves finiteness only where it was never in doubt.

## 10. Unified classification (both tails, per obligation) + dead-route guard

| obligation | object | verdict | consumes / new |
|---|---|---|---|
| corank-tail SVD family (§§1–4, hole #1) | `∫_Γ frobSq(Γ·S)^{−c'}`, S fixed | **TRANSCRIPTION** (Morse) | `frobSq_mul_eq_sum_eigenvalues`, `lintegral_comp_rightMulₚ`, `corner_block_cube_lintegral_lt_top`; new N1–N5 |
| pivot obligation 1 (§8) | `∫_{(P,B₁₂)} det(Q̃ₚQ̃ₚᵀ)^{−a/2}`, top stratum | **TRANSCRIPTION** | shared right-eigenframe of `Q_b`, `qbox_lintegral_lt_top`; new P1–P3 |
| pivot/corank obligation 2 (§9) | `A_r` transverse-Jac repair, deeper strata, shared product | **STRUCTURE transcribes; EXACT VALIDITY is the GAP → ESCALATE** | `measurableEigendecomp` + `A_r` budget (satred) + l2witness ratios; the non-submersive principalization is the wall |

**The 5 DEAD routes (recon-map §DEAD) — all honored:** (1) atom trap — §8 carries the PIVOT Gram
`det(Q̃ₚQ̃ₚᵀ)`, NEVER `det(Q_bQ_bᵀ)`; (2) single-factor / naive `m²` at min≥2 — obligation 2 is exactly why
a single-factor peel is unsound (the joint incidence survives, W1); (3) single radial for c≥2 — §1 uses the
spectral CoV + active-block radial, not a whole-space radial (and the corank hole is Morse, so even the
"determinantal" objection is a non-issue for FIXED S, §Q4); (4) pointwise inner-peel — the atoms
(`gammaAtom`, `qbox`) are consumed at the MEASURE level after the CoVs, and their PosDef/gate hyps hold on
the top stratum a.e. (obligation 2 supplies the rest); (5) `cornerComparator` flat / radialize-and-drop-J —
`|det J|` (= `|det P|^{b}`, `|det Ψ|^{−t}`, and the `A_r` transverse weight) is CARRIED throughout, never
dropped.

**Equality-at-binding-cell witnesses (both tails).** Corank: `c' = a·r/2 ⟹ ∫ = ∞` (§1.3, log-boundary,
tight). Pivot: `qbox` gate `a = b − t + 1 ⟹` the free-Wishart integral is the log-boundary (marginal);
per-stratum `A_r + minAdm(reducedᵣ) = minAdm(M)` with EQUALITY at the binding `r*` (satred, W3/W4;
`(4,4,4,4)@t=2`: `A_{r*} + reduced = 11 = minAdm`, no slack). The transcription lands the threshold EXACTLY
(no slack), which is why the `A_r` repair (not a looser bound) is forced.

---

## Close

- **Firmest result.** `corankSVD_chartFamily_lt_top` (S fixed) is **Morse (smooth-linear-center),
  EXPENSIVE-TRANSCRIPTION, not an OPEN-PROBLEM**: `frobSq(Γ·S)` is a rank-`a·rank(S)` PSD quadratic form;
  spectral CoV (unit Jacobian) + one `corner_block_cube_lintegral_lt_top` on the `a·rank(S)` active block
  closes it below the tight threshold `2c' < a·rank(S)`. Banked substrate suffices;
  `measurableEigendecomp` is NOT needed (fixed S). Two decorrelated lines converge (my exact algebra +
  Codex xhigh, independent, same counterexample + same Q4 level-separation).
  spectral CoV (unit Jacobian) + one `corner_block_cube_lintegral_lt_top` on the `a·rank(S)` active block
  closes it below the tight threshold `2c' < a·rank(S)`. **The pivot-tail obligation 1** (§8, the
  `(P,B₁₂)→free-Wishart` CoV → `qbox`) is likewise **TRANSCRIPTION** (linear/affine CoV + PSD-shift
  determinant dominance + `qbox`, all verified). Both tails free-ify over the **shared eigenframe of
  `Q_b·Q_bᵀ`** and dominate by a banked free-matrix lemma. Decorrelated across two Codex consults + exact
  algebra.
- **The ONE escalation (§9).** The pivot/corank **obligation 2** — the `A_r = (b−r)²` transverse-Jacobian
  repair on the deeper (rank-drop) strata for the **non-submersive shared deeper product `Q_b(A')`** — has
  transcribable STRUCTURE (Aoyagi Case-2 codim exponent + satred's airtight `A_r` arithmetic) but its EXACT
  VALIDITY (a genuine SNC resolution, all exponents `> −1`, no smaller-ratio divisor) is **absent from
  Aoyagi's exact results** = the `GAP-IN-RELATIVE-JACOBIAN` = the prodcorank wall. This is where native
  Lane-2 either becomes a genuine multi-tide theorem or consolidates at the cite; not clean transcription.
- **Most likely to break it.** (i) The `hbox : volume box < ⊤` signature — the corank hole is FALSE at it
  (counterexample §5); MUST become `IsBounded box`. (ii) If `corankStratum_lt_top` needs a *quantitative*
  inner bound (not just finiteness), the stated corank finiteness lemma is the wrong tool (§7). (iii) The
  exact-rank-strata cover routes all content to the generic stratum (lower strata are null, §9 subtlety);
  confirm the intended decomposition is a rank-boundary BLOW-UP, not a null-partition.
- **Next.** (a) l2engine: adopt `hbox : Bornology.IsBounded box` (or `⊆ closedBall`); the socket's
  `genBox … 1` translate satisfies it. (b) Confirm the finiteness-vs-quantitative question (§7) and the
  cover-vs-blow-up question (§9). (c) Build sub-lemmas N1–N5 (corank) + P1–P3 (pivot); everything else is
  consume-not-derive. (d) Escalate obligation 2 (§9) to the operator: it is the wall, and Lane-2's native
  bet rests on it — satred owns the `A_r` arithmetic, l2witness the ratios, but the non-submersive
  transverse-Jac validity needs an explicit decision (build-as-monument vs cite).

**Files (absolute):**
- this design: `…/threads/genm-l2svd/svd-chart-design.md`
- verify: `…/threads/genm-l2svd/svd_verify.py` (corank tail) + `…/pivot_verify.py` (pivot tail), + `.out`s
- decorrelated consults: `…/threads/genm-l2svd/codex/svd-{prompt,answer}.md` (corank),
  `…/codex/pivot-{prompt,answer}.md` (pivot)
- socket/hole: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJProductCorankEngine.lean` (origin/genm-l2engine
  @c90352f1f) — `corankSVD_chartFamily_lt_top:217`, `corankStratum_lt_top:262` (+ its measure-reduction
  design note, the 4 caveats)
- banked refs: §3 table + §8 (`qbox_lintegral_lt_top` `RouteMSJQBoxCore:113`, `gammaAtom_aniso_shifted_eq`
  `RouteMSJGammaAtom:142`), all origin/genm-integration
- prior certs: prodcorank-cert (the WALL adjudication), decstep-cert rounds 4–6 (GAP-IN-RELATIVE-JACOBIAN),
  recon-map §H/§DEAD, witness-battery W1–W4
