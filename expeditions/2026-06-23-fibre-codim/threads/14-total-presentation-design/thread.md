# thread 14 — G2-3 total-presentation design recon (G2-3a, explore/scout — scope the wall)

**Type:** explore (scout) · design recon. G2-2 (the localized BASE presentation `A_loc/Iad ≅ₐ[k] Sd`)
is done. G2-3 is the genuine wall: the **total**-space side + flatness, en route to
`codim_{Σ̄^r}(fibre) = δ` ⟹ the final `codimRepCanonical(fibre d B) = cCodim d r + r(d_0+d_N−r)`. Scope
it before any formaliser tide. **No production Lean** (throwaway probes fine); output = the G2-3
rung-ladder + reachability verdict. Decorrelated Codex required.

## The target + where G2-2 leaves us
Final Core target (= `BundleShiftInterface.cited_bundle_shift`): for `[Field K][IsAlgClosed K][CharZero K]`,
`B.rank = r`, `r ≤ d k'`, `0 < N`:
`codimRepCanonical (fibre d B) = codimRepCanonical (productRankLocusLE d r) + (r*(d_0+d_N−r):ℕ∞)`
(= `cCodim d r + δ`; Brick A gives `codimRepCanonical Σ̄^r = cCodim`). Via the catenary this is
`codim_{Σ̄^r}(fibre) = δ`. G1 (reduce-to-`E`) lets us work at the normal form `E = diag(I_r,0)`.

**Landed foundation (reuse, don't rebuild):** G2-2's base presentation `A_loc/Iad ≅ Sd` (regular dim δ,
`height Iad = C`); the reusable engines — `MvPolynomialKerAeval` (`ker_aeval = graphIdeal`),
`GraphIdealHeight` (`height_graphIdeal_eq` + localized transport), `DeterminantalBaseElimination`
(reindex + `blockAlgEquiv` + detΔ bridge), `DeterminantalChartRing` (bordered Schur minor); the
going-down height-additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (LANDED in
Mathlib, used in `FlatQuasiFiniteHeight`/`PolynomialDimension`); the affine-domain equidim + the
catenary bridge.

## Questions to answer (the blueprint)
1. **The total-space presentation on the chart.** `B_total` = the coordinate ring of `Σ̄^r ⊆ Rep_d` (vs
   G2-2's base `Mat^{rk=r}`). On the pivot chart, does the reindex/graph-ideal/Schur machinery extend
   from `Mat` to the full `Rep_d`? What are the "free" vs "forced" coordinates of the TOTAL ring on the
   chart, and what is the fibre-over-`E` coordinate ring `F_E` concretely (the "zero-product-type"
   locus)? Is `B_loc ≅ A_loc ⊗_k F_E` (the bundle trivialization) the right object, or is there a
   cheaper route reusing G2-2?
2. **Flatness / going-down.** The chain needs `HasGoingDown` for the comorphism `A_base → B_total` ON
   THE CHART (mult is NOT globally flat — fibre dim jumps). Does `B_loc ≅ A_loc ⊗ F_E` (free over
   `A_loc`) ⟹ flat ⟹ going-down, with the landed `height_eq_height_add_…`? Pin the exact lemma chain to
   `codim_{Σ̄^r}(fibre) = δ`. (Reserve: Codex's earlier "total-coordinate" route — fibre = `C+δ` explicit
   coordinate equations on the chart ⟹ height directly, no going-down — evaluate if cleaner now.)
3. **Reducibility (the G2-5 question).** `codimRepCanonical = iInf` over minimal primes; Σ̄^r reducible
   when θ>1. How do the fibre's components match Σ̄^r's orbit-components (Brick A
   `minimalPrimes_sigmaIdeal_eq`) with the uniform `+δ`? Pin the correspondence; decide whether it folds
   into G2-3 or stays a separate rung.
4. **Rung-ladder + risk.** Decompose G2-3 (+G2-4/G2-5) into tide-sized rungs; per rung the machinery
   (reuse-vs-new), size, risk; name the single hardest sub-wall and its reachability verdict. Is the
   total-presentation a clean mirror of G2-2's base presentation, or materially harder (Rep_d ≫ Mat)?

## Method / rules
Exact algebra; use the `(2,2,2),r=1` anchor (`dim Σ̄^1 = 7 = 3 + 4`; fibre codim `4 = C(1)+δ(3)`). **Fire a
decorrelated `local-codex-consult`** (authenticated, xhigh) on Q1+Q2 (the total presentation + flatness),
saved under `threads/14-total-presentation-design/codex/`. Read: `Core/DeterminantalBasePresentation`
(G2-2), `Core/DeterminantalBaseElimination`, `Core/MultComorphism`/`FibreCodim` (the fibre + comorphism),
`Core/SigmaCodim` (Brick A + minimal primes), `Core/FlatTrivialProductProbe`/`ChartFlatnessProbe` (the
flatness API + the prior NO-GO write-ups). **NO production Lean / no commits to library files.**

## Output (report to controller)
The confirmed G2-3 rung-ladder, per-rung machinery + size + risk, the single hardest sub-wall + its
reachability verdict, the decorrelated-Codex read, and a clear recommendation: the route for the total
presentation + flatness (or, if the total presentation is out of reach at v4.29, the precise wall + the
fallback). Honest scout — if G2-3 is genuinely much harder than G2-2 (or a wall), say so plainly.
In-repo notes only; never `~/.claude/**/memory/`; don't touch other worktrees.

---

# DISPATCH 1 (scout) — G2-3 total-presentation design recon

## Method
Read the landed engines (`DeterminantalBasePresentation` G2-2, `DeterminantalBaseElimination`,
`GraphIdealHeight`, `DeterminantalChartRing`, `MultComorphism`, `FibreCodim`, `SigmaCodim`,
`FlatTrivialProductProbe`, `ChartFlatnessProbe`, `FlatQuasiFiniteHeight`, `Setup`, `RlctPayoffGeneral`).
Worked the `(2,2,2) r=1` anchor + `(3,3,3)`, `(2,3,2)` in sympy. Fired a decorrelated Codex consult
(xhigh) on Q1+Q2 (`codex/q1q2-answer.md`).

## Key computations (sympy, recorded)

**C1 — the total rank ideal FACTORS (reducibility).** For `(2,2,2) r=1`, `det(A₂A₁) = detA₁·detA₂`
(REDUCIBLE), vs the base target `det B` (IRREDUCIBLE). So the rank ideal of `Σ̄^r ⊆ Rep_d` factors
into orbit-component pieces; the product entries are degree-N polys, NOT coordinate variables. =>
**G2-2's B22-elimination/graph-ideal trick does NOT port to the total side.**

**C2 — fibre-over-E structure (anchor).** `F_E = {A₂A₁ = E}`, `E = diag(I₁,0)`. dim 4 (= dim Σ̄^1 − δ
= 7 − 3). REDUCIBLE: ≥2 top components, one per Σ̄^1-component:
  - Branch A (`detA₁≠0` ⟹ `A₂ = E A₁⁻¹` forced) sits in `{detA₂=0}`, dim 4.
  - Branch B (`detA₁=0`, rank-1 A₁) sits in `{detA₁=0}`, dim 4 (361/397 generic pts dim 4; the
    36 dim-5 readings are SINGULAR points, not a component).
  Each fibre component sits in a DISTINCT Σ̄^r-component at codim δ within it — the "uniform +δ".

**C3 — the going-down chain (pinned).** `R := Sd` (G2-2's output ring = O(target rank-locus chart),
regular dim δ); `S := B_loc` (= O(Σ̄^r ∩ chart)), a `Sd`-algebra via the localized comorphism. Want
`S ≅ₐ[Sd] Sd ⊗_k F_E` (free ⟹ flat ⟹ HasGoingDown). `P` minimal prime of fibre-ideal in `S`, lies
over the maximal `m_B` of `B` in `R` (height δ). `P` minimal in `S/m_B S ≅ F_E` ⟹ relative height 0.
`height_S P = δ + 0 = δ` ⟹ `codim_{Σ̄^r}(fibre) = δ`. Then `+ cCodim_{Rep}(Σ̄^r)` (Brick A) over
minimal primes ⟹ `codim_{Rep}(fibre) = C + δ`. **Note: the `+C` is NOT automatic from Brick A — it
needs the minimal-prime/catenary assembly** (Codex caveat, confirmed).

**C4 — the CI "reserve route" is DEAD (a trap I checked and killed).** I found the algebraic identity
`(d_N−r)(d_0−r) + δ = d_N·d_0` ALWAYS (a complete-intersection-looking identity), and generic smooth
fibre points give codim `d_N·d_0` for `r≥1` across `(2,2,2),(3,3,3),(2,3,2)`. BUT this is a CONFOUND:
`(d_N−r)(d_0−r) = C_single` (codim of the TARGET `Mat^{rk≤r}` in `Mat`), which is NOT the BundleShift
target's `C = cCodim_{Rep}(Σ̄^r)` (the type-A quiver combinatorial codim in `Rep_d`). They agree only
when `Σ̄^r` has the same codim in `Rep_d` as the target rank locus has in `Mat`. **This FAILS at r=0**:
for `(2,2,2)`, `cCodim_{Rep}(Σ̄^0) = 3` (LANDED, `codimRepCanonical (fibre d222 0)=3`, dim Σ̄^0=5),
while `d_N·d_0 = 4`. So the CI route gives the WRONG codim (4≠3) at r=0; `mult⁻¹(0)` is NOT a complete
intersection. The CI/Jacobian route also only certifies ONE component at a smooth point (Krull gives
the wrong-direction bound; the lower bound is the whole content). Codex (decorrelated, Q3) independently
reached the same NO verdict. **Do not re-explore the CI/explicit-equation reserve.**

## Codex decorrelated read (Q1+Q2, `codex/q1q2-answer.md`)
- **Q1 (cheaper trivialization construction):** do NOT port G2-2's graph trick. Present
  `S := P ⊗_T R ≅ R[factor entries]/(mult(A) − B_univ)`, then **endpoint row-column normalization**:
  `B = L E H` (L,H unipotent/triangular built from the target Schur blocks `Δ,P,Q`), normalize the
  FIRST and LAST factors `Ã₁ = A₁ H⁻¹`, `Ã_N = L⁻¹ A_N`, middle factors unchanged. Then
  `mult(A)=B ⇔ mult(Ã)=E`, transporting the ideal to `(mult(Ã)−E)`, giving `S ≅ R[Ã]/(mult(Ã)−E) ≅
  R ⊗_k F_E`. The explicit section: canonical `e_i` with `I_r` pivot block, `e_N···e_1 = E`,
  `s(B)_1 = e₁H`, `s(B)_N = L e_N`, middle `e_i`. **This is the key construction** — it sidesteps the
  reducible-rank-ideal wall by making factoring a FIBRE relation (`ℓm=0`), not a base obstruction.
- **Q2 (flatness chain):** `S ≃ₐ[R] R ⊗_k F_E` ⟹ `Module.Free R` (F_E free over field k) ⟹
  `Module.Flat R S` (`of_linearEquiv`) ⟹ `HasGoingDown` ⟹ `height_eq_height_add_…`. SOUND. The
  flat-quasi-finite brick is the WRONG tool (fibre positive-dim ⟹ QuasiFiniteAt FAILS). For
  `height m_B = δ`: use the explicit `Localization.Away detSchurS` presentation (poly ring in δ Schur
  vars), prove the point ideal has height δ — don't rely on "regular dim δ" alone.
- **Size estimate:** relative chart flatness = 4–6 modules; full ambient `C+δ` theorem with
  localization + minimal-prime bookkeeping = 7–10 modules. Hard wall = the explicit quotient/tensor
  `AlgEquiv`, not Mathlib's flatness API.

## Verdict: total presentation is MATERIALLY HARDER than G2-2's base
- G2-2 base: single matrix, target entries ARE variables, ONE irreducible locus, the Schur relation
  forces B22 as a graph ⟹ clean graph-ideal height squeeze.
- G2-3 total: `Rep_d` product, product entries are degree-N polys, rank ideal FACTORS (REDUCIBLE,
  θ>1), the object is a fibre-BUNDLE trivialization `S ≅ R ⊗_k F_E` whose construction needs the
  endpoint-normalization AlgEquiv (genuinely new) + a per-component minimal-prime assembly for `+C`.
  The going-down step itself is a one-liner once the AlgEquiv exists; the AlgEquiv IS the wall.

## Two structural simplifications found
- **Single chart suffices for the fibre.** At the normal form `E = diag(I_r,0)` (G1 reduces to E),
  E's pivot minor = 1 ≠ 0, so the WHOLE fibre `mult⁻¹(E)` lies in the single pivot chart. No
  multi-chart gluing for the fibre.
- **Rank-restriction is FORCED.** The going-down base must be `R = Sd` (= O(target `Mat^{rk≤r}`
  chart), dim δ) and `S = O(Σ̄^r ∩ chart)` — NOT the full target/total chart. On the full target chart
  `mult` is still non-flat (other product entries degenerate), so flatness only holds after restricting
  the target to `Mat^{rk≤r}`. Consequence: `S` already quotients by the Σ̄^r ideal, so heights in `S`
  are codim-WITHIN-Σ̄^r (= δ); the `+C` (to codim in Rep_d) is a SEPARATE minimal-prime/catenary
  assembly reusing Brick A — a distinct rung from the going-down rung.

## API probe (throwaway, built green at v4.29, then deleted)
All five flatness/going-down closers compile: `Module.Free R (R ⊗[k] F)`, free⟹flat⟹HasGoingDown,
`Algebra R (R ⊗[k] F)`, `Module.Flat R (MvPolynomial σ R)`, `Module.Flat.of_linearEquiv e.toLinearEquiv`.
**The flatness/going-down closer is a one-liner once the `AlgEquiv S ≅ R ⊗_k F_E` exists.** The wall is
the AlgEquiv, NOT Mathlib API.

## The G2-3 rung-ladder (tide-sized)
| Rung | What | Reuse vs new | Size | Risk |
|---|---|---|---|---|
| R2-1 | Localized total ring `B_loc` as an `R=A_loc`-algebra via `Localization.Away.mapₐ multComap detΔ` | API present (ChartFlatnessProbe pins it) | S | low |
| R2-2 | Graph/base-change presentation `S_rk ≅ R[factor entries]/(mult(A)−B_univ) = P ⊗_T R` (rank-restricted) | new scaffolding; engine has only `vanishingIdeal`, NO quotient-ring presentation of O(Σ̄^r) | M–L | med |
| R2-3 | **The endpoint-normalization AlgEquiv** `S_rk ≅ R ⊗_k F_E` (B=LEH, normalize endpoints, transport ideal) | GENUINELY NEW (validated on anchor) | L | **HIGH — the wall** |
| R2-4 | free ⟹ flat ⟹ HasGoingDown ⟹ `height_eq_height_add` ⟹ `codim_{Σ̄^r}(fibre)=δ` | LANDED API (one-liner closer) | S | low |
| R2-5 | `height m_B = δ` (explicit `Localization.Away detSchurS` poly presentation) + "P minimal over fibre ideal ⟹ relative height 0 in `S/m_B S ≅ F_E`" | reuse G2-2's Sd + minimal-prime API | M | med |
| R2-6 | `+C` assembly: `codim_{Rep}(fibre-component) = C + δ` per minimal prime, then `iInf` (reuse Brick A `minimalPrimes_sigmaIdeal_eq`) | reuse Brick A + SigmaCodim catenary | M | med |

Total: ~6 rungs, ≈7–10 modules (matches Codex). G2-4/G2-5 (reducibility) FOLD into R2-6 — the
per-component matching is the same minimal-prime bookkeeping, not a separate wall.

## F_E open question (flagged, not resolved)
`F_E = O(mult⁻¹(E))` must be FREE over k (automatic — any k-vector space is free) AND its structure
(reducibility, the `ℓm=0`-type relations) must be tractable enough to BUILD as an explicit ring in
R2-3. The anchor's `F_E = k[u,v,X,Z,ℓ,m]/(uX+vZ−1, ℓm)` is concrete; for general N the fibre over E
is the N-chain zero/rank-product locus (middle factors free, endpoints carrying the `I_r` block). Its
explicit presentation for general N is itself a sub-construction inside R2-3 — a possible second wall.

## F_E need not be decomposed (softens the second-wall worry)
R2-3 only needs `F_E := k[Ã entries]/(mult(Ã)−E)` with `E` a CONSTANT matrix — the fibre over a fixed
point, uniform in N (generic N-chain product = E). It does NOT need F_E's irreducible decomposition or
the `ℓm=0` relations. So the wall is squarely R2-3: proving the endpoint-normalization (entries involve
`Δ⁻¹`, defined on the localized ring) is a well-defined AlgEquiv that carries the ideal
`(mult(A)−B_univ)` to `(mult(Ã)−E)` — a polynomial-identity ideal-transport over the localization.

## CLOSE / reflection
- **Most likely to advance the expedition:** Claim G2-3-A (the endpoint-normalization trivialization).
  It is the right object, it's decorrelated-confirmed, the flatness/going-down closer is a verified
  one-liner, and it folds G2-4/G2-5 (reducibility) into the `+C` assembly. The route is REACHABLE at
  v4.29 — no Mathlib gap — but it is materially harder than G2-2 (≈7–10 modules, ~6 rungs).
- **Most likely to break:** R2-2/R2-3 — the leap from the engine's `vanishingIdeal`-only handle on
  O(Σ̄^r) to an explicit `R`-algebra QUOTIENT presentation `R[Ã]/(mult−B_univ)` and the
  ideal-transport AlgEquiv. The engine has NO quotient-ring presentation of the total space; this is
  from-scratch affine-AG scaffolding. If R2-2's base-change presentation can't be made to compute
  cleanly (the localized comorphism's algebra/scalar-tower bookkeeping, à la G2-2's `blockAlgEquivLoc`
  but for a non-graph ideal), R2-3 has nothing to stand on.
- **Next computation to clarify:** pin R2-2 precisely — build (throwaway) the localized comorphism
  `A_loc → B_loc` as an `IsLocalization.Away.mapₐ` and check whether `B_loc ≅ A_loc[factor entries
  modulo the localized fibre ideal]` is expressible with the existing `MvPolynomial.isLocalization` +
  scalar-tower machinery G2-2 already used. That decides whether R2-2 is "reuse G2-2's localization
  scaffolding" (M) or "new scheme-free affine presentation" (L) — the swing factor in the size estimate.
