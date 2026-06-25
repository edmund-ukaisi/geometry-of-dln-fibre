# thread 16 — cut-ideal radical certification (R2-2/R2-3 ideal-transport, pen-and-paper)

**Type:** pen-and-paper (specialised scout) · a sharp truth-value adjudication via exact algebra. NO Lean.
R2-2 (thread 15) found verdict **L**: the G2-3 endpoint-normalization route needs an ideal-transport the
engine doesn't supply, and it hinges on a **radical/reducedness** fact that must be certified before any
formaliser builds the AlgEquiv. Hand back a certificate (the mechanism) or an obstruction (→ re-route).

## Read first
- `threads/15-total-ring-presentation/codex/{r2-2-presentation-prompt, r2-2-presentation-answer,
  r2-2-verdict-analysis}.md` — R2-2's wall write-up + Codex's reframing (routes a/b). **Your blueprint.**
- Synthesis §"G2-3 RECON VERDICT" (the endpoint-normalization route + the rung-ladder).
- `Core.DeterminantalBasePresentation` (R = `SchurLoc`), `Core.MultComorphism` (`multPoly`/`multComap`),
  `Core.SigmaCodim` (`sigmaIdeal = vanishingIdeal Σ̄^r`, radical; `minimalPrimes_sigmaIdeal_eq`).

## THE TRUTH-VALUE to adjudicate (sharp)
On the pivot chart, the route wants to identify the **cut presentation** `Scut := R[Ã]/(mult(Ã)−B_univ)`
(scheme-theoretic, degree-N cut equations) with the engine's **reduced** chart ring
`Sred := (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)[1/ΔP]` (`sigmaIdeal` = `vanishingIdeal(Σ̄^r)`,
radical). `Scut = Sred` ⟺ **the cut ideal `(mult(Ã)−B_univ)` is RADICAL** (equivalently, the fibre
`F_E = k[Ã]/(mult(Ã)−E)` is **reduced**, since the chart trivializes as a product over `R`).

**Adjudicate: is the cut ideal radical / is `F_E` reduced?** This is load-bearing: if NOT radical, the
trivialization `S ≅ R ⊗_k F_E` connects to a non-reduced object and the route (as stated) has a hole.
- **Witness (likely target):** the cut ideal IS radical / `F_E` reduced ⟹ certify the MECHANISM a
  formaliser can use (route (a) direct: `(sigmaIdeal).map(loc) = radical of the localized cut pullback`,
  or route (b) deferred: `F_E` reduced ⟹ `Scut` reduced ⟹ `Scut = Sred` post-R2-3 — say which is
  Lean-certifiable + the exact lemma chain / Mathlib handles).
- **Obstruction:** the cut ideal is NOT radical (nilpotents) ⟹ exhibit the witness + state the precise
  consequence for the route (S ≠ R⊗F_E) + the cleanest re-route (e.g. work with `Sred`/`F_E^red` directly,
  or a smoothness/Jacobian-criterion reducedness argument).

## Method (exact algebra — your remit)
- Anchor `(2,2,2), r=1`: compute a Gröbner basis of the fibre ideal `(A₂A₁ − diag(1,0))` over ℚ; test
  radical-ness (`I == radical(I)`, e.g. sympy/Singular/Macaulay2/Sage); inspect the primary decomposition
  (the recon found ≥2 components — confirm they're reduced, no embedded/nilpotent). Then a general-`N`/`d`
  argument: is the fibre `mult⁻¹(E)` (generically) reduced? (It's a "zero-product-type" locus — smooth
  locus dimension / Jacobian rank may give reducedness on the relevant component.)
- **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh) on the radical-ness + the
  Lean-certifiable mechanism; save under `threads/16-cut-ideal-radical/codex/`.

## Output (certificate to controller)
A certificate hand-off for the R2-2/R2-3 formaliser: the radical/reducedness VERDICT (with the anchor
computation + the general argument), the chosen route (a vs b) + the EXACT mechanism + Mathlib/engine
handles it needs (so the formaliser builds on confirmed contracts), OR the obstruction + the re-route.
No Lean / no commits to library files. In-repo notes only; never `~/.claude/**/memory/`; don't touch
other worktrees.

---

## VERDICT (pen-and-paper, 2026-06-24) — the cut ideal IS RADICAL / F_E IS REDUCED

**Truth-value: the fibre ideal `I_E = (mult(Ã) − E)` is RADICAL; `F_E = k[Ã]/I_E` is REDUCED.**
For every `N ≥ 1`, every dimension vector `d`, every target `E` (depends only on `rank E`, not on the
pivot normal form). Certified by exact algebra (Singular `primdecGTZ` + `radical` over ℚ) + a decorrelated
xhigh Codex consult that converged AND independently predicted the `d=(3,3,3)` component data.

### Exact-algebra certificate (Singular, ℚ, `primdecGTZ`)
Every case below: `radical(I) ⊆ I` (radical), and EVERY primary component equals its associated prime
(NO embedded primes, NO nilpotents). #comps matches Codex's type-A rank-pair rule exactly.

| case | dims | r | E | radical | #comps | comp dims |
|---|---|---|---|---|---|---|
| anchor | (2,2,2) | 1 | diag(1,0) | YES | 2 | 4,4 |
| genericE | (2,2,2) | 1 | [[1,2],[3,6]] | YES | 2 | 4,4 |
| genE2 | (2,2,2) | 1 | [[2,3],[4,6]] | YES | 2 | 4,4 |
| N=3 deep | (2,2,2,2) | 1 | diag(1,0) | YES | 3 | 8,8,8 |
| N=3 full | (2,2,2,2) | 2 | I | YES | 1 | 8 |
| wide | (3,2,3) | 1 | rank-1 | YES | 2 | 5,5 |
| narrow | (2,3,2) | 1 | diag(1,0) | YES | 1 (irred) | 8 |
| (1,2,1) | (1,2,1) | 1 | [1] | YES | 1 | 3 |
| full rank | (2,2,2) | 2 | I | YES | 1 | 4 |
| zero-prod | (2,2,2) | 0 | 0 | YES | 3 | 5,4,4 (non-equidim) |
| big | (3,3,3) | 1 | rank-1 | YES | 3 | 10,9,9 (non-equidim) |

The fibre is **reducible** in general (N comps for the `d=2` chain, one per rank-bottleneck position)
and **non-equidimensional** for low `r` (e.g. r=0, and (3,3,3) r=1) — but ALWAYS reduced.

### The MECHANISM (Codex angle (A), the load-bearing one — NOT smoothness/CM)
`F_E` reduced is **inherited** from the reduced ambient rank locus `Z_r = mult⁻¹{rank ≤ r}` (a type-A
quiver rank locus — KNOWN reduced: Buch–Fulton, Kinser–Rajchgot; normal/CM/rational-singularities) via
**faithfully-flat local triviality**: the endpoint group `GL(d_N)×GL(d_0)` acts transitively on rank-`r`
matrices, with a REGULAR section by Gaussian elimination on the pivot chart (denominators = powers of the
pivot minor), so `mult⁻¹(U) ≅ U × mult⁻¹(E)` scheme-theoretically over the rank-`r` orbit `U`. Reducedness
DESCENDS from the reduced left side along faithful flatness over `k`. This is EXACTLY the engine's
`S ≅ R ⊗_k F_E` route — and reducedness flows `Sred (reduced) ⟹ F_E reduced`, i.e. route (b)/Codex's
tension-6 reordering is the natural direction. (Generic-smoothness+CM is the WRONG global proof — the
fibre is not equidimensional/CM in general; reducedness is structural via the trivialization, not via CM.)

Verified scheme-side on anchor: `J_r=(det product)=detA₁·detA₂` is radical (Z_r chart reduced);
`sigmaIdeal`-generator `∈ I_E` (fibre ⊆ Σ̄^r automatically); dim arithmetic `dim Σ̄^1 (7) = δ (3) + dim F_E (4)`.

### CORRECTION to the R2-2 prompt framing
The R2-2 prompt asserted "sigmaIdeal is prime over IsAlgClosed". FALSE: the engine carries
`sigmaIdeal d r = sInf(orbitIdeals d r)` — an intersection of the minimal primes, hence RADICAL but
generally NOT prime (`Σ̄^1 = {detA₁·detA₂=0}` is reducible). `minimalPrimes_sigmaIdeal_eq` is plural by
design. This REMOVES the tension: `Sred` reduced+reducible and `F_E` reduced+reducible are consistent.

Codex consult: `codex/{radical-prompt.md, radical-answer.md}`.

## ROUTE for the R2-2/R2-3 formaliser (chosen: a hybrid — the radical-collapse IS the handle)

The decisive engine contract is `Core.MultComorphism` point 4:
  `vanishingIdeal(fibre d B) = radical(fibreGenIdeal d B)`   over `[IsAlgClosed k]`,
where `fibreGenIdeal d B = span{multPoly d r c − C(B r c)}` IS the cut ideal `I_E`.

My verdict (I_E radical) upgrades this to the clean identity the route needs:
  **`fibreGenIdeal d B = radical(fibreGenIdeal d B) = vanishingIdeal(fibre d B)`**
i.e. the `radical(...)` wrapper in the existing point-4 lemma COLLAPSES — the cut ideal is already its
own radical. This is the smallest-surface handle: one new lemma `fibreGenIdeal_isRadical` (or
`radical_fibreGenIdeal_eq_self`).

Two ways to prove `fibreGenIdeal_isRadical`, in increasing engine-friendliness:

- **(a-direct) the ideal-level identity.** Want `fibreGenIdeal = radical(fibreGenIdeal)`. The HARD part
  is the `⊇` (radical ⊆ ideal). This is NOT a formal corollary of `vanishingIdeal_isRadical` (that
  gives `radical(fibreGenIdeal) = vanishingIdeal(fibre)`, the OTHER side). It needs the geometric input:
  the scheme `mult⁻¹(B)` is reduced. Proving reducedness purely ideal-theoretically = re-deriving
  primary decomposition; AVOID.

- **(b-structural, RECOMMENDED) reducedness DESCENDS via the R2-3 trivialization.** This is Codex's
  tension-6 reordering, and it is the NATURAL direction of inference (my mechanism §):
    1. R2-3 builds `S ≅ₐ[R] R ⊗_k F_E` (endpoint normalization; F_E = `k[Ã]/I_E`).
    2. The AMBIENT rank-locus chart `Sred = (P/sigmaIdeal)[1/ΔP]` is reduced (engine: `sigmaIdeal` is a
       `vanishingIdeal`, hence radical via `vanishingIdeal_isRadical`; `Reduced (R/radical-ideal)`).
    3. `Sred ≅ S` (the chart trivialization, R2-3) ⟹ `S` reduced ⟹ `R ⊗_k F_E` reduced ⟹ (faithfully
       flat `k → R`, `R` a domain/regular) `F_E` reduced ⟹ `I_E` radical.
  So `Scut = Sred` is NOT a precondition of R2-3 — it is the CONCLUSION, and `I_E` radical is a corollary,
  not a lemma to prove first. **The formaliser should build R2-3 against `Sred` (reduced) directly and
  DERIVE `F_E` reduced** rather than assert cut-ideal radical-ness up front.

NET for the controller: the load-bearing reducedness is TRUE (certified). The route has NO hole. The
cleanest Lean shape carries reducedness from the engine's already-radical `sigmaIdeal`/`vanishingIdeal`
into `F_E` through the R2-3 AlgEquiv (route b), not by an independent radical proof of the cut ideal
(route a, which would need primary decomposition). Handles confirmed to exist:
`vanishingIdeal_isRadical` (NullstellensatzCodim:69), `vanishingIdeal(fibre)=radical(fibreGenIdeal)`
(MultComorphism pt 4), `sigmaIdeal = vanishingIdeal` (SigmaComponents:130), faithfully-flat/tensor
reducedness lemmas in Mathlib (`Algebra.TensorProduct`, `RingHom.reduced` descent).

### Mathlib reducedness-descent handle to confirm (the one open dependency)
`F_E reduced ⟸ R ⊗_k F_E reduced` over a field `k` (k → R faithfully flat). Mathlib has
`Algebra.TensorProduct` + reducedness-under-flat-base-change for FIELD base (separable/perfect — char 0
is fine). The formaliser should confirm the exact lemma name (`IsReduced` tensor a field, or via
`Localization`/faithfully-flat descent `RingHom.IsReduced`-pullback). This is the single contract to pin
before R2-3 closes — but it is a STANDARD descent, not new content.
