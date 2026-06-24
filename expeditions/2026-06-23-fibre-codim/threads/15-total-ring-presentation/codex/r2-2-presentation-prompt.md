<task>
Lean 4 + Mathlib v4.29 formalisation. We are building the fibre-codimension result of
Lehalleur–Rimányi Lemma 4.6 for deep linear networks. This is a SPECIFY/PROBE consult on rung
R2-2 (the "localized total-ring presentation"). The KEY decision we need from you:

  Does presenting the localized TOTAL ring `S = O(Σ̄^r ∩ pivot-chart)` as an explicit `R`-algebra
  QUOTIENT (`R := Sd`, the localized base ring) REUSE the landed G2-2 base-presentation machinery
  (`blockAlgEquivLoc` = an `IsLocalization.algEquivOfAlgEquiv`, the `graphIdeal`/`graphIdealQuotientEquiv`
  block-elimination, the `k → B → Q` scalar-tower pattern) — verdict **M** — or does it need NEW
  scheme-free affine scaffolding the engine does not carry — verdict **L**?

We need your independent verdict + the precise "cut-ideal handle" the downstream `AlgEquiv` (R2-3)
will consume, so we don't grind a doomed presentation.

## Setup (objects that EXIST and are LANDED, sorry-free, in the engine)

Fixed dimension vector `d : Fin (N+1) → ℕ`, `N ≥ 1`, field `k` (`IsAlgClosed`, `CharZero` where needed).

- `RepCoord d := Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)` — one variable per factor entry over
  ALL N factors. The rep coordinate ring is `MvPolynomial (RepCoord d) k`.
- `mult d A = A_N ⋯ A_1`. `multPoly d r c : MvPolynomial (RepCoord d) k` = the generic product entry
  (= `(mult d genericTuple) r c`), a DEGREE-N polynomial in the RepCoord variables (NOT a coordinate
  variable — this is the crux difference from the base case).
- `multComap d : MvPolynomial (Fin d_N × Fin d_0) k →ₐ[k] MvPolynomial (RepCoord d) k`,
  `multComap d (X (r,c)) = multPoly d r c`. (The comorphism of `mult`. LANDED.)
- `sigmaIdeal d r : Ideal (MvPolynomial (RepCoord d) k)` — the vanishing ideal of
  `Σ̄^r = productRankLocusLE d r` (rank of product ≤ r). Carried ONLY as a `vanishingIdeal` (an opaque
  closed-locus ideal); there is NO quotient-ring presentation of `O(Σ̄^r)` in the engine.
  Over `IsAlgClosed`, `sigmaIdeal` is prime (the relevant strata), height = `C = cCodim d r`.
- `fibreGenIdeal d B = span {multPoly d r c − C (B r c)} = Ideal.map (multComap d) (maxIdealOfPoint d B)`
  — the fibre-over-B generator ideal (extension of B's max ideal along the comorphism). LANDED.
- `detPivotPoly` etc.: on the SINGLE-matrix base `dStratum q p = ![q,p]` (N=1), the pivot r×r minor
  of `multPoly`. Inverting it = the pivot chart.

## The LANDED G2-2 BASE presentation (the machinery whose reuse is the M/L question)

For the SINGLE matrix `dStratum q p` (N=1, where target entries literally ARE the RepCoord variables):
- `blockAlgEquivLoc : Localization.Away detΔ ≃ₐ[k] MvPolynomial B22block Sd`
  (= `IsLocalization.algEquivOfAlgEquiv` localizing the reindex-then-split `blockAlgEquiv` at
  `detΔ ↦ C detSchurS`). Built with the `k → B → Q` scalar tower + `MvPolynomial.isLocalization`.
- `Iad := (sigmaIdeal (dStratum q p) r).map (algebraMap _ (Localization.Away detΔ))` — the localized base
  ideal. PROVED `blockAlgEquivLoc(Iad) = graphIdeal forcedB22` (height squeeze: both prime, height C,
  J ⊆ Ψ(Iad), `height_strict_mono_of_is_prime`).
- `forcedB22 ab = mk' Sd (forcedNum ab) detSchurS` — the FORCED B22 block value `B21 Δ⁻¹ B12` in
  `Sd = Localization.Away detSchurS`.
- `basePresentationEquiv : (Localization.Away detΔ ⧸ Iad) ≃ₐ[k] Sd` — the final base presentation.
  (Sd is regular dim δ.)
This whole construction REQUIRES that the target B22 entries ARE coordinate variables (so the Schur
relation `B22 = B21 Δ⁻¹ B12` is a GRAPH `X − C(forced)`). The recon already established (sympy) that on
the TOTAL side this FAILS: product entries are degree-N polys, the total rank ideal FACTORS / is reducible
(`det(A₂A₁) = detA₁·detA₂`), so the B22-graph-elimination does NOT port.

## The recon's intended R2-2 object (decorrelated earlier Codex; we want your fresh read)

`R := Sd` (G2-2's `SchurLoc`, the localized base ring = `O(Mat^{rk≤r} target-chart)`, regular dim δ).
`S := O(Σ̄^r ∩ pivot-chart)` = `(MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r)` localized at the image of
`detΔ(product)`. The intended presentation (on the pivot chart, detΔ of the PRODUCT inverted):

  `S ≅ₐ[R] R[ factor entries ] / (cut ideal: mult(A) − B_univ)`

i.e. "rep ring localized, modulo the cut ideal `mult(A)=B`, as an R-algebra via the localized comorphism."
Then R2-3 (NOT this rung) does endpoint-normalization `B = LEH`, normalize `Ã₁=A₁H⁻¹, Ã_N=L⁻¹A_N`, to get
`S ≅ R ⊗_k F_E` (free over k ⟹ flat ⟹ going-down ⟹ `codim_{Σ̄^r}(fibre) = δ`).

Anchor numerics ((2,2,2), r=1): #factor-entries=8, #target-entries=4, δ=3, dim Σ̄^1 = 7 = δ + C(=1)? no:
dimRep=8, dim Σ̄^1=7, so C=1; fibre-over-E dim = dim Σ̄^r − δ = 4.

## The tensions WE see (vet these — tell us if we are wrong)

1. The base ring `R = Sd` is built for the SINGLE matrix `dStratum q p` (the TARGET `Mat^{rk≤r}`), with
   its OWN `RepCoord (dStratum q p)` (one variable per target entry). But `S` lives over `RepCoord d`
   (factor entries, N factors). So the "R-algebra structure on S via the localized comorphism" must factor
   `R = Sd` (target-side) → `S` (factor-side) through `multComap d` localized at `detΔ(product)`. Is
   `Localization.Away.mapₐ multComap detΔ` (LANDED to exist) really an `algebraMap R → S`, i.e. does the
   target localization `Localization.Away detΔ_target` actually EQUAL/embed as `R = Sd` after the
   base presentation `basePresentationEquiv`? Or is there a mismatch (the base presentation quotients by
   `Iad` to GET Sd, but the comorphism's source is the UN-quotiented target localization)?

2. The presentation claims `S ≅ R[factor entries]/(cut ideal)`. But `S` is `(rep ring ⧸ sigmaIdeal)`
   localized — it ALREADY quotients by the Σ̄^r ideal. For the presentation to be `R[Ã]/(mult(Ã)−E)`
   WITHOUT a separate `sigmaIdeal` quotient, the cut ideal `(mult(A)−B_univ)` over `R = O(rank≤r chart)`
   must ALREADY enforce rank(product) ≤ r (because `B_univ ∈ R` is rank ≤ r on the chart). Is that the
   right reading — i.e. is `(rep⧸sigmaIdeal)_loc ≅ R[Ã]/(cut)` actually TRUE, or does the `sigmaIdeal`
   quotient leave residual content the cut-ideal-over-R does not capture? Concretely: is the localized
   comorphism `R → S` FLAT/does the fibre product `Spec S = Spec R ×_{Mat} Rep` literally equal
   `Σ̄^r ∩ chart`?

3. `R[factor entries] := R ⊗_k MvPolynomial (RepCoord d) k` (the base-changed rep ring), and `S := P ⊗_T R`
   (T = target ring, P = rep ring) per the recon. The "cut ideal" is then `ker(R ⊗_k k[Ã] → S)`. Is the
   right Mathlib object `Algebra.TensorProduct` + a `graphIdeal`-style kernel, and does the `graphIdeal`/
   `ker_aeval_eq_graphIdeal` engine (which gave G2-2 its elimination) apply when the "forced" values are
   NOT a graph (mult is degree-N, not linear in the factor entries)?

## What we have LANDED to reuse (Mathlib v4.29 + engine)

- `IsLocalization.Away.map`/`.mapₐ`, `IsLocalization.algEquivOfAlgEquiv`, `MvPolynomial.isLocalization`,
  the `k→B→Q` scalar-tower `IsScalarTower.of_algebraMap_eq` pattern (from `blockAlgEquivLoc`).
- `graphIdeal c = span{X i − C(c i)}`, `ker_aeval_eq_graphIdeal`, `graphIdealQuotientEquiv :
  MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R` (the elimination), `graphIdeal_isPrime` (R domain).
- `Algebra.TensorProduct.instFree`, `Module.Flat.of_linearEquiv`, `HasGoingDown` from flat,
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (all pinned, the R2-4 closer is a one-liner).
- `Ideal.map`, `Ideal.quotientEquivAlg`, `Ideal.quotientEquivAlgOfEq`, `RingEquiv.height_comap`.
</task>

<output_contract>
Six sections, terse, object-level (no pep talk):

1. VERDICT: **M** or **L** (one word), then 2–3 sentences why. (M = the localized total-ring
   QUOTIENT presentation `S ≅ₐ[R] R[Ã]/(cut)` reuses G2-2's `blockAlgEquivLoc`/`IsLocalization`/
   `graphIdeal` scalar-tower machinery with only routine adaptation; L = it needs genuinely new
   scheme-free affine scaffolding — name what.)

2. THE PINNED PRESENTATION: the exact Lean-shaped object for `S`, the `R`-algebra structure (the
   algebraMap `R → S` route), and the cut-ideal handle the R2-3 AlgEquiv will consume. Be concrete
   about types (Localization.Away of what, ⧸ what, ⊗ over what).

3. THE THREE TENSIONS: adjudicate tensions 1, 2, 3 above — for each, TRUE/FALSE/needs-care + the
   one-line reason. Especially tension 2 (does the cut-ideal-over-R presentation actually equal
   `(rep⧸sigmaIdeal)_loc`, or is a separate sigmaIdeal quotient needed?).

4. CUT-IDEAL HANDLE clarity: is the handle the AlgEquiv needs CLEAR (a named ideal + a named quotient
   equiv chain) or UNCLEAR (some step has no Mathlib/engine lemma)? If unclear, name the missing lemma.

5. REACHABILITY: M-route module estimate (count) + the single hardest sub-step of R2-2 ITSELF (not
   R2-3). If L, the precise wall + whether a pen-and-paper ideal-transport certificate is needed
   BEFORE any formaliser commits.

6. ONE THING WE MIGHT BE GETTING WRONG: the most likely error in our framing.
</output_contract>
