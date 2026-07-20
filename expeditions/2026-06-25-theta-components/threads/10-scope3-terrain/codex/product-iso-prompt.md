# Consult: Lean route for the deep product trivialization + reducedness wall (DLN fibre)

I am mapping the Lean (Lean 4 + Mathlib v4.29) formalisation route for "scope-3" of a research expedition:
the local-trivial bundle + smoothness of a fibre of the matrix-multiplication map for deep linear networks.

## Setup (the math, certified TRUE by exact algebra)

- Dimension vector `d : Fin (N+1) → ℕ`; `Rep_d` = tuples of composable matrices `(A_{N-1},...,A_0)`,
  `A_i : Mat(d_{i+1} × d_i)`. `mult d A = A_{N-1}···A_0 : Mat(d_N × d_0)`.
- Target `B` of rank `r`; the FIBRE `F = mult^{-1}(B)`. We work on the pivot chart `{ΔP ≠ 0}` where
  `ΔP` = the top-left `r×r` minor of the generic product (a unit on the chart).
- `fibreGenIdeal d B = (mult(Ã) − B)` in `MvPolynomial (RepCoord d) k`; `FibreAlg d B = k[Ã]/fibreGenIdeal`.
- The rank locus `Σ̄^r = {rank(mult) ≤ r}`, `sigmaIdeal = vanishingIdeal(Σ̄^r)` (RADICAL, it's a vanishingIdeal).
- `Sred = Localization.Away(ΔPdeep) ⧸ IadDeep` (the rank-locus chart ring), PROVED reduced (`isReduced_Sred`).

## What is ALREADY built (sorry-free, Lean)

1. `FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`: GIVEN a `k`-algebra iso
   `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` (R nontrivial) AND `IsReduced S`, concludes `fibreGenIdeal d B` is
   RADICAL. The tensor-with-a-field descent (`isReduced_of_tensor`) is proved. So the reducedness wall is
   REDUCED to: build `e` (the product/tensor trivialization) with `S = Sred`, `R = SchurLoc` (a localized
   polynomial domain).
2. `Sred` is proved reduced (`isReduced_Sred`); the `SchurLoc`-algebra structure on `Sred` is built
   (`schurToSred`, `sredSchurAlgebra`, scalar tower `k → SchurLoc → Sred`).
3. A DIFFERENT chart iso `e_β : Localization.Away(chartDsig) ≃ₐ[k] Localization.Away(chartGfib)` is built
   (`chartLocalizedAlgEquiv`) — localizations of the two reduced vanishingIdeal-quotients (Σ^r side and
   fibre side). This was used for the codim result (a `ringKrullDim` equality), radical-INSENSITIVELY. It is
   NOT in product/tensor form.
4. `EndpointNormalization`: a gauge-change `AlgEquiv` (the substitution `A_i ↦ P_{i+1} A_i P_i^{-1}`) on the
   unquotiented polynomial ring over ANY coeff ring R, with `aeval_gaugeSub_multPoly: aeval (gaugeSub P)(multPoly) = L^{-1}·multPoly·H^{-1}` — the endpoint-normalization that turns `mult(A)=LEH` into `mult(Ã)=E`.
5. Generic-smoothness machine for ORBIT closures (`OrbitSmooth.isSmoothAt_normalFormIdeal`): proves
   `IsSmoothAt k m_M` for an orbit-closure point via "dense smooth locus (`dense_smoothLocus_of_perfectField`,
   needs `[IsReduced X]`) ∩ dense orbit points, then G_d-transport". Fully worked.
6. The fibre Jacobian (`FibreJacobian`): tangent space = ker(Jacobian) at a rational point, UNCONDITIONAL;
   `finrank(ker) + rank(matrix) = card(RepCoord)`. The rank value `= C+δ` was NOT computed (codim went via
   Krull dim, not the Jacobian).
7. `SmoothPointRegular`: `IsSmoothAt k m ⟹ regular local ring` (the converse direction), with the étale
   dimension bridge. Mathlib has NO `regular ⟹ smooth`.

## The certified structural mechanism (thread 16, exact algebra over ℚ on ~11 cases + Codex)

`F_E` reduced is INHERITED from the reduced rank locus `Σ̄^r` via faithfully-flat local triviality: the
endpoint group `GL(d_N)×GL(d_0)` acts transitively on rank-r matrices with a regular Gaussian-elimination
section on the pivot chart, so `mult^{-1}(U) ≅ U × mult^{-1}(E)` scheme-theoretically. Reducedness DESCENDS:
`Sred reduced ⟹ Sred ≅ SchurLoc ⊗_k FibreAlg reduced ⟹ FibreAlg reduced`. The product iso `e` is the
endpoint-normalization (gauge by the Schur-data unipotents L, H built from the chart). The fibre is REDUCIBLE
in general (N components for a d=2 chain) and NON-equidimensional for low r — but always reduced.

## My questions (be concrete + skeptical; I want honest cost, not optimism)

A. **The product iso `e : Sred ≃ₐ[SchurLoc] SchurLoc ⊗_k FibreAlg`.** Is the cleanest Lean construction:
   (i) compose the existing endpoint-normalization gauge `AlgEquiv` (over R = SchurLoc, item 4) with a
   "base extraction" identifying the SchurLoc-base variables, presenting `Sred` as a polynomial/localization
   extension of `SchurLoc` whose remaining variables are exactly `FibreAlg`'s; OR (ii) some other route?
   What is the single hardest sub-lemma, and is it a tractable multi-tide effort or a months-scale AG build?
   Concretely: is `Sred ≃ SchurLoc ⊗_k FibreAlg` an instance of a packaged Mathlib "base change of a tensor /
   polynomial extension" fact, or all hand-built?

B. **Is there a cheaper route to `fibreGenIdeal` radical that AVOIDS building the product iso `e`?** E.g.:
   - via the EXISTING chart iso `e_β` (item 3) — does `Away(chartDsig) ≅ Away(chartGfib)` plus `Σ^r` reduced
     give `fibre` reduced more directly (both sides are already reduced vanishingIdeal-quotient localizations
     — but does that PROVE `fibreGenIdeal = vanishingIdeal(fibre)`, i.e. the generator ideal is radical, vs
     just relating the two reduced quotients)?
   - via a Jacobian/generic-smoothness argument (`F` reduced because smooth on a dense open + the singular
     locus has codim ≥ 1 + ... ) — but this seems circular with smoothness, which itself wants reducedness.

C. **The smoothness route depends on the reducedness wall.** `dense_smoothLocus_of_perfectField` needs
   `[IsReduced X]`. So the honest smooth-locus statement (fibre smooth away from the deepest stratum) seems to
   REQUIRE reducedness first. Confirm: is there ANY route to the smooth locus that does NOT first need the
   fibre scheme reduced? (The orbit-closure module got reducedness for free — domain. The fibre does not.)
   Could one instead prove smoothness on the pivot chart directly via a submersive/complete-intersection
   Jacobian criterion (Mathlib `SubmersivePresentation`/`isUnit_jacobian_of_linearIndependent...`) at points
   where the Jacobian has full rank, sidestepping the global reduced-scheme generic-smoothness theorem?

D. **Sequencing.** Given all the above: is the reducedness wall (product iso `e` + descent) genuinely the
   GATING first tide for both the honest bundle statement and smoothness — or can the bundle and/or smoothness
   be stated honestly in a form that does NOT need it? What is the minimal honest "locally-trivial bundle"
   statement given there is NO scheme-level FiberBundle API in Mathlib?

Give me: the recommended decomposition into lemmas with rough sizes, the hardest sub-piece, and a blunt
months-scale-vs-tractable verdict for the product iso `e`.
