# Statement card — L2a: Zariski cotangent = Jacobian kernel

> **Claim.** For `R = MvPolynomial σ k` (`σ` a `Fintype`, `k` a field), an ideal `I = span(range g)`
> with a finite generating family `g : Fin m → R`, and a `k`-rational point `a : σ → k` of `V(I)`
> (`∀ i, eval a (g i) = 0`), with `A = R ⧸ I` and `m_A` the maximal ideal at `a` (the kernel of the
> augmentation `ε : A →ₐ[k] k` induced by `eval a`): the `k`-dimension of the local cotangent space
> at `a` equals the `k`-dimension of the kernel of the Jacobian of the generators at `a`.
>
> - **Lean:** `DLNFibre.Core.finrank_cotangentSpace_eq_finrank_ker_jacobian`
>   (`lean/DLNFibre/Core/CotangentJacobian.lean` @ `f600c40`)
> - **Gloss.** With `jacobian g a : (σ → k) →ₗ[k] (Fin m → k)`,
>   `jacobian g a v i = ∑ x, (eval a (pderiv x (g i))) • v x` (rows = generators, cols = `σ`; it is
>   `(jacobianMatrix g a).mulVecLin`, entry `(i,x) = eval a (pderiv x (g i))`), the theorem states
>   `finrank k (IsLocalRing.CotangentSpace (Localization.AtPrime (maxIdealAt g a hg)))
>      = finrank k (LinearMap.ker (jacobian g a))`.
>   Equivalently (cokernel form, `finrank_ker_jacobian_eq_finrank_coker`):
>   `finrank k (ker (jacobian g a)) = finrank k ((σ → k) ⧸ range (jacobianTranspose g a))
>      = card σ − rank(Jacobian)`. The residue field `κ(m_A) = k` since `a` is `k`-rational
>   (`m_A = ker (aug g a hg)`, and `aug` is split by `algebraMap k A`).
> - **Proved.** The full finrank equality, unconditionally, for any field `k`, any `Fintype σ`, any
>   finite generating family `g`, and any `k`-rational point `a ∈ V(span(range g))`. Sorry-free,
>   `#print axioms = [propext, Classical.choice, Quot.sound]`. Supporting reusable lemmas, all proved:
>   - `kerCotangentToTensor_split_bijective` — for a split augmentation `ε : A →ₐ[k] k` of a `k`-algebra
>     `A`, the conormal map `kerCotangentToTensor k A k : (ker ε).Cotangent → k ⊗[A] Ω[A⁄k]` is bijective
>     (general; the recon-flagged crux);
>   - `finrank_cotangentSpace_localization_eq_cotangent` — for any `k`-algebra `A` and maximal `p`,
>     `finrank k (CotangentSpace (Localization.AtPrime p)) = finrank k (p.Cotangent)` (general);
>   - `span_cotangent_eq_top` — `I.Cotangent` is `R`-spanned by `toCotangent` of a generating family.
> - **Assumed.** `a` is a `k`-**rational** point (`a : σ → k`, the generators vanish at `a`). This is
>   exactly the L2 use-case (the orbit normal form `M` is a rational point). No smoothness/regularity
>   assumed — the equality is exact at an arbitrary (possibly singular) point.
> - **Cited.** None. Built entirely on Mathlib `Ideal.Cotangent`, `KaehlerDifferential`
>   (`kerCotangentToTensor` / `mapBaseChange` / `mvPolynomialBasis`), `retractionKerCotangentToTensorEquivSection`,
>   `Ideal.tensorCotangentEquiv`, `IsLocalizedModule` — zero new cited interfaces.
> - **Deferred.** None for this lemma. Downstream (L2b) consumes it to identify
>   `finrank(cotangent at m_M)` with `finrank(range δ⁰)` via `ker(J_M) = range δ⁰` (the orbit-map
>   linearisation), which is a separate thread.
> - **Status.** sorry-free (awaiting reviewer for fidelity → `reviewed`).

## De-risk verdict (the thread's purpose)

**BOUNDED.** The "Zariski tangent = Jacobian kernel" packaging is reachable on
`Ideal.Cotangent` / `KaehlerDifferential.kerCotangentToTensor` / `MvPolynomial.mvPolynomialBasis` /
`Ideal.tensorCotangentEquiv` — no genuinely-absent sub-library. The kill-condition did **not** fire.
The one step recon flagged as most-likely-to-break (the split-augmentation conormal bijection) is the
clean general lemma `kerCotangentToTensor_split_bijective`, proved via the Mathlib retraction-↔-section
equivalence and `Ω[k⁄k] = 0`.

## (2,2,2) verification

Instantiated at thread-17's `Z_M` data: `σ = Fin 8` (= `a,b,c,d,e,f,g,h`), `m = 6` generators
(`det A_0 = X0·X3 − X1·X2`, `det A_1 = X4·X7 − X5·X6`, and the 4 entries of `A_1·A_0`), point
`M = (0,1,0,0,0,1,0,0)`. The lemma's `jacobianMatrix gen Mpt` was proved equal (Lean `example`,
`fin_cases` + `pderiv_X` + `simp`) to the hand/sympy Jacobian
`!![0,0,−1,0,0,0,0,0; 0,0,0,0,0,0,−1,0; 0,0,1,0,0,0,0,0; 0,0,0,1,1,0,0,0; 0,0,0,0,0,0,0,0; 0,0,0,0,0,0,1,0]`,
which has rank 3 (sympy-confirmed: 3 independent columns). Hence
`finrank(ker(jacobian gen Mpt)) = 8 − 3 = 5 = finrank(range δ⁰)` (thread-17), and the headline gives
`finrank(CotangentSpace at M) = 5`. (The symbolic-Jacobian-entry match is the substantive Lean check;
the rank=3 numeric is sympy-confirmed and elementary.)
