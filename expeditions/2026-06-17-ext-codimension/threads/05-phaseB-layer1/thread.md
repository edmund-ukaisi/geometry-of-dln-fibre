# Thread 05 — Phase-B Layer 1: `orbitLinearCodim` (formaliser)

The honest **linear (tangent-space) codimension** capstone tying the geometry-to-come onto the
committed Phase-A deformation `Ext¹`. New module `lean/DLNFibre/Core/OrbitLinearCodim.lean` (Core
engine; imports only `DeformationExt`). Build green, `scripts/sorries` = 0, `#print axioms` on both
headlines = `[propext, Classical.choice, Quot.sound]` (clean). Fidelity-reviewed PASS (all 5 checks).

## What it adds

`orbitLinearCodim M := finrank C¹(M,M) − finrank (im δ_M)` — the codimension of the orbit's tangent
space `B¹ = im δ_M` inside the ambient tangent space `C¹ = cochain1 d d`. Two headlines:

- `orbitLinearCodim_eq_finrank_deformationExt1 M : orbitLinearCodim M = finrank (deformationExt1 M M)`
  — pure rank–nullity (`Submodule.finrank_quotient_add_finrank`; `deformationExt1 = coker δ`).
- `orbitLinearCodim_eq_multSum L : (orbitLinearCodim (⊕L) : ℤ) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`
  — chains the above with the committed `finrank_deformationExt1_self_eq_multSum` (Cor 3.5).

Witnesses ((2,2,2)/ℚ): `(1,1)`-orbit `orbitLinearCodim = 3`; `{A=0}` locus `= 4` (Ex 4.3 / §4 table).

## Name = content — the deferral (Layer 2)

`orbitLinearCodim` is the **expected / tangent-space** codimension. It equals the *geometric*
`codim Ō_M` **only if** (a) the orbit is smooth and its tangent space is `B¹ = im δ`, and (b) the
orbit-dimension bridge holds: `dim Ō = dim C¹ − dim Ext¹` (Voigt). Both are **DEFERRED**; nothing in
this module proves them. No declaration is named `codim O` / `codim_orbit`. This is the honest linear
shadow of Voigt's codimension formula, not Voigt's theorem.

## Statement cards

> **Claim (rank–nullity).** The expected (tangent-space) codimension of the orbit equals the
> deformation-`Ext¹` dimension: `dim (C¹ ⧸ im δ_M) = dim (coker δ_M)`.
>
> - **Lean:** `DLNFibre.Core.orbitLinearCodim_eq_finrank_deformationExt1`
>   (`lean/DLNFibre/Core/OrbitLinearCodim.lean` @ `8205df4` — pre-integration; controller rebumps)
> - **Gloss.** `finrank C¹(M,M) − finrank (range δ_M) = finrank (deformationExt1 M M)`, where
>   `deformationExt1 M M = C¹ ⧸ range δ_M`.
> - **Proved.** The equality, for any `Tuple` `M` over a field, unconditionally.
> - **Assumed.** `Field k` (finrank additivity over the quotient).
> - **Cited.** none.
> - **Deferred.** that this linear codimension equals the geometric `codim Ō_M` (orbit smoothness +
>   Voigt orbit-dimension bridge — Layer 2).
> - **Status.** sorry-free + reviewed.

> **Claim (multiplicity form, Cor 3.5 at the linear level).** For `M = ⊕L`, the expected
> codimension is the paper's quadratic form `Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`,
> `m = multiplicityArray L`.
>
> - **Lean:** `DLNFibre.Core.orbitLinearCodim_eq_multSum`
>   (`lean/DLNFibre/Core/OrbitLinearCodim.lean` @ `8205df4` — pre-integration; controller rebumps)
> - **Gloss.** `(orbitLinearCodim (intervalDirectSum L) : ℤ)` equals the four-fold `Finset.Icc` sum
>   over `1≤i≤u≤j≤v≤N` of `multiplicityArray L (i-1)(j-1) * multiplicityArray L u v`.
> - **Proved.** The equality, for any interval list `L` over a field.
> - **Assumed.** `Field k`.
> - **Cited.** none (the Cor 3.5 RHS is reproved upstream in `DeformationExt`).
> - **Deferred.** same as above — the geometric `= codim Ō` reading rests on Voigt (Layer 2).
> - **Status.** sorry-free + reviewed.
