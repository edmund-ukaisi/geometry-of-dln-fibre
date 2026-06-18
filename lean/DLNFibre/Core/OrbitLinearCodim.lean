import DLNFibre.Core.DeformationExt

/-!
# `DLNFibre.Core.OrbitLinearCodim` — the expected (tangent-space) orbit codimension

For a tuple `M : Tuple d` (a representation of the equioriented `A_N` quiver, the diagonal case
`N = M`, target = source), the **expected / tangent-space codimension** of the orbit `O_M` is

  `orbitLinearCodim M := finrank C¹(M,M) − finrank (im δ_M)`,

the codimension of the orbit's tangent space `B¹ = im δ_M` inside the ambient tangent space
`C¹ = cochain1 d d`. By rank–nullity this equals `finrank (deformationExt1 M M)` (the cokernel
`coker δ_M = C¹ ⧸ im δ_M`), so it is the *algebraic* `Ext¹`-dimension already computed in
`DeformationExt`.

**Name = content — this is NOT the geometric codimension.** `orbitLinearCodim` is the dimension of
`C¹ ⧸ B¹`: the *expected* codimension read off the linear (tangent-space) data. It **equals** the
geometric codimension `codim Ō_M` of the orbit closure **only if** the orbit is smooth and
`dim Ō_M = dim (tangent space at M)` — that the orbit tangent space is `B¹` (orbit smoothness /
the orbit-map differential is surjective onto `B¹`) and that `dim Ō = dim C¹ − dim Ext¹` (Voigt's
theorem, the orbit-dimension bridge). Those algebraic-geometry facts are **DEFERRED (Layer 2)**:
nothing here proves them. Hence no declaration is named `codim O` / `codim_orbit`; this module is
the honest **linear shadow** of Voigt's codimension formula, not Voigt's theorem.

The chain to the paper's quadratic form (Le Halleur–Rimányi Cor 3.5) is *exact* at the linear level:
`orbitLinearCodim (⊕L) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`, by composing the rank–nullity identity
with the committed headline `finrank_deformationExt1_self_eq_multSum`.
-/

namespace DLNFibre.Core

open Matrix Module

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- The **expected (tangent-space) codimension** of the orbit `O_M`: `finrank C¹ − finrank im δ_M`,
the codimension of the orbit tangent space `B¹ = im δ_M` inside the ambient tangent space
`C¹ = cochain1 d d`. **Not** the geometric `codim Ō_M`: that equality needs orbit smoothness and the
orbit-dimension bridge (Voigt), both DEFERRED (Layer 2). The linear shadow of Voigt's formula. -/
noncomputable def orbitLinearCodim {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) : ℕ :=
  finrank k (cochain1 (k := k) d d) - finrank k (LinearMap.range (deformationδ M M))

/-- **Rank–nullity.** `orbitLinearCodim M = finrank (deformationExt1 M M)`: the codimension of the
orbit tangent space `B¹ = im δ_M` in `C¹` equals the dimension of the cokernel `coker δ_M`. -/
theorem orbitLinearCodim_eq_finrank_deformationExt1 {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    orbitLinearCodim M = finrank k (deformationExt1 M M) := by
  have hcoker : finrank k (deformationExt1 M M)
      + finrank k (LinearMap.range (deformationδ M M)) = finrank k (cochain1 (k := k) d d) :=
    Submodule.finrank_quotient_add_finrank _
  rw [orbitLinearCodim]; omega

/-- **The expected-codimension multiplicity form (Le Halleur–Rimányi Cor 3.5, linear level).** For
`M = intervalDirectSum L` over a field, the expected (tangent-space) codimension is the paper's
quadratic form `Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`, `m = multiplicityArray L`. Rank–nullity chained
with the committed headline `finrank_deformationExt1_self_eq_multSum`. The geometric reading
`= codim Ō` still rests on the DEFERRED orbit-dimension bridge (Voigt). -/
theorem orbitLinearCodim_eq_multSum (L : List (Fin (N + 1) × Fin (N + 1))) :
    (orbitLinearCodim (intervalDirectSum (k := k) L) : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i (N : ℤ), ∑ j ∈ Finset.Icc u (N : ℤ),
          ∑ v ∈ Finset.Icc j (N : ℤ),
          multiplicityArray L (i - 1) (j - 1) * multiplicityArray L u v := by
  rw [orbitLinearCodim_eq_finrank_deformationExt1, finrank_deformationExt1_self_eq_multSum]

/-! ## Non-vacuity witnesses (`(2,2,2)`, `Fin 3`, over `ℚ`; Le Halleur–Rimányi Ex 4.3)

The same two Kostant partitions of the dimension vector `(2,2,2)` as in `DeformationExt`, now read
as the *expected* orbit codimension: the `(1,1)`-orbit `M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}` has
`orbitLinearCodim = 3` (the paper's codimension `C` for this orbit, under the DEFERRED geometric
reading), the zero-product locus `{A = 0} = M_{00}² ⊕ M_{12}²` has `orbitLinearCodim = 4`. -/

/-- **`(2,2,2)` `(1,1)`-orbit:** `orbitLinearCodim = 3` for `M_{00} ⊕ M_{01} ⊕ M_{12} ⊕ M_{22}`. -/
example :
    orbitLinearCodim (intervalDirectSum (k := ℚ)
        [((0 : Fin 3), (0 : Fin 3)), (0, 1), (1, 2), (2, 2)]) = 3 := by
  rw [orbitLinearCodim_eq_finrank_deformationExt1, finrank_deformationExt1_intervalDirectSum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    finrank_deformationExt1_interval]
  decide

/-- **`(2,2,2)` zero-product locus:** `orbitLinearCodim = 4` for `M_{00}² ⊕ M_{12}²` (`{A = 0}`). -/
example :
    orbitLinearCodim (intervalDirectSum (k := ℚ)
        [((0 : Fin 3), (0 : Fin 3)), (0, 0), (1, 2), (1, 2)]) = 4 := by
  rw [orbitLinearCodim_eq_finrank_deformationExt1, finrank_deformationExt1_intervalDirectSum]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    finrank_deformationExt1_interval]
  decide

end DLNFibre.Core
