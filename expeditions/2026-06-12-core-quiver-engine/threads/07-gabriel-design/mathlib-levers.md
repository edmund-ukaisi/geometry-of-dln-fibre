# Mathlib v4.29 levers for rungs 4c/4d (read-only recon, verified from source)

Pinned identifiers + signatures the 4c/4d teammates cite verbatim. From a read-only recon (`scripts/lean-search`
+ `rg`); no build. 11 EXISTS, 2 ABSENT (composable from primitives).

| Lever | Identifier | Signature (abridged) | File | Status |
|---|---|---|---|---|
| Complement existence | `Submodule.exists_isCompl` | `(p : Submodule K V) : ∃ q, IsCompl p q` | `LinearAlgebra/Basis/VectorSpace` | EXISTS |
| `IsCompl` | `IsCompl` | `Disjoint x y ∧ Codisjoint x y` | `Order/Disjoint` | EXISTS |
| quotient finrank | `Submodule.finrank_quotient_add_finrank` | `[Module.Finite R M] (N) : finrank (M⧸N) + finrank N = finrank M` | `…/Dimension/RankNullity` | EXISTS |
| **IsCompl finrank add** | — | derive: `finrank_quotient_add_finrank` + `Submodule.quotientEquivOfIsCompl S T h : (V⧸S)≃ₗT` + `LinearEquiv.finrank_eq` | — | **ABSENT (compose)** |
| rank·left-unit | `Matrix.rank_mul_eq_left_of_isUnit_det` | `(A : Matrix n n R)(B : Matrix m n R)(hA : IsUnit A.det) : (B*A).rank = B.rank` | `…/Matrix/Rank` | EXISTS |
| rank·right-unit | `Matrix.rank_mul_eq_right_of_isUnit_det` | `(A : Matrix m m R)(B : Matrix m n R)(hA : IsUnit A.det) : (A*B).rank = B.rank` | `…/Matrix/Rank` | EXISTS |
| rank of unit | `Matrix.rank_of_isUnit` | `[Nontrivial R](A : Matrix n n R)(h : IsUnit A) : A.rank = card n` | `…/Matrix/Rank` | EXISTS |
| rank one | `Matrix.rank_one` | `[Nontrivial R] : (1 : Matrix n n R).rank = card n` | `…/Matrix/Rank` | EXISTS |
| **blockdiag rank add** | — | **ABSENT** at this pin — PROVED locally in `IntervalModule.lean` as `rank_fromBlocks_zero_zero` (Field). Reuse it. | — | **DONE (4b)** |
| comap | `Submodule.comap` (+ `mem_comap`, `comap_mono`, `comap_comp`) | `(f : M →ₛₗ M₂)(p) : Submodule R M` | `Algebra/Module/Submodule/Map` | EXISTS |
| rank–nullity | `LinearMap.finrank_range_add_finrank_ker` | `[FiniteDimensional K V](f) : finrank (range f) + finrank (ker f) = finrank V` | `…/FiniteDimensional/Lemmas` | EXISTS |
| Matrix→Lin | `Matrix.toLin'`, `toLin'_apply`, `toLin'_mul` | `toLin' (M*N) = (toLin' M).comp (toLin' N)` | `…/Matrix/ToLin` | EXISTS |
| general basis | `Matrix.toLin`, `LinearMap.toMatrix` | base-change bridge | `…/Matrix/ToLin` | EXISTS |

**Two gaps, both composable (no missing axioms):**
1. *IsCompl finrank additivity* → `Submodule.quotientEquivOfIsCompl` + `finrank_quotient_add_finrank`.
2. *block-diagonal rank additivity* → already PROVED in 4b (`rank_fromBlocks_zero_zero`, Field); reuse.

All signatures READ-ONLY verified against the v4.29.0 source. Use verbatim in 4c/4d.
