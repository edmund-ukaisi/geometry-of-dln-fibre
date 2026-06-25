<task>
Write a COMPLETE Lean 4 + Mathlib v4.29 proof of this theorem. I have confirmed the route (adapted
bases + basis_toMatrix glue); I now need a concrete, compile-oriented proof with EXACT v4.29 names so I
can build and debug locally. Give the full proof term/tactic block, plus any helper lemmas, in order.

FROZEN THEOREM (Skeleton.lean; namespace DLNFibre.DLN.RLCT; `open Matrix LinearMap Module`):
  theorem block_elimination (H : Fin (L + 1) → ℕ) (r : ℕ)
      (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ) (hB : B.rank = r) :
      ∃ (P : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
        (Q : Matrix (Fin (H (Fin.last L))) (Fin (H (Fin.last L))) ℝ),
        IsUnit P ∧ IsUnit Q ∧
          P * B * Q = Matrix.of (fun i j => if (i:ℕ) = (j:ℕ) ∧ (i:ℕ) < r then (1:ℝ) else 0)

Abbreviate a := H 0, b := H (Fin.last L). So B : Matrix (Fin a) (Fin b) ℝ, rank r over ℝ.

CONFIRMED FACTS / API (verified present in v4.29):
- `Matrix.rank B = Module.finrank ℝ (LinearMap.range B.mulVecLin)` holds by `rfl`/defeq (so
  `finrank ℝ B.mulVecLin.range = r` is just `hB`).
- `LinearMap.finrank_range_add_finrank_ker`, `Module.finrank_pi` (finrank (Fin n → ℝ) = n).
- glue: `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix` in Matrix/Basis.lean.
- `Module.finBasisOfFinrankEq` (FiniteDimensional/Defs), `Basis.prod` (Basis/Prod.lean),
  `Basis.reindex`, `Pi.basisFun`, `LinearMap.quotKerEquivRange`.
- `Submodule.exists_isCompl`, `Submodule.prodEquivOfIsCompl` exist but I have NOT pinned exact
  signatures — please give the exact names you rely on and flag any you're unsure of.
- `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n)`, `finCongr`.

KEY HAZARD: I need P*B*Q to equal EXACTLY `Matrix.of (fun i j => if (i:ℕ)=(j:ℕ) ∧ (i:ℕ)<r then 1 else 0)`,
the rectangular a×b rank block. The adapted bases live on `Fin r ⊕ Fin (a-r)` and `Fin r ⊕ Fin (b-r)`;
the reindex along `finSumFinEquiv.trans (finCongr ...)` must land on this exact Fin-indexed `if`.
</task>

<output_contract>
Give, in build order:
1. Helper lemma: rank-nullity giving `finrank ker = b - r` and `r ≤ b`, `r ≤ a` (exact lemmas).
2. The adapted DOMAIN basis on `Fin r ⊕ Fin (b-r)` (ker-complement first r, ker last) and adapted
   CODOMAIN basis on `Fin r ⊕ Fin (a-r)` (range first r, complement last). Exact constructions.
3. The sum-indexed normal form: `LinearMap.toMatrix bDomΣ bCodΣ B.mulVecLin (Sum.inl i) (Sum.inl j) = ...`
   — the proof that it's the block-identity on the inl/inl corner, 0 else. THIS is the crux; give it in
   full (it needs: codomain basis's first r vectors ARE f(domain's first r), so toMatrix entry = δ).
4. The reindex to Fin a / Fin b and the exact-RHS match (the `if (i:ℕ)=(j:ℕ) ∧ (i:ℕ)<r` shape).
5. P, Q from `Basis.toMatrix` vs `Pi.basisFun`, IsUnit via `Basis.invertibleToMatrix`/`isUnit_of_invertible`,
   and `LinearMap.toMatrix (Pi.basisFun..) (Pi.basisFun..) B.mulVecLin = B` (exact lemma name).
6. Flag EVERY lemma name you are not certain exists in v4.29 — I will rg-verify before building.
</output_contract>

<grounding_rules>
Concrete code is fine here (I WILL build it, not paste blindly). But mark any uncertain API name with
[?] so I verify it first. Prefer fewer, robust steps. If a sub-step is genuinely ~50 lines, say so.
</grounding_rules>
