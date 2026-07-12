<task>
A Lean-formalised loop invariant for an induction on chain arity. Judge whether a specific committed
clause is preservable by the inductive step, or is satisfiable only at the base. Logic/structure only.

## Setup
Chains `M` of matrices `A_0,…,A_{k-1}` (`A_s : M_s×M_{s+1}`); the "product" `prod(M) = A_0·A_1···A_{k-1}`
(an `M_0×M_last` matrix, MULTILINEAR in the parameters). A "decoration" `D` on `M` has a deeper
parameter space `D.Z` and residual linear forms `res_i(z)` (`z ∈ D.Z`). A separately-required clause
`genuineCarrier` PINS: `D.Z ≃ᵐ Params(M)` (the full parameter tuple of ALL of `M`'s matrices) and the
residuals read the product entries: `res_i(z) = prod(M)(z)_{entry(i)}`.

The invariant `adm` is preserved DOWN an arity recursion: from `adm` at arity `k` the step must
establish `adm` at arity `k−1` (a shorter chain, still ≥ 2 matrices at intermediate levels; the BASE
is arity 1 = a single matrix). The clause under audit (the `d ≥ 1` branch) asserts:

    ∃ (a n Dt : ℕ) (Z : Matrix (Fin n) (Fin Dt) ℝ) (c > 0)
      (eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ))          -- a measure-iso of D.Z onto a SINGLE free block Γ = eΓ z
      (ρ : D.ι ≃ (Fin a × Fin Dt)),
      Z·Zᵀ ≽ c·I  ∧  D.dom = eΓ⁻¹(box)  ∧  minAdm(M) ≤ a·n  ∧
      ∀ z i,  res_i(z) = (Γ(z)·Z)_{ρ(i)}           -- Γ = eΓ z varies with z; Z is a SINGLE FIXED matrix

I.e. the residual matrix equals `Γ(z)·Z` with `Γ(z)` a free block ranging over `D.Z` and `Z` a FIXED
constant matrix.

## Facts
- At the BASE (arity 1): `prod(M)` is a SINGLE matrix `A_0` (`M_0×M_1`), `Params(M) ≃` that matrix.
- At an INTERMEDIATE arity (≥ 2 matrices): `prod(M) = A_0·A_1···` is a genuine product of ≥2 matrices,
  MULTILINEAR in the parameters (e.g. two factors: `prod = B·C`, `B,C` both free/varying).
- `genuineCarrier` (always required) forces `res_i(z) = prod(M)(z)_{entry(i)}` and `D.Z ≃ Params(M)`.

<questions>
State FACT vs JUDGEMENT.
1. At an intermediate arity where `prod(M) = B·C` (two free matrix factors, both varying over `D.Z`),
   can the clause hold — i.e. can there exist a SINGLE FIXED matrix `Z` and a measure-iso
   `eΓ : D.Z ≃ (single block Γ)` with `res_i(z) = (Γ(z)·Z)_{ρ(i)} = prod(M)(z)_{entry(i)} = (B(z)·C(z))_{entry}`
   for all `z`? Consider: (a) `Γ(z)·Z` is LINEAR in `Γ(z)` with `Z` fixed, whereas `B·C` is BILINEAR in
   `(B,C)`; (b) `eΓ : D.Z ≃ (single a×n block)` identifies ALL of `D.Z` with one free block, but `D.Z ≃
   Params(M)` contains BOTH `B` and `C` (two matrices' worth of parameters). Is the clause satisfiable
   there, or not?
2. At the BASE (arity 1, `prod = A_0` a single matrix), is the clause satisfiable (e.g. `Γ = A_0`,
   `Z = I`, `Dt = n`)? 
3. If the clause is satisfiable at the base but not at intermediate arities, what does that imply for
   an arity-DOWN induction that must carry `adm` at every intermediate level to reach the base — can
   the step preserve it? What is the minimal generalization of the clause that IS satisfiable at all
   arities (hint: what must `Z` depend on, and must `D.Z` split as block × remainder)?
</questions>
</task>

<output_contract>
Three numbered answers, 3-6 sentences each, FACT/JUDGEMENT tagged. End with two one-liners:
"CLAUSE-AT-INTERMEDIATE:" (satisfiable | unsatisfiable, one-clause why) and "FIX:" (the minimal
generalization that is satisfiable at all arities).
</output_contract>

<grounding_rules>
Ground in the setup. A product of ≥2 free matrices is multilinear, not equal to (one free block)×(one
fixed matrix) as a function of all parameters unless one factor is constant. A measure-iso of D.Z onto
a single block forgets any additional parameters D.Z carries. Do not assume the clause works.
</grounding_rules>
