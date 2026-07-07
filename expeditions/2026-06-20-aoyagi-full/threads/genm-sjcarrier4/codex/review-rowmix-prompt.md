<task>
You are reviewing a Lean 4 (Mathlib) formalisation brick, adversarially, for a DIFFERENT reviewer thread
than the one that designed it (decorrelated second opinion). Judge ONE question precisely: is the
"support-faithful row-mix" theorem below a GENUINE mathematical advance over the previously-banked
`frobSq`-level identity, or is it a restatement so coarse/circular that its hypothesis silently contains
the entire difficulty?

Context. In this project's `(S,J)` resolution of a real-log-canonical-threshold problem, a "generator"
`bᵢ(u,x) = (monomial prefix in exceptional divisors u) · (linear residual in active variables x)`. The
OLD banked fact (previous tide) was purely at the sum-of-squares level:

```
theorem corankStep_prefactor (pref u : ℝ) (A : Matrix t t ℝ) (B : Matrix t b ℝ) (C : Matrix a t ℝ)
    (D : Matrix a b ℝ) [Invertible A] (Q : Matrix (t ⊕ b) n ℝ) :
    pref * frobSq ((u • fromBlocks A B C D) * Q)
      = (pref * u ^ 2) * (frobSq (A * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id))
          + frobSq (C * (Q.submatrix Sum.inl id + ⅟A * B * Q.submatrix Sum.inr id)
              + schurCompl A B C D * Q.submatrix Sum.inr id))
```

This tracks only `∑ᵢ bᵢ²`, an aggregate — it CANNOT certify which individual generators bᵢ share a
common exceptional-divisor factor (needed downstream to build the exact monomial Jacobian of a blow-up
chart). The new module adds an explicit per-generator carrier and this theorem:

```
structure SJLinGenState (ζ ν ι : Type*) (d : ℕ) where
  supp  : SJSupport ι d                    -- SJSupport ι d := ι → Fin d → ℕ (monomial-exponent row per generator)
  coeff : ζ → ι → ν → ℝ

def residual (G : SJLinGenState ζ ν ι d) (z : ζ) (x : ν → ℝ) (i : ι) : ℝ :=
  ∑ v, G.coeff z i v * x v

def genMonomial (e : SJSupport ι d) (i : ι) (u : Fin d → ℝ) : ℝ := ∏ ℓ, |u ℓ| ^ (e i ℓ)   -- from prior module

noncomputable def gen (G : SJLinGenState ζ ν ι d) (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) (i : ι) : ℝ :=
  genMonomial G.supp i u * G.residual z x i

def rowMix (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d) :
    SJLinGenState ζ ν ι' d where
  supp := s'
  coeff := fun z j v => ∑ i, R j i * G.coeff z i v

theorem gen_rowMix (R : ι' → ι → ℝ) (s' : SJSupport ι' d) (G : SJLinGenState ζ ν ι d)
    (hsh : ∀ j i, R j i ≠ 0 → ∀ ℓ, G.supp i ℓ = s' j ℓ)
    (u : Fin d → ℝ) (z : ζ) (x : ν → ℝ) (j : ι') :
    (rowMix R s' G).gen u z x j = ∑ i, R j i * G.gen u z x i := by
  -- proof: unfolds `gen`, distributes `genMonomial s' j u` into the sum using `hsh` to identify
  -- `genMonomial s' j u = genMonomial G.supp i u` for every `i` with `R j i ≠ 0` (the `R j i = 0` terms
  -- vanish either way). Uses `genMonomial_congr_supp : (∀ ℓ, e i ℓ = e' i' ℓ) → genMonomial e i u = genMonomial e' i' u`.
  sorry -- (elided; the actual proof is a Finset.sum_congr + by_cases R j i = 0 case split, ~10 lines)

theorem sharedDivisorExp_rowMix_const [Nonempty ι] [Nonempty ι'] [Fintype ι']
    (R : ι' → ι → ℝ) (s : Fin d → ℕ) (G : SJLinGenState ζ ν ι d) (hconst : ∀ i, G.supp i = s)
    (ℓ : Fin d) :
    sharedDivisorExp (rowMix R (fun _ => s) G).supp ℓ = sharedDivisorExp G.supp ℓ := by
  -- proof is: sharedDivisorExp (rowMix ...).supp = sharedDivisorExp (fun _ => s) = s ℓ  [by sharedDivisorExp_const, since (rowMix R (fun _ => s) G).supp is DEFINITIONALLY (fun _ => s)]
  --           sharedDivisorExp G.supp = s ℓ  [by sharedDivisorExp_const hconst]
  -- i.e. it does NOT inspect R at all.
  sorry
```

Note `rowMix`'s `supp` field is a caller-SUPPLIED target `s'` (a bare structure field assignment), not
something computed FROM `G`'s actual generators post-mix by inspecting `R`/`G.coeff`. The theorem
`gen_rowMix` proves that IF the caller's chosen `(R, s')` satisfies the side-condition `hsh` (every
nonzero-weight source generator `i` in row `j`'s combination already has support ROW equal to the
declared target `s' j`), THEN the mixed generator equals the R-weighted sum of the old generators
(monomial factors out of the linear combination). No theorem in this module connects `rowMix`'s abstract
`R`/`s'` to the CONCRETE Step-3 block-elimination matrices (`invSchurLeft`, `invSchurRight`, a Schur
complement) from a sibling module — that instantiation is deferred to future work ("the recursion").

<questions>
1. Strip away the "generator-level" framing: is `gen_rowMix`'s proof content, once `hsh` is granted,
   anything beyond "if you factor a single scalar (a monomial value that's asserted, not computed, to
   be the SAME for every active term in a sum) out of a linear combination, you get the same linear
   combination with that scalar distributed back in" — i.e. is the hard content ENTIRELY inside the
   hypothesis `hsh`, making the theorem itself a near-tautological packaging (`mul_sum` distributivity)
   once `hsh` holds?
2. Is `hsh`'s hardness commensurate with what a REAL support-faithful block-elimination needs to
   establish? Concretely: to apply this at the real Step-3 unit-triangular block factors
   (`invSchurLeft`/`invSchurRight`, which have arbitrary nonzero off-diagonal entries `-A⁻¹B` /
   `-CA⁻¹`), would `hsh` typically hold, or would it typically FAIL (i.e. does a genuine block-
   elimination usually mix generators of DIFFERING support, making this lemma inapplicable to the
   real mechanism without further case-splitting the recursion has not yet built)?
3. Is `sharedDivisorExp_rowMix_const`, which literally does not read `R`, a vacuous corollary of
   `rowMix`'s definition (the caller declares the new support, so of course a "constant declared
   support" stays constant), i.e. does it prove anything beyond "if you assign a structure field to a
   constant function, reading that field gives the constant function back"?
4. Given (1)-(3), classify the brick: (a) genuine nontrivial generator-level advance over
   `corankStep_prefactor`, (b) correct but its hypothesis smuggles the real difficulty (a valid but
   low-content lemma), or (c) something in between — and say exactly where the line is.
</questions>

<output_contract>
Answer each question in 2-5 sentences, direct verdict first ("yes/no/tautological/nontrivial") then the
one-line justification. End with a single verdict line: "VERDICT: <(a)|(b)|(c)> because <one clause>".
Do not hedge with "it depends" without stating the deciding factor.
</output_contract>

<grounding_rules>
State inferences about the undisclosed `step3_blockFactor` matrices (`invSchurLeft`/`invSchurRight`) as
INFERENCE, not fact — you were given only their shape (unit-triangular, off-diagonal `-A⁻¹B`/`-CA⁻¹`),
not their full context. Do not assume the recursion module exists or has been checked; treat "future
work" claims in the prompt as the target module's own assertion, not verified fact.
</grounding_rules>
