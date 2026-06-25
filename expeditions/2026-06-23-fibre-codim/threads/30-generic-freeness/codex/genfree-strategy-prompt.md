# Codex consult — generic freeness in Lean 4 / Mathlib v4.29

I am formalising **generic freeness** (Grothendieck's lemma) in Lean 4 + Mathlib **v4.29.0**.

## Target statement

For a Noetherian **integral domain** `R` and a finitely generated `R`-module `M`, there exists a
nonzero `r ∈ R` such that the localization `M[1/r]` is **free** over `R[1/r]` (equivalently flat;
equivalently the free locus contains the dense basic open `D(r)`).

## The approach I found (and verified elaborates)

Mathlib v4.29 has `Module.FinitePresentation.exists_free_localizedModule_powers`:

> If `M` is finitely presented over `R` and `M_S` is FREE over `R_S` for some submonoid `S ⊆ R`,
> then `M_r` is free over `R_r` for some `r ∈ S`.

My move: take `S = nonZeroDivisors R`, `R_S = FractionRing R` (the fraction FIELD of the domain),
`M_S = LocalizedModule (nonZeroDivisors R) M`. Since `FractionRing R` is a **field**, EVERY module
over it is `Module.Free` (Mathlib instance, confirmed). So the hypothesis `Module.Free R_S M_S` is
discharged for free. The lemma then hands me `r ∈ nonZeroDivisors R` (hence `r ≠ 0` in a domain) with
`M_r` free over `R_r`. `Module.finitePresentation_of_finite` bridges `Module.Finite` (+Noetherian) to
`Module.FinitePresentation`.

I have elaborated all three output forms sorry-free:
1. `∃ r ≠ 0, Module.Free (Localization (.powers r)) (LocalizedModule (.powers r) M)`
2. flat form (`Module.Free ⟹ Module.Flat` instance)
3. `freeLocus` form: `∃ r ≠ 0, basicOpen r ⊆ Module.freeLocus R M` (via `basicOpen_subset_freeLocus_iff`).

## Questions (be adversarial)

1. **Soundness of the fraction-field reduction.** Is "free over the fraction field ⟹ free after
   inverting a single element" a CORRECT proof of generic freeness, or does it secretly need something
   more (e.g. is the descent from `FractionRing R = Localization at nonZeroDivisors` to `Localization
   at powers of a single r` doing real work I'm taking for granted via `exists_free_localizedModule_powers`)?
   In particular: `exists_free_localizedModule_powers` is stated for an arbitrary submonoid `S`. With
   `S = nonZeroDivisors R`, is the conclusion genuinely "free after inverting ONE element `r`", and is
   `r ∈ nonZeroDivisors R ⟹ r ≠ 0` the right nonvacuity (i.e. is `D(r)` actually dense — nonempty — so
   the statement is not vacuously about the empty locus)?

2. **The standard textbook proof is dévissage** (prime filtration `0 = M_0 ⊂ ... ⊂ M_n = M` with
   `M_i/M_{i-1} ≅ R/p_i`, then generic freeness of `R/p`). My route bypasses dévissage entirely by
   leaning on `exists_free_localizedModule_powers`. Is there a hidden gap — e.g. does
   `exists_free_localizedModule_powers` ITSELF secretly assume something that fails for a general f.g.
   module over a domain (it requires `FinitePresentation`, which I get from Noetherian; anything else)?

3. **The `Module.Free` over a field instance** — is it unconditional in Mathlib (every module over a
   `DivisionRing`/`Field` is free, including infinite-dimensional / non-finite), or does it need
   finiteness? (I confirmed `infer_instance` succeeds for an arbitrary module over a `Field`.)

4. **Downstream use.** The next rung needs: "on a dense open of the base, the chart map is flat, so
   going-down holds there and the relative-fibre-dimension formula `dim(fibre) = dim S − dim R`
   applies." Which of my three output forms (free / flat / freeLocus-dense) is the RIGHT interface to
   hand a relative-fibre-dimension rung that will combine flatness on `D(r)` with the LANDED
   going-down height-additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` and
   `Algebra.HasGoingDown.of_flat`? Is there a subtlety in moving from "module flat" to "ALGEBRA flat /
   ring map flat" (the going-down lemma wants `Algebra.HasGoingDown`, which is a property of a ring
   homomorphism, not a module)?

5. Any v4.29-specific naming/instance pitfalls (`Localization.Away` vs `Localization (.powers r)`;
   `nonZeroDivisors` notation; `FractionRing` vs `IsFractionRing`)?

Tell me if the approach is sound and minimal, or if I am fooling myself and need the full dévissage.
