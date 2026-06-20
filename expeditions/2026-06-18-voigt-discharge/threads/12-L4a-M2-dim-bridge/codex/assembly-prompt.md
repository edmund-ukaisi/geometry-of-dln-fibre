<task>
Lean 4 + Mathlib v4.29 (pinned). I am assembling the "dimension bridge" theorem M2: for `A` a
finite-type algebra over an algebraically closed field `k`, `m` a maximal ideal at which `A` is
smooth, prove
  ringKrullDim (Localization.AtPrime m) = n
where `n := Module.finrank A (Ω[A⁄k])` (the local relative dimension), computed via an ÉTALE-route
that is NON-CIRCULAR (does NOT use the cotangent = dim identity).

Already-landed bricks I will reuse (all in namespace DLNFibre.Core, sorry-free, building):
- M1 `Ideal.height_eq_under_of_etale` : for `[IsNoetherianRing R] [IsNoetherianRing S]
  [Algebra R S] [Algebra.Etale R S]` and a prime `Q : Ideal S` `[Q.IsPrime]`,
  `Q.height = (Q.under R).height`.
- L5 `height_add_ringKrullDim_quotient_eq (k) [Field k] (n) (p : Ideal (MvPolynomial (Fin n) k))
  [p.IsPrime]` : `(p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p) = n`.

Verified Mathlib v4.29 decls (exact names, exact signatures read from source):
1. `Algebra.IsSmoothAt R p` is an abbrev for `Algebra.FormallySmooth (Localization.AtPrime p) ...`
   actually `abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop := Smooth R (Localization.AtPrime p)`-ish.
2. `IsSmoothAt.exists_notMem_isStandardSmooth (R) [FinitePresentation R S] (p : Ideal S) [p.IsPrime]
   [IsSmoothAt R p] : ∃ (f : S), f ∉ p ∧ IsStandardSmooth R (Localization.Away f)`.
3. `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential [Nontrivial S] (n : ℕ)
   [IsStandardSmoothOfRelativeDimension n R S] : Module.rank S Ω[S⁄R] = n`.
4. `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth [Nontrivial S]
   [IsStandardSmooth R S] (n : ℕ) : IsStandardSmoothOfRelativeDimension n R S ↔ Module.rank S Ω[S⁄R] = n`.
5. `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n) (R S) [Algebra R S]
   [IsStandardSmoothOfRelativeDimension n R S] : ∃ g : MvPolynomial (Fin n) R →ₐ[R] S, g.Etale`
   where `g.Etale` is `RingHom.Etale (g : MvPolynomial (Fin n) R →+* S)` (no AlgHom.Etale exists;
   it coerces). `RingHom.Etale f := @Algebra.Etale _ _ _ _ f.toAlgebra`. There's
   `RingHom.etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R S`.
6. `IsLocalization.height_map_of_disjoint (M : Submonoid R) [IsLocalization M S] (p : Ideal R)
   [p.IsPrime] (h : Disjoint (M : Set R) (p : Set R)) : (p.map (algebraMap R S)).height = p.height`.
7. `IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A) [CommRing A]
   [Algebra R A] [IsLocalization.AtPrime A I] : ringKrullDim A = I.height`.
8. `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` and
   `MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton` exist for `[IsAlgClosed K] [Finite σ]`.
9. `finite_of_finite_type_of_isJacobsonRing (R S) [CommRing R] [Field S] [Algebra R S]
   [IsJacobsonRing R] [Algebra.FiniteType R S] : Module.Finite R S` (Zariski's lemma).
10. `isJacobsonRing_of_finiteType`, fields are Jacobson, `MvPolynomial (Fin n) k` is Jacobson.

The chain (my draft):
  Step A. From smoothness, get `f ∉ m`, `S := Localization.Away f`, `IsStandardSmooth k S`.
          (Need `FinitePresentation k A` from `FiniteType k A` over a field — field is Noetherian.)
  Step B. `q := m.map (algebraMap A S)`. `q` is prime (disjoint from powers f, since f∉m), and
          `ringKrullDim (AtPrime m) = ringKrullDim (AtPrime q)`? Actually I want to relate
          `(AtPrime m)` to `(AtPrime q)`. Plan: `IsLocalization.height_map_of_disjoint` on the
          powers-of-f submonoid gives `q.height = m.height`. Then
          `ringKrullDim (AtPrime m) = m.height = q.height = ringKrullDim (AtPrime q)` using decl 7
          on both. (Do I even need an explicit ring iso `(AtPrime m) ≅ (AtPrime q)`? I think
          `height_map_of_disjoint` + two applications of decl 7 suffices.)
  Step C. `n := Module.finrank S Ω[S⁄k]`. Want `rank Ω[S⁄k] = n`. `Ω[S⁄k]` is free (S standard
          smooth) of finite rank, so `Module.rank S Ω = finrank S Ω = n` as cardinals; then via
          decl 4 install `IsStandardSmoothOfRelativeDimension n k S`.
  Step D. decl 5 ⟹ `g : MvPolynomial (Fin n) k →ₐ[k] S` with `RingHom.Etale g`. Install
          `g.toRingHom.toAlgebra` as the `Algebra (MvPolynomial (Fin n) k) S` so M1 applies.
  Step E. `p := q.comap g.toRingHom = q.under (MvPolynomial (Fin n) k)`. Show `p` is MAXIMAL.
  Step F. `p` maximal ⟹ `ringKrullDim (B ⧸ p) = 0` ⟹ via L5, `p.height = n`.
  Step G. M1: `q.height = p.height = n`. Combine with Step B/7: `ringKrullDim (AtPrime m) = n`.
  Also deliver `Module.rank S Ω[S⁄k] = n` and transport `Module.rank (AtPrime m) Ω[(AtPrime m)⁄k] = n`
  (the rank-Ω side) for downstream M3.

<output_contract>
Be concrete and Lean-v4.29-specific. Address in order, briefly:

1. STEP E (the riskiest): the cleanest way in Mathlib v4.29 to prove `p := q.comap g` is MAXIMAL,
   given `q` maximal in `S`, `g : B = MvPolynomial (Fin n) k → S` étale (hence finite type), `B`
   Jacobson, `k` alg closed. Is there a direct "comap of maximal is maximal for finite-type algebra
   over a Jacobson ring" lemma? If not, give the exact fallback (e.g. via `B/p ↪ S/q`, `S/q` a field
   module-finite over `k` by Zariski decl 9, so `B/p` is a finite-type domain inside a finite
   `k`-module ⟹ Artinian domain ⟹ field ⟹ p maximal). Name the precise decls. Is `q` even maximal in
   `S = Localization.Away f`? (m maximal in A, f∉m — is the image maximal in the localization? Give the
   decl, e.g. `IsLocalization.isMaximal_of_isMaximal_disjoint` or similar.)

2. STEP B: confirm whether `IsLocalization.height_map_of_disjoint` + two `AtPrime.ringKrullDim_eq_height`
   is enough, or whether I need the explicit localization-of-localization iso. Flag the disjointness
   obligation `Disjoint (powers f) m` from `f ∉ m` (prime) — exact decl
   (`Ideal.disjoint_powers_iff_notMem`?).

3. STEP C: the cardinal/finrank bookkeeping to install `IsStandardSmoothOfRelativeDimension n k S`
   from `rank Ω = n` where `n := finrank`. `Ω` free finite ⟹ `rank = finrank` decl
   (`Module.finrank_eq_rank` / `rank_eq_finrank`?). Watch `Cardinal.lift`. Give the cleanest `n` choice
   so decl 4's `Module.rank S Ω = (n:ℕ)` holds definitionally-ish.

4. STEP D: installing `Algebra B S` from `g.toRingHom` via `algebraize`/`.toAlgebra` such that M1's
   `Algebra.Etale B S` instance + `q.under B = q.comap g` both hold. Pitfalls with two competing
   `Algebra B S` instances / `IsScalarTower`. The `RingHom.etale_algebraMap` direction needed.

5. The rank-Ω transport for M3 (`rank Ω[(AtPrime m)⁄k] = n`): the localized-module API
   (`KaehlerDifferential.isLocalizedModule_map`, `Module.lift_rank_of_isLocalizedModule_of_free`).
   Is this needed for M2's headline, or only for M3? If only M3, say so — I may defer it.

6. Any STEP that is a hidden balloon (a missing brick that turns this from ~150-250 lines into a
   sub-library). Name it and the kill-condition.
</output_contract>

<grounding_rules>
You may rely on the verified decl names/signatures I gave (I read them from source). For any decl
YOU introduce, mark it [UNVERIFIED-recall] — I will check it with rg before using. Distinguish "this
exact lemma exists" (cite the file if you can) from "a lemma of this shape should exist". Do not invent
Mathlib lemma names confidently; prefer naming the mathematical step + the likely Mathlib file/area.
</grounding_rules>
