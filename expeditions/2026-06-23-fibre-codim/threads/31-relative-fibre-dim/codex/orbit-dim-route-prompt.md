<task>
Adjudicate, as an independent algebraic geometer / commutative algebraist, whether a SPECIFIC Lean-4 +
Mathlib (pin v4.29) formalization route reaches a target dimension identity through ALREADY-FORMALIZED
machinery, OR whether it inescapably needs a Mathlib-absent theorem. Give a sharp verdict and name the
exact absent theorem if there is one. Do NOT rubber-stamp; argue from the algebra.
</task>

<context>
We have a finite-type affine setup over an algebraically closed field k of characteristic 0. Two relevant
loci live in the affine space Rep_d = ⊕ Mat (composable matrix tuples, "deep linear network reps"):

- mult : Rep_d → Mat_{m×n} (m = d_N, n = d_0) is the iterated matrix product A_N···A_1 (a polynomial map).
- Σ^r := mult⁻¹(Mat^{=r})   — the EXACT-rank-r locus (preimage of rank-EXACTLY-r matrices).
- F := mult⁻¹(E)            — the fibre over a fixed rank-r normal form E. F is REDUCIBLE in general
  (worked anchor: d = (3,3,3), r = 1 gives F with irreducible components of dims 10, 9, 9 — NOT
  equidimensional, NOT irreducible).
- δ := r(d_N + d_0 − r) = dim Mat^{=r} (the rank-r matrix stratum dimension).

TARGET IDENTITY (called hSweep):
    varietyDim Σ^r = δ + varietyDim F
where varietyDim Z := Krull dim of the SET-LEVEL coordinate ring O(Z) = MvPolynomial(coords) / I(Z),
I(Z) = vanishingIdeal Z (radical by construction). So varietyDim is the dimension of the Zariski CLOSURE
of Z as a reduced affine set; it equals max over irreducible components.

The MATHEMATICS of hSweep is already certified by an independent pen-and-paper argument + Monte-Carlo:
H = GL_{d_N} × GL_{d_0} acts on Rep_d through the two END vertices (inner units telescope away in mult),
mult is H-equivariant: mult(P·A) = P_N · mult(A) · P_0⁻¹. Mat^{=r} is a SINGLE H-orbit (any two rank-r
matrices are GL×GL-equivalent). Hence Σ^r = H·F = ⋃_{h∈H} h·F (a homogeneous sweep). The action map
α : H × F → Σ^r, (h,f) ↦ h·f is surjective with fibres = Stab-cosets of uniform dimension dim H − δ
(homogeneity, NO flatness needed), giving dim Σ^r = dim H + dim F − (dim H − δ) = δ + dim F. We are NOT
asking you to re-verify this math. We are asking about LEAN REACHABILITY.

WHAT IS ALREADY FORMALIZED IN THE ENGINE (verified to exist, green builds):
(A) An ORBIT-DIMENSION method for a DIFFERENT object. For a quiver representation M, the orbit-closure
    Z_M = closure(G_d · M) (G_d = full base-change group ∏ GL_{d_i}) is IRREDUCIBLE, and:
       varietyDim Z_M = ringKrullDim((μ_M*).range),  where μ_M* : O(Rep_d) → O(G_d) is the comorphism
    of the orbit map μ_M : G_d → Rep_d, g ↦ g·M. CRUCIALLY (μ_M*).range is a SUBALGEBRA of O(G_d) =
    Localization.Away(Δ) of MvPolynomial, which is a DOMAIN. So Z_M irreducible ⟹ O(Z_M) ≅ (μ_M*).range
    is a DOMAIN, and then ringKrullDim = trdeg (finite-type domain over a field, Mathlib has this).
    The whole trdeg machinery (trdeg ≤ generic differential rank, char-0 Jacobi-Zariski criterion) is
    formalized for this DOMAIN case (JacobianTrdeg.lean).
(B) varietyDim Mat^{=r} = δ (the base stratum dim) is formalized.
(C) The sweep SET identity Σ^r = ⋃_P (P·)''F is formalized (set-level).
(D) The codim-CONSTANCY of all rank-r fibres (G1: same rank ⟹ same fibre codim) is formalized.

THE KEY STRUCTURAL ASYMMETRY: the orbit-dim method (A) computes the dimension of an IRREDUCIBLE
orbit-closure Z_M, by pulling back through ONE orbit map μ_M into the DOMAIN O(G_d). But Σ^r is the
H-sweep of the REDUCIBLE F. The analogous "action pullback" α* : O(Σ^r) → O(H × F) lands in
O(H) ⊗_k O(F), and O(F) is NOT a domain (F reducible). So α* does not land in a domain; trdeg(range α*)
is not obviously additive.

Mathlib v4.29 facts (verified): trdeg-of-tensor-product ABSENT; ringKrullDim(A ⊗_k B) = dim A + dim B
ABSENT; relative ringKrullDim additivity for reducible quotients is a `proof_wanted` TODO
(MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing, KrullDimension/Basic.lean); Noether
normalization is FIELD-base only (no relative Noether normalization over a domain); no abstract
homogeneous-space / principal-bundle dimension package; trdeg_add_eq (Stacks 030H tower additivity)
needs the TOP ring NoZeroDivisors (= a DOMAIN = irreducible). Already ruled out (do NOT propose):
Jacobian-rank route (circular), flatness-at-E (circular), general trdeg-additivity for reducible
varieties (the Mathlib proof_wanted, and it is mathematically valid only with caveats).
</context>

<questions>
1. Can the orbit-dimension method (A) — designed for the IRREDUCIBLE single-orbit-closure Z_M, pulling
   back into the DOMAIN O(G_d) — be repurposed to compute varietyDim Σ^r via the action map α : H×F → Σ^r?
   Σ^r is the image of α. Does varietyDim Σ^r = trdeg(range α*) hold, and is range α* a domain? (Σ^r is
   itself REDUCIBLE — it is the closure of the H-sweep of reducible F. Is it?)
2. Is the additive split varietyDim Σ^r = δ + varietyDim F obtainable from trdeg additivity / the orbit
   structure WITHOUT one of: (a) a determinantal-ideal-generation theorem, (b) a reducible-component /
   minimal-prime correspondence, (c) a product iso O(Σ^r) ≅ O(base) ⊗ O(F), (d) a general
   relative/fibre-dimension theorem (uniform fibre dimension of a dominant morphism)? Which is unavoidable?
3. DECISIVE QUESTION — is the orbit-dimension route GENUINELY DIFFERENT in its Mathlib-absent dependency
   from a "chart-trivialization / product-iso" route (which is known to need a determinantal-ideal
   theorem + a reducible-component correspondence)? Or does the orbit-dim route SECRETLY need the SAME
   absent machinery, just hidden inside the "uniform fibre dimension of α" or the "trdeg of range α*"
   step? Be adversarial. Specifically: the certified math gives uniform fibre dim of α via HOMOGENEITY
   (Stab-cosets) — but does turning "uniform fibre dim ⟹ dim image = dim source − fibre dim" into Lean,
   for a REDUCIBLE image/source, require a relative-dimension / Chevalley fibre-dimension theorem that is
   Mathlib-absent? Is the uniform-fibre-dim step a domain statement or does the reducibility of F leak in?
4. Is there a way to AVOID the reducibility problem: e.g., does it suffice to take ONE top-dimensional
   irreducible component F_0 of F (dim F_0 = dim F), form H·F_0 (irreducible, since H connected × F_0
   irreducible), show varietyDim Σ^r = varietyDim(closure H·F_0) (because Σ^r = ⋃_i H·F_i and dim = max),
   and compute dim(closure H·F_0) by the orbit-dim/single-orbit method on the IRREDUCIBLE H·F_0? Does
   THAT reduce hSweep to the irreducible case the engine already handles — and what is then the residual
   Mathlib-absent step (identifying dim(closure H·F_0) = δ + dim F_0, i.e. dim of an irreducible orbit
   image)? Would the single-orbit-image dimension formula dim(G·x closure) = dim G − dim Stab apply, and
   is THAT in Mathlib?
</questions>

<output_contract>
- A one-line VERDICT: either "ORBIT-DIM ROUTE REACHES hSweep through landed machinery (no new
  Mathlib-absent theorem)" with the lemma chain, OR "ORBIT-DIM ROUTE ALSO WALLED: it needs Mathlib-absent
  theorem X = [precise statement]", and whether X coincides with the chart-route's absent theorems.
- For Q4 specifically: say clearly whether reducing to ONE irreducible component F_0 + H·F_0 dodges the
  reducibility wall, and what the residual absent theorem is THEN (be precise: is it "dim of orbit image
  = dim G − dim stabilizer", or "dim of a constructible/locally-closed image", or a fibre-dimension
  theorem — and is that in Mathlib v4.29?).
- Distinguish FACT (you are sure) from INFERENCE (your best read). Name Mathlib lemmas by name when you
  assert presence/absence; flag where you are guessing about v4.29 contents.
- An honest module-count estimate for any residual sub-library.
</output_contract>

<grounding_rules>
- Reason from the commutative algebra, not from authority. The asymmetry domain-vs-reducible is the crux:
  test whether it can be dodged or whether it is fatal.
- Do not paste Lean code you have not type-checked; describe lemma shapes and name Mathlib lemmas.
- If you believe the route works, give the explicit chain with each step labelled LANDED / Mathlib-present
  (named) / Mathlib-absent. If walled, name the single tightest absent theorem.
</grounding_rules>
