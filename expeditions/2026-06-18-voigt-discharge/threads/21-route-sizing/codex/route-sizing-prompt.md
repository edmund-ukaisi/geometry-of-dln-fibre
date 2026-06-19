<task>
Lean 4 + Mathlib (pinned at v4.29.0, late-2025 toolchain) sizing question for a formalisation project.

SETTING. We want, for a fixed type-A (equioriented A_{N+1}) quiver representation `M` (a tuple of
composable matrices), to prove in Lean that the orbit `O_M` under the product group
`G = ∏ GL(d_i)` has variety dimension equal to `finrank(range δ⁰)`, where `δ⁰` is the
differential of the orbit map (a known linear map; `range δ⁰` = coboundaries, `ker δ⁰ = Hom(M,M) = End(M)`).
Equivalently `dim O_M = dim G − dim Stab(M)`. The orbit closure `Ō_M` is the rank-locus `Z_M`
(rank conditions on the partial matrix products A_j···A_i ≤ those of M).

We have ALREADY LANDED, as reusable Lean (network-free commutative-algebra `Core` modules), the following
bedrock, all green and axiom-clean:
- A point-set→PrimeSpectrum Nullstellensatz codim bridge: `codimRep Z = #vars − varietyDim Z` for an
  irreducible closed Z over an algebraically closed field.
- The polynomial-ring catenary/dimension formula `height p + ringKrullDim(R/p) = n` for R = k[x_1..x_n].
- An affine-domain dimension formula `height p + ringKrullDim(A/p) = ringKrullDim A` and
  local↔global `ringKrullDim(Localization.AtPrime m) = ringKrullDim A` for a finite-type domain A.
- A flat + quasi-finite ⟹ prime-height-equals-contraction lemma (going-down + 0-dim fibre).
- A "smooth point ⟹ regular local ring" lemma `smooth_point_isRegularLocalRing`: for a finite-type
  k-algebra (k perfect), m maximal, IsSmoothAt k m ⟹ IsRegularLocalRing (Localization.AtPrime m).
  And `finrank_cotangentSpace_eq_of_isSmoothAt`: at a smooth k-point, finrank(m/m²) = relative dim = n.
- A general cotangent↔Jacobian-kernel bridge `finrank_cotangentSpace_eq_finrank_ker_jacobian`: for V(I) ⊆ k^σ
  at a k-rational point, finrank(CotangentSpace(AtPrime m)) = finrank(ker Jacobian-of-generators) —
  UNCONDITIONAL (no smoothness, no radicality needed).
- O_M is Zariski-irreducible; the orbit map; vanishingIdeal(image orbit map) = ker(orbit-map pullback).
- Rank-nullity: finrank(range δ⁰) + finrank(ker δ⁰) = finrank(C⁰).

We are choosing between TWO non-circular routes to `varietyDim(Z_M) = finrank(range δ⁰)`, to pick the
SMALLER remaining Lean build:

ROUTE (a) — "determinantal / smooth-point" assembly. Via the landed bridges:
  varietyDim(Z_M) = ringKrullDim(AtPrime m_M)       [affine-domain local↔global; needs Z_M prime]
                  = finrank(cotangent at m_M)         [smooth_point_isRegularLocalRing + iff_finrank_cotangentSpace; needs M a smooth point of Z_M]
                  = finrank(ker Jacobian_M)            [landed cotangent↔Jacobian bridge]
                  = finrank(range δ⁰)                  [identify ker Jacobian of the rank-locus generators with range δ⁰]
  Remaining NEW content: (i) Z_M's vanishing ideal is prime (Z_M irreducible); (ii) M is a smooth point of
  Z_M (homogeneity: smooth locus is G-stable, dense, transitive action); (iii) ker(Jacobian of the
  rank-locus / product-minor generators at M) = range δ⁰; (iv) the rank-locus IS the orbit closure
  (degeneration order). Some versions need the minors to GENERATE the radical/prime vanishing ideal
  (the equioriented type-A quiver determinantal-ideal primeness theorem — Lakshmibai–Magyar / Knutson–
  Miller–Shimozono).

ROUTE (b) — "orbit-stabiliser / fibre-dimension". `dim O_M = dim G − dim Stab(M)` where Stab(M) = Aut(M)
  is open in End(M) = ker δ⁰, so dim Stab = finrank(ker δ⁰); dim G = finrank(C⁰); rank-nullity ⟹
  dim O_M = finrank(range δ⁰); then dim Z_M = dim O_M (orbit dense in its closure). The crux is the
  orbit-stabiliser dimension identity, which over a field is an instance of Chevalley's fibre-dimension
  theorem for the orbit map G → O_M (a dominant morphism of irreducible affine varieties:
  dim(source) = dim(target) + dim(generic fibre)).
</task>

<output_contract>
Answer these precisely, each with a one-line justification grounded in what is/isn't in Mathlib at a
recent pin (cite a Stacks tag, a Mathlib declaration name, or "absent — I could not find it"):

1. Is Chevalley's FIBRE-DIMENSION theorem (dim source = dim target + dim generic fibre for a dominant
   morphism; Stacks 02FZ / 02NM / 05F6 / the "dimension of fibres" formula) available in Mathlib, in ANY
   form usable for affine varieties / finite-type domains over a field (e.g. ringKrullDim relating a
   morphism's source, target, and fibre; trdeg = ringKrullDim and additivity of trdeg)? Yes/No + the
   decl name or "absent".
2. Is there ANY algebraic-group / group-action ORBIT-DIMENSION package in Mathlib (dim orbit = dim G −
   dim stabiliser; orbit locally closed; closure preserves dimension of an irreducible)? Yes/No + names.
3. For route (b): aside from the fibre-dimension theorem itself, which of these are present vs absent —
   (b1) "units of a finite-dimensional algebra form a Zariski-open set"; (b2) "dim(Zariski-dense subset) =
   dim(ambient)" / "closure of an irreducible preserves Krull dimension"; (b3) trdeg-based dimension of a
   f.g. domain?
4. For route (a): is there any determinantal-ideal theory in Mathlib (minors of a generic matrix generate
   a prime/radical/Cohen–Macaulay ideal; variety-of-complexes; quiver-locus ideals)? Yes/No + names.
5. THE DECISION: given the landed bedrock above (especially that the smooth-point⟹regular and
   cotangent=ker-Jacobian bridges are DONE), which route is the smaller REMAINING Lean build, and by
   roughly how much? In particular: does route (a) actually need the full determinantal-ideal primeness
   theorem, or can it get Z_M-prime from "O_M irreducible (image of irreducible G) + Z_M = Ō_M", and get
   the smooth point from homogeneity — reusing the landed smooth⟹regular + cotangent=ker-Jacobian chain —
   so that the ONLY genuinely new geometric content is {Z_M = Ō_M (degeneration order), M smooth via
   homogeneity, ker(Jacobian)=range δ⁰}? Compare that against building Chevalley fibre-dimension + the
   orbit-dimension package from scratch for route (b).
6. Sharpest risk: name the single hardest remaining lemma in your recommended route and what would make
   it balloon.
</output_contract>

<grounding_rules>
- Distinguish "present in Mathlib (decl/Stacks tag)" from "standard math, but I'd have to build it". Do
  not assert a Mathlib declaration exists unless you can name it or a close analog; otherwise say "absent
  / I could not confirm".
- Do not assume our landed bedrock has gaps — take the listed landed lemmas as given green facts.
- Be explicit about circularity: if a step secretly needs dim O_M (the goal) to prove a sub-step, flag it.
- It is fine to conclude "both routes need a from-scratch sub-library"; if so, say which sub-library is
  smaller and why, given the reuse asymmetry.
</grounding_rules>
