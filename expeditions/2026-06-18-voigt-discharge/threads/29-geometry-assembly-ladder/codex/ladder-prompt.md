<task>
I am building a dependency-resolved Lean 4 / Mathlib (v4.29 pin) proof ladder to discharge a single
algebraic-geometry hypothesis. Help me (a) decide the cleanest lemma factoring for one entangled
step, and (b) size one hard step honestly. This is a DESIGN review: I want your independent read on
the factoring and the sizing, NOT confirmation of a plan I will give you (I am deliberately not
stating my tentative answer).

## The setup (exact-algebra, all over an algebraically closed field k = IsAlgClosed)

Fix a dimension vector d : Fin (N+1) → ℕ. Rep_d = ∏_{i:Fin N} Matrix (Fin d(i+1)) (Fin d(i)) k
(composable matrix tuples; the equioriented type-A quiver). The group G_d = ∏_v GL_{d_v} acts by
base change: (P • A)_i = P_{i+1} · A_i · P_i⁻¹. Fix a tuple M.

Flatten Rep_d to coordinates (RepCoord d → k), one variable per matrix entry; R := MvPolynomial
(RepCoord d) k. The orbit O_M ⊆ (RepCoord d → k) is the image of the orbit map μ_M : G_d → RepCoord,
P ↦ flatten(P•M). Z_M := the orbit closure (cut out as a determinantal rank locus; that the closure
EQUALS the rank locus is a SEPARATE sub-ladder "L6", not part of this question — assume the IDEAL
equality vanishingIdeal(Z_M) = vanishingIdeal(O_M) is delivered by L6).

GOAL hypothesis to discharge:
  codimRep(orbitRankLocus M) = orbitLinearCodim M
where codimRep Z := Ideal.height (vanishingIdeal (Z)) [the geometric codimension], and
orbitLinearCodim M := finrank C¹ − finrank(range δ⁰), an already-PROVED tangent-space quantity.

The deformation complex (Ringel/Voigt), all PROVED in Lean already:
  C⁰ = ∏_v Matrix(d_v, d_v) k ;  C¹ = ∏_i Matrix(d_{i+1}, d_i) k ;
  δ⁰ = deformationδ : C⁰ → C¹,  δ⁰(φ)_i = φ_{i+1}·M_i − M_i·φ_i  (k-linear).
  orbitLinearCodim M = finrank C¹ − finrank(range δ⁰) = finrank(coker δ⁰) = finrank Ext¹(M,M).

## The intended assembly chain (each `=[Lk]` is one ladder step)

codimRep(orbitRankLocus M)
 =[L0]  Nat.card(RepCoord) − varietyDim(Z_M)          -- catenary: height + dim = ambient  [LANDED]
 =[L4d] Nat.card(RepCoord) − ringKrullDim(AtPrime m_M) -- equidim at a closed pt of a domain [LANDED]
 =[M3, needs L3] Nat.card − finrank κ(m_M)(cotangent of AtPrime m_M)  -- smooth⟹regular [LANDED, needs IsSmoothAt]
 =[L2a] Nat.card − finrank_k(ker Jacobian of vanishingIdeal-generators at M)  -- Zariski tangent = ker Jac [LANDED]
 =[L2b] Nat.card − finrank_k(range δ⁰)                -- ??? THE STEP IN QUESTION
 = finrank C¹ − finrank(range δ⁰) = orbitLinearCodim M  -- since Nat.card(RepCoord) = finrank C¹ [easy]

## LANDED bricks (all sorry-free in Lean already), with exact content:

- L0: for prime vanishingIdeal Z, height(vanishingIdeal Z) + varietyDim(Z) = Nat.card(RepCoord),
  varietyDim Z := ringKrullDim(R / vanishingIdeal Z). [additive, ℕ∞]
- L4d: for A = R/I a finite-type DOMAIN over a field and m maximal,
  ringKrullDim(Localization.AtPrime m) = ringKrullDim A = height m  [equidimensionality at closed pt].
- M3 (smooth_point_isRegularLocalRing + finrank_cotangentSpace_eq_of_isSmoothAt): for A finite-type
  over alg-closed k, m maximal with [IsSmoothAt k m] (= FormallySmooth k (AtPrime m)) and
  ringKrullDim(AtPrime m)=n, then finrank κ(m)(CotangentSpace(AtPrime m)) = n. [needs IsSmoothAt]
- L2a (finrank_cotangentSpace_eq_finrank_ker_jacobian): for R = MvPolynomial σ k, generators
  g : Fin m → R, a k-RATIONAL point a of V(I) (eval a (g i)=0), with maxIdealAt = ker(augmentation
  ε:A→k), one has finrank_k(CotangentSpace(AtPrime maxIdealAt)) = finrank_k(ker Jacobian g a), where
  Jacobian_{i,x} = eval a (pderiv x (g i)). The residue field κ = k (rational point). [LANDED, general]
- L1 (isPrime_vanishingIdeal_orbitSet): vanishingIdeal(O_M) is PRIME — O_M = range μ_M, and
  vanishingIdeal(range μ_M) = ker(μ_M^* : R → 𝒪(G_d)=Localization.Away Δ), a kernel into a domain. [LANDED]
- Mathlib: `Algebra.FormallySmooth.of_equiv` (transfer smoothness across an AlgEquiv);
  scheme-side `Scheme.Hom.dense_smoothLocus_of_perfectField` (generic point smooth, dense smooth
  locus over a perfect field — but only SCHEME-side; no ring-side generic-smoothness lemma at v4.29).
  Precedent `smooth_of_grpObj_of_isAlgClosed` proves a reduced loc-finite-type GROUP scheme over
  alg-closed k is smooth, by: pick a smooth closed pt from dense smooth locus, then translate it to
  any other closed point by group multiplication (mulRight), so smooth locus = everything.

## QUESTION A — the L2b factoring (the entanglement)

L2b must connect finrank_k(ker Jacobian) [delivered by L2a, applied to the vanishingIdeal generators
at the point M] to finrank_k(range δ⁰) [the deformation coboundary].

Observations I am confident about:
 - range(δ⁰) ⊆ ker(Jacobian) is the EASY inclusion: O_M ⊆ Z_M, so the orbit tangent (image of the
   orbit-map differential dμ_M at the identity) lies in the Zariski tangent (ker of the defining
   Jacobian). And dμ_M = δ⁰ as linear maps (the orbit-map linearization φ ↦ φ·M − M·φ blockwise).
 - The reverse inclusion / dimension equality does NOT follow from linear algebra alone — it must
   route through smoothness + dim O_M = varietyDim Z_M (the orbit is dense in its closure, both have
   the same dimension; smoothness makes Zariski tangent dim = local dim).

The factoring decision: there are (at least) two ways to organize L2b.
 (Option 1) Prove L2b "standalone": finrank(ker Jacobian at M) = finrank(range δ⁰) as a direct
   equality, by exhibiting an explicit iso ker(Jac) ≅ range(δ⁰), OR by a dimension count that
   re-imports the smoothness/dimension facts internally.
 (Option 2) Do NOT prove L2b as a standalone equality at all. Instead let the assembly chain itself
   deliver it: the chain proves Nat.card − finrank(ker Jac) = codimRep, and SEPARATELY one shows
   finrank(range δ⁰) = dim O_M = varietyDim(Z_M) [via L0/L4d on the orbit], so the two sides match
   by transitivity through varietyDim, never proving ker(Jac)=range(δ⁰) directly.

Which factoring is cleaner / lower-risk to formalize, and WHY? In particular: does the
"dim O_M = varietyDim Z_M" fact (closure of O_M, equal dimension of a dense orbit) belong as a
separate named lemma, or does it fall out of the chain for free? Is the easy inclusion
range δ⁰ ⊆ ker Jac actually NEEDED anywhere, or is it a red herring once you route through dimensions?
Be concrete about which other landed bricks each option consumes and where the residual obligation
lands.

## QUESTION B — the L3 sizing (IsSmoothAt m_M via homogeneity)

L3 must produce the instance [IsSmoothAt k m_M] for A = R / vanishingIdeal(Z_M) at the maximal ideal
m_M = (the point M). The plan is a homogeneity argument:
 (i)   a smooth closed point of Spec A exists (generic smoothness over a perfect field — but Mathlib
       only has this SCHEME-side, via dense_smoothLocus_of_perfectField; need a Spec detour + transport
       back to ring-side IsSmoothAt via StructureSheaf.stalkIso / AtPrime ≃ stalk);
 (ii)  the smooth locus is G_d-stable: each P ∈ G_d(k) gives a k-algebra automorphism α_P of A with
       α_P(m_{P•M}) = m_M, and FormallySmooth.of_equiv transfers smoothness;
 (iii) G_d acts transitively on O_M (LANDED: rankPattern_eq_iff_orbit);
 (iv)  the witnessed smooth closed point lies in O_M (smooth locus open+dense ∩ open orbit open+dense
       in irreducible Z_M is nonempty), so transitivity moves smoothness to M.

The Mathlib precedent smooth_of_grpObj_of_isAlgClosed does EXACTLY this homogeneity argument, but for
a GROUP scheme (translation = group mulRight). Our Z_M is NOT a group — it is a homogeneous space /
orbit closure under an EXTERNAL group action G_d. So the precedent cannot be invoked directly.

Size this honestly:
 - Can the precedent's argument be REUSED (is there a Mathlib homogeneous-space / group-action-on-
   scheme smoothness-transfer, or a clean way to package the G_d-action as scheme automorphisms so
   the same `nonempty_inter_closedPoints` + translate machinery applies)? Or must it be re-derived?
 - Which sub-step is most likely to break, and why? I have flagged a CAUTION: openness of the smooth
   locus gives generalization-stability, not specialization — so step (i) yields a smooth closed pt
   SOMEWHERE in Spec A, and step (iv) is what must move it INTO O_M. Is that caution well-placed, or
   is there a subtler gap (e.g. a smooth closed point of Z_M that is NOT in the open orbit, if Z_M's
   smooth locus met the boundary)? Does the irreducibility of Z_M (LANDED via L1) plus "open orbit is
   dense" actually force the witnessed smooth point into O_M, or is more needed?
 - Is the ring-side vs scheme-side detour for step (i) avoidable? Is there a purely ring-theoretic
   route to "some maximal ideal is in the smooth locus" given finite-type + reduced + the field
   perfect, at the v4.29 pin?
 - Estimate module count and name the single hardest sub-lemma.

<output_contract>
Respond in this structure, terse and concrete:

## A. L2b factoring
- VERDICT: Option 1 / Option 2 / a third framing (name it).
- WHY (2–4 sentences, the load-bearing reason).
- dim O_M = varietyDim Z_M: separate lemma | falls out | not needed — and the reason.
- range δ⁰ ⊆ ker Jac: needed | red herring — and where it is (or isn't) consumed.
- Per-option: which landed bricks consumed; where the residual obligation lands.

## B. L3 sizing
- REUSE precedent: yes (how) | no (why re-derive).
- The Spec detour for (i): necessary | avoidable (how).
- Most-likely-to-break sub-step + the precise reason.
- Is the (iv) "smooth point ∈ open orbit" step sound given irreducibility + dense open orbit? State
  the exact additional fact needed if any.
- Module-count estimate + the single hardest sub-lemma.

## C. Cross-cutting
- Any ORDERING constraint between L2b/L3/L1/L4d/L0 I may have gotten wrong.
- Any hidden hypothesis (rationality κ(m_M)=k; M maximal; reducedness of A; need for L6 BEFORE L3).
- The one thing in this plan you are most suspicious of.
</output_contract>

<grounding_rules>
Distinguish what you KNOW about Mathlib v4.29 API from what you INFER. If you assert a Mathlib lemma
exists, mark it (KNOWN) or (LIKELY/INFER). Do not invent lemma names with false confidence. If a step
is genuinely a research-grade open question rather than a formalization-effort question, say so.
</grounding_rules>
</task>
