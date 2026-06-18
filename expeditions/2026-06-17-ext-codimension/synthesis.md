# synthesis.md — controller's integrative read (ext-codimension)

## RECON LANDED (2026-06-17) — both threads converge, Codex-concurred

**recon-mathlib (coverage)** + **recon-ext-design (design, via Codex)** agree on the development. Math:

- **Ext/Hom between interval modules** (equioriented A_N, arrows t→t+1, M_{ij} = k on [i,j]):
  dim Hom(M_{ij},M_{uv}) = 1[u≤i≤v≤j];  dim Ext¹(M_{ij},M_{uv}) = 1[i<u≤j+1≤v]  (false when j=N).
  Via the 2-term projective resolution 0→P_{j+1}→P_i→M_{ij}→0, P_p = M_{p,N}.
- **Cor 3.5 match:** substitute i'=i+1, j'=j+1 ⟹ dim Ext¹(M,M) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}. ✓
- **Euler form** ⟨a,b⟩ = Σ_t a_t b_t − Σ_t a_t b_{t+1}; hereditary identity dim Hom − dim Ext¹ = ⟨d,d⟩.
- **Voigt (deformation complex):** C⁰ = ∏_v End(M_v) →δ C¹ = ∏_{t} Hom(M_t,M_{t+1}) = T_M Rep;
  B¹ = im δ = T_M(orbit); no relations ⟹ Z¹ = C¹; Ext¹(M,M) = C¹/im δ; so
  codim O_M = dim C¹ − dim im δ = dim Ext¹(M,M). Clean here because Rep is affine (smooth) and the
  stabiliser Aut(M) is open in End(M) (smooth) — holds in arbitrary characteristic for the UNBOUND quiver.
- **Controller cross-check (2,2,2):** (1,1) orbit M_00⊕M_01⊕M_12⊕M_22 → dim Ext¹ = 3 (00→12, 01→12,
  01→22). {A=0} = M_00²⊕M_12² → 2·2·1 = 4. So C=3, θ=1. Matches the paper.

## COVERAGE VERDICT — opposite profiles

- **Phase A (Ext algebra): reachable, and SIMPLER than the path-algebra route.** Mathlib has all GENERIC
  homological algebra (ModuleCat abelian, ProjectiveResolution, CategoryTheory.Ext, biproduct additivity)
  but nothing quiver-specific (no path algebra kQ, no Euler form). The **standard hereditary development
  is the finrank 2-term deformation/Ringel complex** Ext¹ := coker(δ: C⁰→C¹) directly on the existing
  `Tuple` encoding — pure linear algebra (LinearMap.range/ker/finrank, Submodule.Quotient). NO path
  algebra, NO ModuleCat, NO derived Ext needed for the headline dim Ext¹(M,M) = Σ m_{i-1,j-1} m_{uv}.
  Codex confirms this is textbook (Assem–Simson–Skowroński, Crawley-Boevey). The derived-Ext /
  quiver-rep-category reconciliation is a SEPARATE, deferrable bridge — not on the headline path.
  ⇒ **Deviation from Q1 ("path-algebra modules"):** the path algebra was the means; the standard
  hereditary route reaches the same Ext without it. Proceeding with the finrank route.
- **Phase B (orbit-dimension AG / Voigt): a Mathlib desert.** NO algebraic groups (no GL_n group scheme,
  no LinearAlgebraicGroup), NO orbit dimension (dim G − dim Stab), NO Zariski tangent space of a scheme.
  The finrank route proves the **algebraic** normal-space identity Ext¹(M,M) = C¹/im δ honestly. The
  **geometric** step — finrank(im δ) = dim O_M, dim closure = dim orbit, codim = dim Rep − dim orbit —
  needs orbit-locally-closed + orbit-dimension theory built essentially from scratch (a large, separate
  foundational ocean, possibly upstream-worthy).

## BIGGEST RISK (recon + Codex flagged; controller concurs)
Scope drift: proving the clean finrank normal-space theorem and naming it `codim_orbit_eq_dim_ext1`.
`voigt_normalSpace_finrank` is NOT the geometric codimension without the orbit-dim→codim bridge. Keep
that bridge an explicit named theorem/assumption. Name = content.

## PLAN (reshaped)
- **Phase A — PROCEEDING.** Finrank deformation complex on `Tuple`: C⁰, C¹, δ; Hom = ker δ; Ext¹ =
  coker δ; the Euler identity (alternating finrank); Ext-between-intervals indicators; additivity over ⊕;
  the headline dim Ext¹(M,M) = Σ m_{i-1,j-1} m_{uv}. Standard, elementary, builds on the engine.
- **Phase B — DECISION PENDING OPERATOR.** Either (A) land the algebraic Voigt identity + name the
  orbit-dim→codim geometric step as the single Cited/Assumed bridge (honest, bounded; the codim formula
  Proved-modulo-named-bridge), then scope the AG as its own programme; or (B) commit now to building
  algebraic-group + orbit-dimension AG from scratch (multi-expedition). Controller recommendation: (A).

## STATE
Recon tasks #1, #2 closed. Task #3 (this synthesis) effectively done. Backend: in-process teammates
(operator-confirmed fine). Next: spawn Phase-A formaliser(s) on the finrank deformation-complex ladder.

## ADDENDUM (recon-ext-design certificate, full) — Phase-B bridge narrows to ONE fact

The certificate (threads/02-ext-design/findings.md) confirms everything and sharpens Phase B. Key glue:
⟨d,d⟩ = dim G − dim Rep, and dim O_M = dim G − dim Aut(M) (orbit dim = dim G − dim Stab; Stab = Aut(M)
open in End(M), so dim Stab = dim End(M) = dim Hom(M,M)). Hence
  codim O_M = dim Rep − dim O_M = dim Hom(M,M) − ⟨d,d⟩ = dim Ext¹(M,M).
So **the Hom−Euler identity IS the Voigt computation** — and the *only* genuinely geometric input is the
single orbit-dimension fact **dim O_M = dim G_d − dim Aut(M)** (plus dim Ō = dim O, codim = dim Rep − dim O).
The Phase-B "AG desert" is therefore not "build all of algebraic groups" but **one named orbit-dimension
theorem**. That sharpens the operator decision: option (A) names exactly this one fact as the Cited/Assumed
bridge; option (B) builds the orbit-map fibre-dimension theorem (still needs algebraic-group-action
machinery underneath, but bounded to that target). Route (b) (dim O = dim G − dim Aut(M) + the Phase-A
Euler identity) is the realistic Lean path — it uses only Phase-A objects plus that one geometric fact.

(2,2,2) dim-O column now also confirmed (origin dim O = 0 / codim 8; (1,1) dim O = 5 / codim 3). Recon
team (recon-mathlib, recon-ext-design) stood down.

## PHASE A CLOSED (2026-06-18) — Cor 3.5 algebraic content, in honest Lean

`Core.DeformationExt` (≈1223 LoC, green / sorry-free / axiom-clean) — built from scratch on `Tuple`,
standard hereditary route (no path algebra / derived Ext needed for the headline). Commits e43b95b
(Euler layer) → 69a6835 (indicators) → 815102b (additivity + list headline + witnesses) → 0a0e64a (grid
m-form) → a327d01 (verbatim Cor 3.5 + lint).

### Statement card — Phase A
- **PROVED.** `finrank_deformationExt1_self_eq_multSum`:
  `(finrank (deformationExt1 (intervalDirectSum L) (intervalDirectSum L)) : ℤ)
     = Σ_{i∈[1,N]} Σ_{u∈[i,N]} Σ_{j∈[u,N]} Σ_{v∈[j,N]} m_{i-1,j-1} m_{u,v}`  (m = multiplicityArray L)
  — Lehalleur–Rimányi Cor 3.5 verbatim, the algebraic content `dim Ext¹(M,M) = Σ m_{i-1,j-1} m_{uv}`.
  Supporting: `euler_identity`, `euler_interval`, `finrank_Hom_interval` (=1[u≤i≤v≤j]),
  `finrank_deformationExt1_interval` (=1[i<u≤j+1≤v]), bi-additivity over `dirSum`, the grid form
  `finrank_deformationExt1_intervalDirectSum_mult`. Axiom-clean ([propext, Classical.choice, Quot.sound]).
  Non-vacuous: (2,2,2)/ℚ witnesses (1,1)→3, {A=0}→4, matching the paper.
- **CITED / DEFERRED.** `deformationExt1` = derived Ext¹ for the hereditary path algebra kQ — the
  categorical-Ext bridge is deferred (named in the docstring, not proved). Standard (ASS / Crawley-Boevey).
- **DEFERRED (Phase B).** The *geometric* `codim O_M = dim Ext¹(M,M)` (Voigt). Reduces to the single
  orbit-dimension fact `dim O_M = dim G_d − dim Aut(M)` (+ dim Ō = dim O, codim = dim Rep − dim O). Nothing
  named `codim…` exists yet. Operator decision pending: (A) name that fact as a Cited/Assumed hypothesis;
  (B) build the orbit-dimension AG to prove it.

Team: ext-phaseA (four tides) stood down. Phase B awaits the operator A/B call.

## PHASE B — DECISION: BUILD IT (operator, 2026-06-18)

Operator chose (B): build the orbit-dimension AG and prove the geometric codim O_M = dim Ext¹(M,M) as
hardened bedrock — NOT a cited bridge. Rising-sea: develop standard AG on Mathlib's foundations until the
geometric codimension is a corollary. Largest/least-charted build of the programme (Mathlib lacks
algebraic groups / orbit dimension / scheme tangent space).

### Two candidate routes (design pass to pick the Lean-feasible standard one)
- **Tangent-space route (ties to Phase A's δ).** T_M Rep = C¹ (affine space, smooth); the orbit's tangent
  space at M is B¹ = im δ_M (the Phase-A coboundary map δ_M : C⁰ → C¹). Orbit smooth ⇒ dim O = dim T_M O =
  dim(im δ_M); dim Ō = dim O; codim Ō = dim Rep − dim O = dim C¹ − dim(im δ_M) = dim(C¹/B¹) = dim Ext¹
  (Z¹=C¹ hereditary). Connects the geometry directly to the committed DeformationExt δ.
- **Orbit–stabiliser route.** dim O = dim G − dim Stab, Stab = Aut(M) open in End(M), dim Stab = dim Hom;
  codim = dim Rep − dim G + dim Hom = dim Hom − ⟨d,d⟩ = dim Ext¹. Needs the fibre-dimension theorem.

### Geometric facts to build (the Phase-B ladder, to be pinned by the design pass)
(i) define codim of a closed subvariety of affine space (Krull dim / Ideal.height / ambient − dim);
(ii) the orbit is a smooth locally-closed irreducible subvariety with T_M O = im δ_M;
(iii) dim O = dim T_M O (smoothness); (iv) dim Ō = dim O; (v) codim Ō = dim Rep − dim Ō; glue via Phase A.
On Mathlib primitives: MulAction.orbit/stabilizer, ringKrullDim/topologicalKrullDim, Ideal.height + Krull
height theorem, MvPolynomial varieties, Module.Cotangent/KaehlerDifferential. Codex-check the standard
development at each step.

## PHASE B DESIGN — scoping correction (phaseB-design + Codex, 2026-06-18)

**B-full is unbounded (multi-expedition), not a bounded tide.** Mathlib grep + Codex (decorrelated):
ABSENT — algebraic groups / group schemes; variety dimension; scheme Zariski tangent space;
`dim O = dim G − dim Stab` (MulAction orbit–stabiliser is pure cardinality); Chevalley/fibre-dimension;
determinantal-variety codim; the catenary `dim R/I = dim R − height I`; dim = trdeg. PRESENT only to
INEQUALITY level: ringKrullDim, topologicalKrullDim, Ideal.height + Höhensatz (height ≤ spanrank),
MvPolynomial Krull dim. The "one orbit-dimension fact" IS the deep theorem; both routes (a/b) need the
same missing geometric core. Codex: "the break is not the linear algebra; it is the missing dimension
theory for images/orbit closures."

### Three-layer split (the honest structure)
- **Layer 1 — NOW, bedrock regardless.** `orbitLinearCodim M := finrank C¹ − finrank (range δ_M)`,
  prove `= finrank (deformationExt1 M M)` (rank-nullity, trivial from `finrank_quotient_add_finrank`),
  + `Stab_{G_d}(M) ↔ ker δ`-style linear identities. NAMED orbit-linear / tangent / *expected* codimension
  — NOT `codim…` (the geometric equality is unproven). Ties the geometry-to-come onto the committed δ.
- **Layer 2 — the ocean, its own sub-expedition.** AG dimension theory: (i) codim of a closed subset of
  affine kⁿ as a usable def; (ii) orbit locally closed + irreducible; (iii) dim Ō = dim O; (iv)
  `dim O = finrank im δ` — research-grade core, large from scratch. Likely upstream-Mathlib-worthy.
- **Layer 3 — bridge corollary:** `codim_Rep Ō = orbitLinearCodim = dim Ext¹`.

### Type-A rank-locus shortcut (Codex-surfaced; ties to our engine)
For equioriented type A the orbit closure is the explicit quiver rank locus
`Ō = {A : rankPattern A ≤ rankPattern M pointwise}` — a determinantal ideal (minors of `submult`), the one
place `RankPattern`/`Orbit.rankPattern_eq_iff_orbit`/orbit↔Kostant plug into geometry. Its codimension is
classical determinantal CA (also absent in Mathlib, but classical CA rather than algebraic-group theory).
Best uses: (1) the single cleanest CITED/ASSUMED bridge if we go honest-hybrid (engine-verifiable); (2) a
possible GENUINE Proved route via regular-sequence determinantal heights — to be probed on (2,2,2) first.

### Operator decision (re-scoped): the cost basis changed
"Build it" is now: commission a multi-expedition AG (or determinantal-CA) dimension-theory sub-expedition.
Plan: land Layer 1 now; probe the (2,2,2) rank-locus ideal height (cheap, picks the buildable route);
then commit the Layer-2 build route. Operator steer requested on the multi-expedition commitment + route.
