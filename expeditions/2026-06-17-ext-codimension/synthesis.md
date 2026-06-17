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
