<task>
Lean 4 + Mathlib formalisation, DLN (deep linear network) RLCT project. I must close ONE remaining
`sorry` ("hstep2") that finishes the ∀-L deepest-gauge diffeo bridge (#120). I need a decorrelated
judgment on ROUTE and SCOPE before committing a multi-tide build.

GOAL (the sorry, in the L≥3 arm of `deepest_gauge_construction`):
  rlctAtOn Φscore wstar = rlctAtOn Φcore wstar
where wstar = image of the deepest point in flat coordinates, and
  Φscore x = (∑ i, (regStraighten (split x)).1 i ^2) + Score x
  Φcore  x = (∑ i, (regStraighten (split x)).1 i ^2) + deepestCoreF r (coreAbsorb (split x)).2.1
`rlctAtOn F w` = the real log-canonical threshold of F at w (a local integrability exponent; volume
Haar measure). The two functions share the reg-energy term `∑ (regStraighten(split x)).1²`; they
differ only in the CORE term: `Score x` vs `deepestCoreF r (coreAbsorb(split x)).2.1`.

Score x = Frobenius-sq of the (1,1)-Schur complement of reindex(endpointP0·(prod(symm x) − B)·endpointQL),
i.e. Score = frobSq(blockSchur(∏_k C_k)) where C_k are the framed, 2×2-blocked DLN layers (r×r pivot
block + core block). deepestCoreF(coreAbsorb …) is (essentially) frobSq of the PLAIN ordered product
of per-layer Schur cores ∏_k S_k, S_k = blockSchur(C_k).

BANKED (sorry-free, available):
 - `schur_product_ldu_rec` (abstract, Type-valued core widths): blockSchur(∏_{k<L} C_k) = coreProd,
   where coreProd = S_0·(1−K_1)·S_1·(1−K_2)·…·(1−K_{L−1})·S_{L−1},
   K_k = (C_k)₂₁·((partProd C (k+1))₁₁)⁻¹·((partProd C k)₁₂). Carries Invertible hyps on all pivots.
 - `rlctAtOn_comp_localDiffeo` (universe-poly): for F:M→ℝ, f:M→M global `ContDiff ℝ ⊤`, e:M≃L[ℝ]M with
   `HasStrictFDerivAt f e wstar` and `f wstar = wstar`  ⟹  rlctAtOn (F∘f) wstar = rlctAtOn F wstar.

CERT'S CLAIMED ROUTE (pen&paper, sympy-checked at L=3 r,M∈{1,2} + L=4): Score = Φcore ∘ Ψ where Ψ is the
"absorbing diffeo" S_i ↦ (I−K_i)·S_i on core coords, identity on reg/spec; Ψ is a LOCAL ANALYTIC DIFFEO
at 0 with dΨ(0)=I (every cross-term carries the vanishing factor S_i(0)=0, since the deepest core =0).
So apply rlctAtOn_comp_localDiffeo with f=Ψ, e=id, F=Φcore. At L=2 K is core-INDEPENDENT (explicit
linear inverse); at L≥3 K_i (i≥2) is core-DEPENDENT, hence the IFT (not explicit inverse). NOTHING of Ψ
is defined yet for general L; the L=2 analog machinery (define Ψ, prove ContDiff, prove strict-deriv,
the "Fin (H k)"-width DLN cast-bridge relating abstract schur_product_ldu_rec to concrete prod, and the
assembly) totals ~4000 lines across several files.

MY ASSESSMENT: closing hstep2 = multi-tide (~1500-3500 LoC). There is NO clean isolated sorry-free
"algebraic" brick beyond schur_product_ldu_rec, because the coreProd = ∏S∘Ψ identity IS effectively the
DEFINITION of Ψ (analytic, K core-dependent), only meaningful once Ψ is constructed on the concrete
space; and Ψ's strict-deriv/smoothness need the concrete DLN block decomposition.
</task>

<output_contract>
Four sections, terse:
1. ROUTE CHECK: Is the cert's Ψ-IFT route the right/only viable one, or is there a materially SIMPLER
   route to `rlctAtOn Φscore = rlctAtOn Φcore` I'm missing? Consider: (a) a direct measure-preserving
   change of variables argument avoiding the local-diffeo IFT; (b) exploiting that rlctAtOn is a LOCAL
   exponent so only a germ/jet of the difference matters; (c) any way to reduce to the L=2 assembled
   theorem by grouping layers (G0 = first L−1, G1 = last), turning ∀L into a 2-factor instance.
2. SCOPE: agree/disagree it's multi-tide with no single-session close; if you see a <~400-LoC path,
   describe it concretely.
3. SMALLEST FIRST BRICK: the single most valuable sorry-free lemma to bank first (exact statement
   shape), that a later tide builds on — or confirm none is cleanly isolable before Ψ is defined.
4. RISK: the most likely thing that turns "bounded IFT labor" into a genuine wall (e.g. dΨ(0)=I not
   formalizing, or the Fin-width cast-bridge).
Flag inference vs. fact explicitly. Do NOT emit Lean code longer than a signature.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the math + the interfaces I gave. If a claim depends on a Lean
API existing that I did not confirm banked, mark it "assumed API". Distinguish "mathematically true" from
"cheaply formalizable at Mathlib v4.29".
</grounding_rules>
