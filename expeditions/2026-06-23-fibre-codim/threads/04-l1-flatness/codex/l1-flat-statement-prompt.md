<task>
Lean 4 + Mathlib v4.29 formalisation. I must SPECIFY (and decide whether to PROVE now or
checkpoint-with-fallback) a single GATING fact, call it "L1-0", inside an existing affine-variety
"engine" for deep-linear-network multiplication fibres. Give me a decorrelated verdict; I will
withhold my own.

THE GEOMETRY. Fix a dimension vector d = (d_0,...,d_N). Rep_d = ∏_{i=1}^N Mat_{d_i × d_{i-1}} is a
product of matrix spaces ("Tuple d" in Lean). mult : Rep_d → Mat_{d_N × d_0} sends (A_1,...,A_N) to
the ordered product A_N···A_1. For a target B of rank r, the fibre mult^{-1}(B) and the exact-rank
locus Σ^r = {A | rank(mult A) = r} sit inside Rep_d. The base of the bundle is the rank-r
determinantal stratum Mat^{rk=r}_{d_N × d_0}. LR Lemma 4.6: mult : Σ^r → Mat^{rk=r} is a Zariski-
LOCALLY-trivial fibre bundle (G_out = GL_{d_N} × GL_{d_0} acts transitively on Mat^{rk=r}; local
sections of the submersion G_out → Mat^{rk=r} give equivariant local trivialisations). It is NOT
globally trivial (the G_out^B-torsor base map has no global section).

WHAT IS ACTUALLY IN THE ENGINE (Lean). The engine handles dimension/codimension PURELY set-
theoretically + via vanishing ideals. Concretely:
- Geometry is "Set (Tuple d)". There is NO scheme, NO Spec, NO morphism of schemes.
- codimRep Z := Ideal.height (vanishingIdeal (coord '' Z)) in MvPolynomial (RepCoord d) k, where
  RepCoord d enumerates matrix entries (one variable per entry) and coord is the canonical entry-
  flattening Tuple d ≃ (RepCoord d → k). "varietyDim Z" = ringKrullDim of the quotient by that
  vanishing ideal. card = #entries.
- Landed facts: dim Σ^r and dim Mat^{rk=r} = r(d_0+d_N−r) are BOTH known (as varietyDim of the
  respective loci). Catenary complement codim = card − dim is landed (primality-gated).
- The engine has the going-down + height-additivity levers ALREADY in use:
  instance [Module.Flat A B] : Algebra.HasGoingDown A B; and
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P over p):
    P.height = p.height + (P.map (Quotient.mk (p.map (algebraMap A B)))).height.
- CRUCIALLY: there is NO coordinate-ring map for mult between two quotient rings. mult exists only
  as a FUNCTION on Tuple d (Set-level). No pullback ring hom k[Mat^{rk=r}] → k[Σ^r] has been built.

THE STATED ROUTE for L1-0 (from a design recon): "Module.Flat A B for the coordinate-ring map of
mult restricted to a rank-r chart, via local triviality ⟹ trivial product ⟹ free ⟹ flat", feeding
the height-additivity lever to extract dim(fibre).

API PROBE RESULT (verified, compiles at v4.29): the Module.Flat surface is fully present and easy:
free⟹flat (instance + Module.Flat.of_free); MvPolynomial (Fin r) A is free hence flat over A;
Module.Flat.of_linearEquiv transports flatness across ≃ₗ and across ≃ₐ (via .toLinearEquiv);
Module.Flat.trans; tensor-of-frees-is-free; and the downstream HasGoingDown + height_eq_height_add
both sit on Module.Flat. So once you HAVE B ≃ₐ[A] (a free A-algebra), Module.Flat A B is a one-liner.

THE TENSION I want you to adjudicate. The Module.Flat *API* is not the wall. The wall is producing
the actual rings A (= k[Mat^{rk=r} chart]) and B (= k[Σ^r chart]), the algebra structure A → B
realising mult's pullback, and the algebra equivalence B ≃ₐ[A] (free) from LOCAL triviality —
none of which exists in the engine, and "locally trivial, not globally trivial" means there is NO
global B ≃ₐ[A] k[Fin r ⊗ A]. Building a faithful "rank-r chart", its coordinate ring as a
localisation/quotient, the pullback algebra map, and the local-trivialisation-⟹-free argument is a
from-scratch affine-AG construction (principal-open localisation of a determinantal quotient ring,
plus an honest section of the torsor) with no landed template.

QUESTIONS.
(1) Is there an HONEST Lean v4.29 statement of "Module.Flat A B for the localised mult" that is
    (a) non-vacuous, (b) faithful to LR Lemma 4.6, and (c) reachable WITHOUT first building the
    scheme-theoretic / coordinate-ring morphism of mult and an explicit chart localisation? Or is
    any such statement either vacuous (e.g. a tautological "if B≃ₐfree then flat") or requires the
    missing chart+pullback machinery?
(2) Local (not global) triviality: can flatness be obtained as a LOCAL-on-base property in this
    Set+vanishing-ideal engine without sheaf/scheme infrastructure? Does Mathlib v4.29 have a
    flat-local-on-base / flat-descent lemma usable WITHOUT schemes (just ring homs + a finite
    principal-open cover of Spec A)? Name it if so.
(3) If L1-0 as "Module.Flat of the localised mult" is NOT cleanly reachable this run, rank the
    fallbacks: (i) the two-inequality dim sandwich (cheap going-up/down lower bound + an
    equidimensionality upper bound from G_out-homogeneity); (ii) discharge only r ≤ 1 / N small as a
    non-vacuity witness and roadmap generality; (iii) build the honest chart+pullback+free machinery
    (estimate module count). Which is the best value-per-effort, and what is the single cheapest
    honestly-landable brick toward retiring the cited bundle-shift?
(4) Is there a DIFFERENT cheap honest target that captures real content of L1-0 without the chart
    machinery — e.g. flatness of the trivial-product MODEL (prove the model fibre bundle k[base] →
    k[base] ⊗ k[fibre] is flat, as a faithful local model), explicitly named as "the local model,
    cited that the actual bundle is locally isomorphic to it"? Is that honest bedrock or is it
    overclaiming?
</task>

<output_contract>
Five short sections, in this order, terse:
A. VERDICT on (1): is there an honest non-vacuous reachable Module.Flat statement WITHOUT the chart
   morphism machinery? YES/NO + one-paragraph why.
B. (2): flat-local-on-base in v4.29 without schemes — exists? name the lemma or say "not usable".
C. (3): ranked fallbacks with a one-line value-per-effort each, and the single cheapest honest brick.
D. (4): is the "local model flatness, cited isomorphism" target honest bedrock or overclaiming?
E. BOTTOM LINE: one of {PROVE the Module.Flat statement now (give the exact honest statement) |
   CHECKPOINT with fallback X}. Be decisive.
</output_contract>

<grounding_rules>
Distinguish Mathlib lemmas you are CONFIDENT exist at v4.29 from ones you are INFERRING. Do not
invent lemma names; if unsure, say "verify". Treat the API-probe result above as established fact.
The honesty bar: a theorem's name+statement must denote exactly what is proven — flag any framing
that would overclaim (e.g. naming a local-model lemma as if it proved the actual bundle's flatness).
</grounding_rules>
