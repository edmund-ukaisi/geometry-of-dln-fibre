<task>
I am formalising in Lean 4 + Mathlib (v4.29) the dimension identity (LR Lemma 4.6, "geometry of
DLN fibres"):

  hSweep:  varietyDim (Σ^r)  =  δ  +  varietyDim (F)

where, for a fixed dimension vector d = (d_0,…,d_N) over an alg-closed char-0 field k:
  - Tuple d = ∏_{i<N} Mat_{d_{i+1} × d_i}(k)  (composable matrix tuples; "Rep_d")
  - mult : Tuple d → Mat_{d_N × d_0},  A ↦ A_N ⋯ A_1
  - Σ^r = productRankLocus = {A | rank(mult A) = r}   (exact rank r)
  - F = fibre d E = mult⁻¹(E) for a fixed rank-r normal form E = diag(I_r, 0)
  - δ = r·(d_N + d_0 − r)
  - varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal k (canonicalCoord d '' Z))).unbotD 0
    i.e. Krull dim of the coordinate ring of the Zariski closure of the canonical flattening of Z.

LANDED (verified, sorry-free) building blocks I can use:
  1. Sweep set identity: Σ^r = ⋃_{P ∈ H} (P • ·) '' F, where H = GL_{d_N} × GL_{d_0} acts on the
     two end factors (`productRankLocus_eq_iUnion_smul_fibre`). H-equivariance mult(P•A)=P_N·mult(A)·P_0⁻¹.
  2. Constant fibre dimension: varietyDim((P•·)''F) = varietyDim F for every P
     (`varietyDim_fibre_endpoint_conj_eq`), via vanishingIdeal_image_smul + ringKrullDim_quotient_comap_ringEquiv.
  3. varietyDim transports across a coordinate-ring k-AlgEquiv between DIFFERENT ambient affine spaces:
     if  (MvPoly σ ⧸ vanishingIdeal Z) ≃ₐ[k] (MvPoly τ ⧸ vanishingIdeal W)  then varietyDim Z = varietyDim W
     (`varietyDim_eq_of_coordRingAlgEquiv`).
  4. Base stratum: ringKrullDim O(Mat^{≤r}_{d_N × d_0}) = δ  (`ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta`),
     and varietyDim(Mat^{≤r}) = δ.
  5. Mathlib PRESENT: MvPolynomial.ringKrullDim_of_isNoetherianRing :
     ringKrullDim (MvPolynomial ι A) = ringKrullDim A + Nat.card ι, for finite ι, ANY Noetherian comm ring A
     (no domain hypothesis).
  6. Schur chart membership iff (just landed): on {detΔ≠0}, rank[[Δ,B12],[B21,B22]] ≤ r ⟺ B22 = B21·Δ⁻¹·B12.
  7. Explicit regular section/retraction (sympy-verified on (2,2,2)r1, (2,2,2,2)r1, (3,3,3)r2):
     s(M) = (P_N=[[Δ,0],[B21,I]], P_0⁻¹=[[I,Δ⁻¹B12],[0,I]]), φ(A) = s(mult A)⁻¹ • A is a regular retraction
     Σ^r∩U_Δ → F (U_Δ = {detΔ(mult A)≠0}); and the claim O(Σ^r∩U_Δ) ≅ O(F)[Δ,B12,B21]_{detΔ} (δ FREE vars).

The PLAN (route iv / chart trivialization), per a prior pen-and-paper + a prior decorrelated Codex:
  rung-2: build the coordinate-ring AlgEquiv  O(Σ^r∩U_Δ) ≃ₐ[k] O(F)[δ free Schur vars]_{detΔ}
          (the explicit Φ/Ψ from the section/retraction), staying at the vanishingIdeal/varietyDim level
          (NEVER the strict generator-ideal inclusion `fibreGenIdeal ≤ ker`, which walled a prior route
          on REDUCEDNESS — R2-3b-4).
  rung-3: apply ringKrullDim_of_isNoetherianRing for the +δ.
  rung-4: finite pivot-cover glue + density (union-max over charts).
  rung-5: assemble hSweep.

QUESTION (the de-risk before I commit ~7-10 modules of build):
Given the LANDED inventory above, what is the CHEAPEST correct Lean route to hSweep? Specifically:

(A) Is the explicit chart-AlgEquiv (rung-2) genuinely necessary, or can the LANDED constant-fibre-dim
    fact (block 2) + the base-stratum dim (block 4) + the sweep (block 1) be assembled into hSweep
    WITHOUT building the chart AlgEquiv — e.g. via a fibration/total-space-dimension lemma? (Prior
    adjudication said NO: the relative-dim = fibre-dim identification needs generic-fibre machinery
    that `mult` lacks globally, because fibre dim jumps as rank drops. Do you agree, or is there a
    cheaper assembly exploiting that the fibres are CONSTANT-dimensional (homogeneous) — i.e. is there
    a clean "constant-fibre-dim fibration ⟹ dim total = dim base + dim fibre" that holds set-theoretically
    / via the explicit trivialization, avoiding Chevalley?)

(B) If the chart AlgEquiv IS necessary: what is the single cleanest Lean shape for
    O(Σ^r∩U_Δ) ≃ₐ[k] O(F)[δ]_{detΔ}? Concretely — should I (i) build it as `aeval` of the explicit
    Ψ substitution and prove it bijective via the inverse Φ substitution, both as AlgHoms on the
    localized polynomial rings, descended to the vanishingIdeal quotients; or (ii) realize Φ as a
    composite of the LANDED base-change-gauge comap (which is already an AlgEquiv transport) with a
    base/fibre splitting? Which avoids re-deriving determinantal-ideal generation?

(C) The localization-no-drop / finite-cover-glue (rung-4): is the union-max + density genuinely needed,
    or does the single top-left-pivot chart U_Δ already carry the full varietyDim of Σ^r (since Σ^r is
    irreducible-component-wise covered and the chart is dense)? If a single chart suffices, the proof
    shrinks dramatically. Under what precise condition (irreducibility? density of one chart in the
    whole locus?) can I use ONE chart and skip the cover?

Be concrete about which Mathlib v4.29 lemmas / which LANDED blocks each step uses. If a step needs a
Mathlib theorem that may be ABSENT at v4.29, name it explicitly so I can search.
</task>

<output_contract>
Three sections (A), (B), (C), in that order. For each: a direct verdict (one of: yes / no / cheaper-route-exists),
then the single cheapest concrete Lean route with the named lemmas. End with a one-paragraph "cheapest overall
route to hSweep" recommendation: the ordered list of sub-lemmas, marking each LANDED / MUST-BUILD / MATHLIB-ABSENT-RISK.
Be terse. No hedging prose.
</output_contract>

<grounding_rules>
You may reason about the mathematics freely. When you assert a Mathlib lemma exists at v4.29, mark it
[believe-present] vs [must-verify]. Distinguish a mathematical claim (provable) from a Lean-availability
claim (lemma exists). Flag any step where the set-level trivialization does NOT cleanly give the
coordinate-ring AlgEquiv (the reducedness / saturation subtlety).
</grounding_rules>
