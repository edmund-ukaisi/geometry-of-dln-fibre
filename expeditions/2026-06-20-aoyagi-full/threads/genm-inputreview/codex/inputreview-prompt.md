# Decorrelated fidelity red-team: three Lean modules

You are an independent reviewer. For EACH of the three Lean modules below I give (A) the informal
mathematical claim it is supposed to formalise, and (B) the exact Lean statement(s). Your job: judge
whether the Lean FAITHFULLY states the claim — no OVERCLAIM (a stronger statement than proved/intended,
e.g. an `iff` where only one direction holds, or an aggregate/coverage claim where only a per-item claim
holds), no VACUITY (hypotheses unsatisfiable so the theorem is empty), and precise naming (the name
denotes exactly what is proven). Also independently check any stated numeric/algebraic identity or
exponent. Argue whichever way the evidence points; do not rubber-stamp. Give a per-module verdict
(FAITHFUL / OVERCLAIM / VACUOUS / WRONG-MATH) with the exact issue if any.

Assume the Lean type-checks (green build). Focus on MEANING, not syntax.

====================================================================
## MODULE 1 — chart-4 polar scaling (front-block fibre integral)

(A) Informal claim. For the front block ℝ^N (in application N = u·b), and τ = ‖YW‖ > 0, the fibre integral
extracts the scale as a monomial:
    ∫_{H ∈ ℝ^N} (‖H‖² + τ²)^{−q} dH  =  τ^{N − 2q} · K,    K := ∫_{V ∈ ℝ^N} (‖V‖² + 1)^{−q} dV,
via the Haar scaling change of variables H = τ·V. The unit integral K is finite when 2q > N (this is the
sufficiency direction; the necessity K<∞ ⟹ 2q>N is deliberately NOT claimed). Hence for τ>0 and 2q>N the
fibre integral is finite.

(B) Lean (lower integrals ∫⁻ over EuclideanSpace ℝ (Fin N), ENNReal-valued via ENNReal.ofReal):

theorem chart4_polar_scaling {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (q : ℝ) :
    ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖H‖ ^ 2 + τ ^ 2) ^ (-q))
      = ENNReal.ofReal (τ ^ ((N : ℝ) - 2 * q))
          * ∫⁻ V : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖V‖ ^ 2 + 1) ^ (-q))

theorem chart4_unit_lintegral_lt_top {N : ℕ} {q : ℝ} (hq : (N : ℝ) < 2 * q) :
    ∫⁻ V : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖V‖ ^ 2 + 1) ^ (-q)) < ⊤

theorem chart4_Htilde_fibre_lt_top {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {q : ℝ} (hq : (N : ℝ) < 2 * q) :
    ∫⁻ H : EuclideanSpace ℝ (Fin N), ENNReal.ofReal ((‖H‖ ^ 2 + τ ^ 2) ^ (-q)) < ⊤

Questions: (1) Is the scaling exponent N−2q correct and in the right direction? (2) Is 2q>N the correct
finiteness threshold for ∫_{ℝ^N}(‖V‖²+1)^{−q}? (3) Is `chart4_unit_lintegral_lt_top` an implication
(sufficiency) or does the name/statement smuggle an iff? (4) Any vacuity — is τ>0, 2q>N satisfiable? (5)
`chart4_polar_scaling` has NO hypothesis on q (any real q). Is that a problem, given both sides may be ⊤?

====================================================================
## MODULE 2 — finite-cover gluing core (measure theory)

(A) Informal claim. If a finite family of cells {C i} covers a domain D up to a null set
(μ(D \ ⋃ C i) = 0), and each cell has finite lower integral of f, then the domain integral ∫⁻_D f is
finite. Two forms: Fintype-indexed and Finset-indexed. The cells and coverage are HYPOTHESES (not built).

(B) Lean:

theorem lintegral_lt_top_of_finite_cover {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] (C : ι → Set α) (D : Set α) (f : α → ℝ≥0∞)
    (hcover : μ (D \ ⋃ i, C i) = 0)
    (hfin : ∀ i, ∫⁻ x in C i, f x ∂μ < ⊤) :
    ∫⁻ x in D, f x ∂μ < ⊤

theorem lintegral_lt_top_of_finset_cover {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (C : ι → Set α) (D : Set α) (f : α → ℝ≥0∞)
    (hcover : μ (D \ ⋃ i ∈ s, C i) = 0)
    (hfin : ∀ i ∈ s, ∫⁻ x in C i, f x ∂μ < ⊤) :
    ∫⁻ x in D, f x ∂μ < ⊤

Proof of the first uses: ∫⁻_D f ≤ ∫⁻_{⋃C} f (monotone under D ≤ᵐ ⋃C from hcover) ≤ ∑' ∫⁻_{C i} f
(countable subadditivity `lintegral_iUnion_le`, which needs NO measurability of the sets) = finite sum.

Questions: (1) Does the Lean match the informal claim exactly? (2) Note there is NO measurability
hypothesis on C, D, or f. Is the theorem still TRUE without it (is `∫⁻_{⋃ i} f ≤ ∑' ∫⁻_{C i} f`
unconditionally valid)? Does the absence make it stronger (fine) or does it hide a needed hypothesis? (3)
Is it vacuous or does it secretly require D ⊆ ⋃C exactly (not up to null)? (4) Is "≤ᵐ from μ(D\⋃C)=0"
sound?

====================================================================
## MODULE 3 — exponent-gate arithmetic (pure ℕ)

Context. For an arity-3 chain M = (M₀, M₁, M₂), a cut u ≤ min(M₀,M₁), with a = M₀−u, b = M₁−u,
d = M₂−b, the rank-ℓ(W)/rank-s(Y-block) joint incidence stratum has normal codimension (claim §3):
    C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ).
Feasible (ℓ,s): s ≤ u, ℓ+s ≤ u, (M₁−u)+ℓ ≤ M₂, u ≤ min(M₀,M₁). `minAdm M` is the minimal admissible
zero-product-stratum codimension; for arity 3 it equals min_{t ≤ min(M₀,M₁)} [(M₀−t)(M₁−t) + t·M₂].
T1_q := (minAdm M − ab)/2 is the shell threshold.

Two claimed facts: (i) ℓ-independence ring identity C_{ℓ,s} + ab = (M₀−s)(M₁−s) + s·M₂ (ℓ cancels);
(ii) PER-STRATUM gate minAdm M ≤ C_{ℓ,s} + ab, i.e. T1_q ≤ C_{ℓ,s}/2. NOT claimed: the AGGREGATE
"min over the enumerated (ℓ,s) range = 2·T1" (index-completeness is gated elsewhere).

(B) Lean (all ℕ; subtractions are truncated ℕ subtraction):

def clsCodim (M : Fin 3 → ℕ) (u ℓ s : ℕ) : ℕ :=
  u * (M 1 - u) + M 0 * ℓ + (M 0 - s) * (u - ℓ - s) + s * ((M 2 - (M 1 - u)) - ℓ)

theorem clsCodim_add_ab_eq (M : Fin 3 → ℕ) (u ℓ s : ℕ)
    (hu : u ≤ min (M 0) (M 1)) (hs : s ≤ u) (hℓs : ℓ + s ≤ u) (hbℓ : (M 1 - u) + ℓ ≤ M 2) :
    clsCodim M u ℓ s + (M 0 - u) * (M 1 - u) = (M 0 - s) * (M 1 - s) + s * M 2

theorem minAdm_arity3 (M : Fin 3 → ℕ) :
    minAdm M = (Finset.range (min (M 0) (M 1) + 1)).inf' _ (fun t => (M 0 - t) * (M 1 - t) + t * M 2)

theorem clsCodim_gate (M : Fin 3 → ℕ) (u ℓ s : ℕ)
    (hu : u ≤ min (M 0) (M 1)) (hs : s ≤ u) (hℓs : ℓ + s ≤ u) (hbℓ : (M 1 - u) + ℓ ≤ M 2) :
    minAdm M ≤ clsCodim M u ℓ s + (M 0 - u) * (M 1 - u)

theorem minAdm_le_ab_add_uM2 (M : Fin 3 → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) (hb : M 1 - u ≤ M 2) :
    minAdm M ≤ (M 0 - u) * (M 1 - u) + u * M 2

Questions: (1) Verify the ring identity C_{ℓ,s}+ab = (M₀−s)(M₁−s)+s·M₂ by hand over ℤ (expand both
sides, confirm the ℓ-terms cancel). (2) Is the gate direction (minAdm ≤ C_{ℓ,s}+ab ⟺ T1_q ≤ C_{ℓ,s}/2)
correct for a FINITENESS gate (radial ∫ r^{C_{ℓ,s}−1−2q}dr finite near 0 needs q<C_{ℓ,s}/2)? (3) The
gate uses the FULL minAdm M (min over 0..min(M₀,M₁)), not a feasibility-restricted min. Since
minAdm(full) ≤ minAdm(feasible subrange), does using the full min make T1_q SMALLER (weaker, safe) or
larger (overclaim)? (4) Does `clsCodim_gate` as stated make ANY aggregate/coverage/completeness claim, or
is it strictly per-(ℓ,s)? (5) Are the feasibility hypotheses satisfiable (non-vacuous)? (6) With
truncated ℕ subtraction, do the hypotheses guarantee no subtraction truncates in a way that breaks the
identity (i.e. is the zify-to-ℤ step valid)?
