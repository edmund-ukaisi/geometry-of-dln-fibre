<task>
You are a second, decorrelated expert (measure theory + real algebraic geometry + change-of-variables
finiteness estimates). I want your INDEPENDENT verdict on whether a specific multi-dimensional integral is
FINITE, and on the cleanest change-of-variables to certify it. I am WITHHOLDING my own tentative conclusion
so as not to anchor you — argue whichever way the algebra points, and if it is a divergence, exhibit the
divergent direction explicitly.

## The setting (a deep-linear-network RLCT "front charge" integral)

Fix naturals u ≥ 1, a = M₀−u ≥ 1, b = M₁−u ≥ 1, and a "deep effective width" ρ ≥ 1, with the SCOPE
    a + b ≤ ρ − 1        (STRICT; equivalently d := ρ − b ≥ a + 1).
Fix a real exponent q with 0 < q, and the finiteness threshold is governed by a per-stratum codimension gate
(stated below). All matrices are real, all "box" integrations are over entrywise [−1,1] cubes unless noted.

There are TWO nested finiteness questions. Please treat them separately and then jointly.

### PART A — the LEAF integral (deep factor trivial, ρ columns), the CRUX.

Variables (all over boxes):
- z0 : u×ρ   (pivot rows source)
- A  : b×ρ   (corank rows source)          [call it A_cor]
- P  : u×u   restricted to the invertible chart {det P ≠ 0}
- B  : u×b
- C  : a×u
Set the pivot rows Q_p = z0 (u×ρ), corank rows Q_b = A (b×ρ). Let
    Π_b = Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b     (orthogonal projection onto row(Q_b), a ρ×ρ projector),
    E_top = ‖P·Q_p + B·Q_b‖²_F,
    E_tr  = ‖C·(Q_p + P⁻¹ B Q_b)·(I_ρ − Π_b)‖²_F.
The corank charge is det(Q_b Q_bᵀ)^{−a/2} (a b×b Gram; PosDef a.e. since b ≤ ρ). The LEAF integral is

    I_leaf := ∫_{z0,A,P,B,C over boxes, det P≠0}
                 det(Q_b Q_bᵀ)^{−a/2} · ( E_top + E_tr )^{−q}   d(all).

GOAL A: is I_leaf < ∞ for the exponent range below, in scope a+b ≤ ρ−1?

The proposed CoV atlas (each step named; I want you to check the JACOBIAN BOOKKEEPING, esp. the |det D| powers):
1. Minor chart on A: A = D·[I_b | X], D∈GL_b (b×b), X∈ℝ^{b×(ρ−b)}=ℝ^{b×d}. Jacobian dA = |det D|^d dD dX.
2. Corank charge: det(Q_bQ_bᵀ) = det(D)²·det(I_b+XXᵀ), so det^{−a/2} = |det D|^{−a}·(bounded X-unit).
   Running |det D| power after steps 1–2: |det D|^{d−a}.
3. Pivot shear: Q_p = [U | U X + W], U = z0's first b cols (u×b), W = z0·[−X;I_d] (u×d). Jacobian 1.
   Transverse Schur: Q_p(I−Π_b)Q_pᵀ = W(I+XᵀX)⁻¹Wᵀ, so E_tr ≍ ‖Y W‖²_F with Y=(P;C) ((u+a)×u = M₀×u).
4. Front B-shear: H = P U + B D. As a change in B: dB = |det D|^{−u} dH. Running |det D| power: |det D|^{d−a−u}.
   Then H̃ = H + (X-dependent shift), measure-preserving. Loss ≍ ‖H̃‖²_F + ‖Y W‖²_F.
5. The H̃-fibre: ∫_{H̃∈ℝ^{ub}} (‖H̃‖² + τ²)^{−q} dH̃ = τ^{ub−2q}·K, τ = ‖YW‖, finite iff 2q > ub.
6. W- and Y-block determinantal big cells (Schur-complement CoV, Jacobian 1), then radial blow-up so each
   stratum (ℓ = rank-drop index of W, s = rank index of Y-block) has radial measure r^{C_{ℓ,s}−1} dr and
   the loss contributes r^{−2q}, giving ∫₀^δ r^{C_{ℓ,s}−1−2q} dr, finite iff q < C_{ℓ,s}/2.

The EXPONENT GATE (assume PROVEN; it is an exact ring identity + a min bound): for every valid stratum (ℓ,s),
    C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ),   and   min_{ℓ,s} C_{ℓ,s} / 2 ≥ q   (strictly > q in scope).
So each per-stratum radial integral converges. That is not in question.

The CRUX I want you to adjudicate: step 4 leaves the weight |det D|^{d−a−u}. The scope gives only d ≥ a+1
(from a+b ≤ ρ−1), NOT d ≥ a+u. So |det D|^{d−a−u} can carry a NEGATIVE net power of |det D| (when u ≥ 2).
Step 5 as written ENLARGES the H̃-image from the D-dependent parallelepiped {H = PU + B·D : B∈box} (a set of
volume ∝ |det D|^u that SHRINKS as D→0) to all of ℝ^{ub}. Concretely:
   ∫_{B∈box} (‖H̃‖²+τ²)^{−q} dB = |det D|^{−u} ∫_{H∈R_D} (‖H̃‖²+τ²)^{−q} dH,  R_D = PU + box·D,  vol(R_D) ∝ |det D|^u.
Enlarging R_D ↦ ℝ^{ub} gives the a-fortiori |det D|^{−u}·τ^{ub−2q}·K, hence the total D-weight |det D|^{d−a−u}
whose b×b determinantal radial (via SVD/triangular pivots δ_i, dD ~ ∏δ_i^{b−i}...) has schematic pivot
exponents (d−a−u) + 2(i−1) per δ_i, which need NOT be > −1 (a divergence) when u ≥ 2.

Q-A1. Is the ENLARGEMENT in step 5 a genuine over-count that creates a FALSE divergence, or is |det D|^{d−a−u}
   actually integrable as written (i.e. is the b×b determinantal measure ∏_i δ_i^{(d−a−u)+2(i−1)} dδ_i finite
   under d ≥ a+1)? Give the exact per-pivot exponent condition and evaluate it at the borderline d = a+1, u = 2, b = 2.

Q-A2. If the enlargement over-counts: is the "joint D–H tube resolution" (do NOT enlarge; estimate
   ∫_{H∈R_D}(‖H̃‖²+τ²)^{−q}dH as a function of BOTH ‖D‖ and τ) actually FINITE overall? Please carry out the
   two-region estimate: region {‖D‖ ≲ τ} (R_D small vs τ) vs {‖D‖ ≳ τ}, give the D-weight on each region, and
   determine whether each converges. Is the correct statement "on {‖D‖≲τ} the tube retention cancels |det D|^{−u},
   restoring |det D|^{d−a} (integrable since d≥a); on {‖D‖≳τ} the τ^{ub−2q} decay + bounded |det D| closes it"?
   Verify or refute, with the exact exponents.

Q-A3. Given only a FINITENESS goal (< ∞, not a sharp constant), is there a materially SIMPLER route than the
   full joint tube — e.g. keep B in its box and dominate the H̃-fibre by min(vol(R_D)·τ^{−2q}, ℝ^{ub}-value),
   or a single clean lower bound E_top+E_tr ≥ (monomial) that separates the variables enough? Or is the joint
   D–H coupling genuinely irreducible (the min-codimension attained at an INTERIOR stratum forces it)?

### PART B — the DEEP factor (general depth): does the tail obstruct the leaf reduction?

Now the true integral has a deep factor. Replace Q_p, Q_b by
    Q_p = z0 · Z,   Q_b = A · Z,   Z = Z(z_tail) an M₂×n matrix (n = last width), z_tail over a box,
with z0 : u×M₂, A : b×M₂. Z is a PRODUCT of layer matrices (a shorter deep-linear chain), whose GENERIC rank
is exactly ρ := min(M₂, …, n) = "deepTailMin" (NOT necessarily M₂ — ρ ≤ M₂, and ρ < M₂ is reachable, e.g. a
narrow interior layer). rank Z = ρ for a.e. z_tail; rank Z < ρ on a measure-zero (but positive-codimension)
set. The scope a+b ≤ ρ−1 is on this ρ.

I claim (please verify) the whole integrand depends on (z0, A, z_tail) only through Q_p, Q_b, and only through
Z's rank-ρ row space: writing a rank factorization Z = S̃·Õ with S̃ (M₂×ρ, full col rank a.e.), Õ (ρ×n, ÕÕᵀ=I_ρ),
one has det(Q_bQ_bᵀ)=det((AS̃)(AS̃)ᵀ), E_top=‖P(z0 S̃)+B(A S̃)‖²_F, and E_tr reduces to the ρ-dim leaf form in
(z0 S̃, A S̃). So the map (z0,A) ↦ (Q̂_p, Q̂_b) := (z0 S̃, A S̃) sends the integrand to the PART-A leaf integrand
in dimension ρ.

Q-B1. Is that reduction exact (verify the E_tr claim: Q̃ₚ(I_n−Π_b) = Q̂ₚ̃(I_ρ−Π̂_b)Õ, hence ‖C·(...)‖ reduces)?

Q-B2. The map (z0,A) ↦ (z0 S̃, A S̃) from ℝ^{u×M₂}×ℝ^{b×M₂} to ℝ^{u×ρ}×ℝ^{b×ρ} is a linear SURJECTION with
   kernel of dim (u+b)(M₂−ρ). Pushing the box measure forward gives a bounded compactly-supported density ψ(·;S̃)
   on the ρ-image; ψ and its support BLOW UP as S̃'s smallest singular value → 0 (i.e. as rank Z → below ρ).
   So the z_tail-integration of the S̃-dependent constant is the "tail coupling." Is this z_tail-integration
   FINITE, or is the neighborhood of {rank Z < ρ} a genuine divergence? Note: the corank charge
   det((AS̃)(AS̃)ᵀ)^{−a/2} only blows up where rank(A S̃) < b, i.e. rank S̃ (=rank Z) drops BELOW b = ρ−(a+2),
   a drop of ≥ a+2 from the generic ρ — a HIGH-codimension locus. Does that high codimension (vs the −a/2 power)
   render the tail charge integrable, analogously to Part A's corank charge? Or does ψ's blow-up (a separate,
   lower-codimension effect at the FIRST rank drop rank Z = ρ−1) dominate and diverge?

Q-B3. VERDICT: is the general-depth front-charge integral I = ∫ det(Q_bQ_bᵀ)^{−a/2}(E_top+E_tr)^{−q} FINITE
   (bounded multi-step labour, no new obstruction beyond Part A's tube + a corank-charge-style tail estimate),
   or is there a genuine general-depth WALL that the leaf/Part-A analysis misses? If a wall, isolate the exact
   divergent direction (which layer degeneration, which exponent fails) as precisely as you can.

<output_contract>
Answer each of Q-A1, Q-A2, Q-A3, Q-B1, Q-B2, Q-B3 in order, labelled. For each: lead with FINITE / DIVERGENT /
UNDETERMINED, then the exact exponent arithmetic (per-pivot δ_i exponents, region estimates, codimension-vs-power
comparisons). Be concrete with the borderline cases I named (d=a+1, u=2, b=2; rank drop ρ→ρ−1 vs ρ→b). If you
disagree with a claimed identity or reduction, say so and give the corrected statement. Distinguish [FACT]
(you verified the algebra) from [INFERENCE] (structural expectation). End with the single most likely way the
overall finiteness could FAIL, if any. Concise; exact algebra over prose.
</output_contract>

<grounding_rules>
- Ground in the exact exponents given. Do not invent a different normalization silently; if you change one,
  state it. The b×b determinantal Lebesgue measure in SVD/triangular pivot coordinates and its pivot exponents
  are load-bearing — get them right and show them.
- The exponent gate min_{ℓ,s} C_{ℓ,s}/2 ≥ q is GIVEN (proven); do not re-litigate it. The open questions are
  the |det D| tube (Part A) and the tail/deep-factor coupling (Part B).
- "FINITE" must mean a stated, checkable exponent inequality holds (e.g. every δ_i-pivot exponent > −1). Say
  which inequality and whether the given scope (d≥a+1) delivers it.
</grounding_rules>
</task>
