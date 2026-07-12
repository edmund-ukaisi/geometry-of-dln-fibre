<task>
I am formalising (Lean 4 / Mathlib) the "off-sector" corank-integrability estimate for a deep-linear-network
RLCT descent. I have LANDED the b=1 case ("Obl-1") and need to design the b>1 case ("Obl-2"). I want you to
red-team my reshaped understanding and rank the cleanest formalisation routes. Withhold agreement until you
have re-derived the key facts yourself.

SETUP (exact shapes).
- Free corank block: A ∈ box = [-1,1]^{b×M2}, i.e. A : (Fin b → Fin M2 → ℝ), integrated w.r.t. Lebesgue.
- Deeper product: Z : Matrix (Fin M2) (Fin n) ℝ, FIXED, with the "full-rank tail" hypothesis
  hZ : ∀ A (b-row), c0^2 · frobSq A ≤ frobSq (A · Z)   (c0 > 0). [Equivalently ZZᵀ ⪰ c0²·I.]
- Q_b := A · Z : Matrix (Fin b) (Fin n) ℝ (the corank block).
- Freed corner: Γ ∈ ℝ^{a×b}, Ccross : Matrix (Fin a) (Fin n) ℝ, fixed pivot energy w > 0 (the reduced loss,
  held constant along the A-fibre), exponent c' with c' > a·b/2.
- Target integral: I := ∫_{A ∈ box} [ ∫_{Γ ∈ sΓ} (w + frobSq(Ccross + Γ·Q_b))^{-c'} dΓ ] dA, sΓ finite measure.

BANKED bricks I can call:
- ATOM (needs Q_bQ_bᵀ PosDef, c' > ab/2): ∫_Γ (w + ‖Ccross+Γ Q_b‖²)^{-c'} dΓ
    = det(Q_bQ_bᵀ)^{-a/2} · Cresid(ab,c') · (w + ‖Ccross(I-P)‖²)^{-(c'-ab/2)},  P = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b.
  (A ≤ set-restricted version over any sΓ also banked.)
- BOUNDED (needs only w>0, c'≥0): ∫_{Γ∈sΓ}(w+…)^{-c'} ≤ w^{-c'}·vol(sΓ).
- detGram_lintegral_lt_top: ∫_{[-1,1]^{r×N}} det(X Xᵀ)^{-a/2} dX < ⊤  for  a < N - r + 1  (r ≤ N).
- Obl-1 (b=1) OUTPUT: I ≤ C1·w^{-(c'-a/2)} + C2·w^{-(c'-M2/2)} for a < M2 (uses det(gramRow)=frobSq, a
  cube-clip {frobSq<w} of volume ≲ w^{M2/2} for the bounded regime, and the atom on the rest).

DESIGN-CERT CLAIM (pen-and-paper, that I am RE-CHECKING): "for b>1 the σ_min-only split UNDERSHOOTS
(example M=(3,3,3), t=1, a=b=2: gives 5/2 < 7/2 = ½·minAdm); the correct switch is to use the FULL determinant
det(Q_bQ_bᵀ)=∏τ_k² (not just the smallest singular τ_min²), with a singular-FLAG stratification into levels
j=0..b, per-flag charge C_j = (a-j)(b-j) + R_{t+j} ≥ minAdm(M)."  Here R_{t+j}=minAdm(reduced chain at cut t+j),
minAdm(M)=ab+R_t at a binding cut, carrierThreshold = ½·minAdm(M).

MY RESHAPED UNDERSTANDING (RED-TEAM THIS):
(U1) At EVERY b>1 binding cut I swept (arity ≤5, widths ≤6), a ≤ M2-b+1 ALWAYS (250 strict + 70 equal, 0 above).
     So the atom-weight ∫_box det(Q_bQ_bᵀ)^{-a/2} either CONVERGES (a < M2-b+1) or is BORDERLINE-log (a = M2-b+1).
(U2) In the CONVERGENT regime a < M2-b+1, the whole thing closes with a SINGLE atom bound + null-set deletion of
     the rank-drop locus {A : det(Q_bQ_bᵀ)=0} (= {det(A Aᵀ)=0} since ZZᵀ invertible), giving
       I ≤ C1 · w^{-(c'-ab/2)},  charge = ab = peelCharge.
     Because on {det>0} the atom applies pointwise (core ≤ w^{-(c'-ab/2)}), and ∫_{det>0} det^{-a/2} ≤
     ∫_box det^{-a/2} =: Wenn < ⊤. The bounded inner integral makes F(A) ≤ w^{-c'}·vol(sΓ) < ∞ for EVERY A, so
     the null locus {det=0} (Lebesgue-null) contributes 0 — legitimate here because w>0 is FIXED (unlike the
     outer tail integral where the "no null-set deletion" warning applies).
(U3) This single charge ab is EXACTLY right: fed to the level-0 reduced IH it needs c'-ab/2 < ½R_t ⟺
     c' < ½(ab+R_t) = ½·minAdm(M) = carrierThreshold(M). So NO multi-level flag is needed for a < M2-b+1;
     "the flag" in the design just means "use det(=∏τ²) not σ_min(=τ_min²)" — and detGram_lintegral_lt_top
     ALREADY integrates across the rank-drop locus up to the codim threshold a < M2-b+1.
(U4) Only the BORDERLINE a = M2-b+1 (70 cases incl. (3,3,3)) has the log divergence of Wenn and genuinely needs
     either the multi-level flag OR a log-absorption (a positive strict-margin dominates the log), analogous to
     the b=1 "a=M2 borderline log" I already carry as a tracked side-condition.

QUESTIONS (rank + justify, re-derive, do not just agree):
Q1. Is (U2)+(U3) SOUND? Specifically: does the single-atom bound with null-set deletion of {det=0} give a
    VALID upper bound for I in the convergent regime, and is the charge ab genuinely = the design's C_0 freed
    charge (so no undershoot vs the flag)? Find any error. Does anything the design says about "σ_min-only
    undershoots" actually contradict the det-based single-atom bound, or is it only about the σ_min² weight?
Q2. Is (U1) plausibly a THEOREM (a ≤ M2-b+1 at every b>1 binding cut), or an artefact of my finite sweep?
    Give the cleanest argument (from convexity R_{t+1}-R_t ≥ a+b-1 and incidence R_{t+1}-R_t ≤ M2) or a
    counterexample.
Q3. For the corank weight Wenn = ∫_box det(A ZZᵀ Aᵀ)^{-a/2} < ⊤ (a < M2-b+1): rank the two Lean routes —
    (R-CoV) factor ZZᵀ = L Lᵀ (LDL/Cholesky, Mathlib has LDL), change variables Y=A·L (Jacobian det(L)^b),
    reduce to ∫_{L·box} det(Y Yᵀ)^{-a/2} ≤ ∫_{matBox b M2 T} … via detGram_lintegral_lt_top (scaled box);
    vs (R-mono) prove PSD Löwner det-monotonicity 0⪯P⪯Q ⟹ det P ≤ det Q from scratch to get
    det(A ZZᵀ Aᵀ) ≥ c0^{2b} det(A Aᵀ). Which is less Lean-friction at Mathlib v4.29? Any THIRD route?
Q4. The measure-zero of {A ∈ box : det(A Aᵀ)=0} (b≤M2, so a nonzero degree-2b polynomial's zero set): cleanest
    Lean route at v4.29 (Mathlib seems to LACK a ready "nonzero polynomial zero set is Lebesgue-null" in ℝ^N)?
    Is there a way to AVOID needing it (e.g. a pointwise bound valid even at det=0)?
Q5. Given all above: is the right formalisation deliverable "Obl-2 = the convergent-regime single-atom lemma
    (a < M2-b+1)" with the borderline a=M2-b+1 carried as a tracked side-condition (mirroring b=1's a=M2), and
    the multi-level flag deferred? Or is the multi-level flag genuinely required for the CONVERGENT regime too
    (find the hole in U2/U3 if so)?
</task>

<output_contract>
Answer Q1..Q5 in order, each ≤ 200 words. For Q1 and Q5 give an explicit VERDICT token: SOUND / UNSOUND /
SOUND-WITH-CAVEAT and name the caveat. For Q3 give a ranked 1-2 (cheapest first) with the single biggest
Lean-friction risk of the top choice. Be concrete about Mathlib v4.29 lemma availability where you can; flag
inference vs recalled-fact.
</output_contract>

<grounding_rules>
Distinguish (a) mathematical facts you re-derived here from (b) recalled Mathlib API that may be wrong at the
v4.29 pin — tag the latter "[recall, verify]". Do not invent lemma names as if confirmed. If you cannot
re-derive a claim, say so rather than agreeing.
</grounding_rules>
