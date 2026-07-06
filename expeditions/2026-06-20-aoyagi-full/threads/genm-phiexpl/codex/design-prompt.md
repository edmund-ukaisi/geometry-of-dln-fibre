<task>
I am formalising in Lean 4 + Mathlib (v4.29) the L=2 case of Aoyagi's Step-1 corner-elimination
RLCT reduction for deep linear networks. I must close ONE remaining theorem (currently `sorry`):

    theorem d1ge_L2_hAtV_explicit
        (H : Fin (2+1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
        (v : Params H) (hopt : prod H v = B) (hB : B.rank = r) :
        ∃ P : Params (fun s => H s - r),
          (nRegL2 H r : ℝ≥0∞)/2 + rlctAtOn (fun A => dlnLoss (H-r) 0 A) P
            ≤ rlctAt H (dlnLoss H B) v

Here `Params H = ∀ s:Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`; `prod H` = ordered
matrix product of layers; `dlnLoss H B A = ∑_{i,j} ((prod H A - B) i j)^2` (square-Frobenius);
`rlctAt`/`rlctAtOn` = real log-canonical threshold (a sSup over exponents c' with |F|^{-c'} locally
integrable); `nRegL2 H r = r*(H 0 + H (last 2) - r)`; widths H0,H1,H2, product rank r.

A DOWNSTREAM consumer theorem is ALREADY PROVEN sorry-free (`d1ge_L2_hAtV_of_explicit_chart`). It
takes these inputs and yields the conclusion:
  - Y : a finite-dim real normed measure space (BorelSpace, ProperSpace, finite-measure-on-compacts);
  - qₑ : (Fin (nRegL2 H r) → ℝ) × Y → EuclideanSpace ℝ (Fin n);  hq : ContDiff ℝ 1 qₑ;  t0 : Y;
  - hchart : rlctAt H (dlnLoss H B) v
        = rlctAtOn (fun p => (∑ i, p.1 i ^2) + (∑ i, qₑ p i ^2)) ((0 : Fin nReg → ℝ), t0);
  - hRne : ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(vol.restrict U), (∑ i, qₑ (0,z) i ^2) ≠ 0;
  - e : Y ≃ₜ (Fin (flatDim (H-r)) → ℝ) × (Fin specDim → ℝ), measure-preserving + measurable-embedding;
  - u : Y → ℝ measurable, ∃ U ∈ 𝓝 t0, ua ≤ |u| ≤ ub on U (ua>0);
  - hfact : ∀ t, (∑ i, qₑ (0,t) i ^2) = u t * dlnLoss (H-r) 0 ((paramsEquivFlat (H-r)).symm (e t).1).
The intended plan ("Option A"): choose Y = (Fin (flatDim (H-r)) → ℝ) × (Fin specDim → ℝ), e = refl,
u ≡ 1. Then hfact reduces to definitions + two BANKED matrix-algebra lemmas:
  schur_product_factor : (over any CommRing, X and M11=X*S+Y*U invertible)
     (Z*T+W*V) - (Z*S+W*U) * ⅟(X*S+Y*U) * (X*T+Y*V) = (W - Z*⅟X*Y) * (V - U*⅟(X*S+Y*U)*(X*T+Y*V));
  schur_complement_zero_of_rank_le : (over a field, B11 invertible, rank(fromBlocks B11 B12 B21 B22) ≤ r)
     ⟹ B22 = B21 * ⅟B11 * B12.
So the measure-theoretic wiring is claimed trivial. The OPEN work is producing qₑ, hq, t0, hchart, hRne
via the explicit "Φ_expl" corner-elimination chart.

THE MATH (splitwit-verified numerically at (4,4,4)/r=1, ‖Δ‖≈1e-15): pick a common invertible r×r pivot
of the layers at v; block A0=[[X:r×r,Y:r×(H1−r)],[Z:(H0−r)×r,W:(H0−r)×(H1−r)]],
A1=[[S,T],[U,V]] similarly; product blocks M11=XS+YU, M12=XT+YV, M21=ZS+WU, M22=ZT+WV.
On {det X≠0, det M11≠0} the reparametrisation
    w = (A0,A1)  ↔  (p | A0red, A1red | X, Y, U),
    p = (M11−B11, M12−B12, M21−B21)          [dim = nRegL2 = r(H0+H2−r), the "regular block"],
    A0red = W − Z X⁻¹ Y : (H0−r)×(H1−r),  A1red = V − U M11⁻¹ M12 : (H1−r)×(H2−r)  [the reduced core],
    (X,Y,U)                                    [dim specDim = r² + 2r(H1−r), the FLAT spectators],
is a rational bijection (rational in det X, det M11) with an exact rational two-sided inverse; the
dimensions sum to flatDim H = H0·H1 + H1·H2 (verified). Since rank B = r and B11 invertible, Schur(B)=0
i.e. B22 = B21 B11⁻¹ B12. And M22−B22 = A0red·A1red + R(p) with R(p) := M21 M11⁻¹ M12 − B21 B11⁻¹ B12
(function of p only, since M11=B11+p1 etc.), R(0)=0. So the DLN loss = ∑p² + ‖M22−B22‖², and defining
qₑ(p,(core,spec)) := reshaped(A0red·A1red + R(p)) gives ∑qₑ(0,·)² = ‖A0red·A1red‖² = dlnLoss(H-r) 0.
The chart Jacobian det = ±det X · det(M11)³ ≠ 0 on the domain.

INFRASTRUCTURE I HAVE (all sorry-free, Lean-level):
  * rlctAt_eq_rlctAtOn_lossFlatShift : rlctAt H (dlnLoss H B) v = rlctAtOn (lossFlatShift H B v) 0,
    where lossFlatShift w = dlnLoss H B ((paramsEquivFlat H).symm (w + paramsEquivFlat H v)).
  * rlctAtOn_eq_of_contDiff_chart (E finite-dim normed Haar measure space):
      given Φ:E→E with ContDiff ℝ 2 Φ, HasFDerivAt Φ (f':E≃L[ℝ]E) wstar, Φ wstar = wstar,
      and germ f =ᶠ[𝓝 wstar] (fun w => F (Φ w)), THEN rlctAtOn f wstar = rlctAtOn F wstar.
    (It internally builds the local inverse via the inverse function theorem; I only supply the FORWARD
    map Φ, its GLOBAL ContDiff ℝ 2, an invertible derivative f' at wstar, the fixed point, and the germ.)
  * splitHomeo : (Fin (flatDim H)→ℝ) ≃ₜ (Fin m→ℝ)×(Fin (flatDim H − m)→ℝ), measure-preserving, C^∞.symm
    (separates a chosen coordinate subset from its complement).
  * exists_contDiff_eventuallyEq_of_contDiffOn : a ContDiffOn-on-an-open-nbhd map extends to a GLOBAL
    ContDiff map agreeing near the point (bump-globalisation).
  * The deepest-point analogue `dln_hchart_residual` is fully built (~2000 lines across 8 files) but uses
    a POLYNOMIAL "selected-loss-entry" chart chartΦ whose inverse is the existence-only IFT inverse Ψsymm
    (so its residual germ q(0,·) is NOT explicitly the reduced core — that is exactly why I need the
    explicit chart instead).
  * exists_jacFlatL2_minor : an invertible nReg×nReg minor of the flat Jacobian exists at any optimal v.

KEY QUESTIONS FOR YOU (rank by importance; be concrete about Lean tactics/lemmas at the v4.29 pin):

Q1. INVERTIBLE DERIVATIVE. The brief suggests computing det J_Φ = ±det X · det(M11)³. But
rlctAtOn_eq_of_contDiff_chart only needs an f':E≃L[ℝ]E with HasFDerivAt Φ (f':E→L E) wstar. Is it cleaner
to AVOID the determinant by: build the EXPLICIT smooth two-sided inverse Ψ_expl, prove Ψ_expl∘Φ_expl =ᶠ id
and Φ_expl∘Ψ_expl =ᶠ id near the base point (matrix-algebra identities), get HasFDerivAt for both, and
conclude DΦ is an ≃L because DΨ is a two-sided inverse of it (differentiating the identities)? If so, what
is the cleanest Mathlib v4.29 construction to turn "CLM A with two-sided CLM inverse Bd" into a
ContinuousLinearEquiv, and to derive HasFDerivAt Φ (that equiv) wstar? Or is there an even cleaner route
(e.g. a Mathlib lemma: local homeomorph that is ContDiff both ways ⟹ invertible fderiv)?

Q2. THE FORWARD MAP IS RATIONAL, but rlctAtOn_eq_of_contDiff_chart needs GLOBAL ContDiff ℝ 2 Φ. Should I
(a) bump-globalise Φ_expl itself via exists_contDiff_eventuallyEq_of_contDiffOn (a matrix-valued/vector-
valued map — does the derivative at the base survive since bump≡1 near base?), or (b) restructure so the
chart map is polynomial and the rationality lives only in F/qₑ? Which minimises Lean pain?

Q3. THE BLOCK REPARAMETRISATION vs FLAT COORDS. Φ_expl is naturally a map between block-structured matrix
spaces, but E must be `Fin (flatDim H)→ℝ`. Recommend the cleanest bridge: define Φ_expl as a self-map of
`Fin (flatDim H)→ℝ` by composing (flat≃blocks homeo) ∘ (block reparam) ∘ (blocks≃flat homeo)? And handle
the Fin r ⊕ Fin (Hs−r) block casts once at the homeo level (never entrywise)? Any traps with
dependent-Fin `HMul` in the block products (M11=XS+YU etc.)?

Q4. THE COMMON INVERTIBLE PIVOT. I need, at v with prod H v = B and rank B = r, a common r×r pivot making
both X (top-left of A0) and M11 (top-left of the product) invertible, WLOG after row/column permutations.
What is the minimal way to establish existence + reduce to the top-left WLOG in Lean (given rank(A0)≥r,
rank(A1)≥r since rank(A0 A1)=r requires both ≥ r; but a common pivot for X AND M11 simultaneously is
stronger)? Is there a slicker choice of the "regular block" p that sidesteps needing X invertible (e.g.
only needing M11 invertible)?

Q5. OVERALL: is my decomposition sound, and what is the SINGLE highest-risk step likely to blow up the
line count or wall me? Give the leanest module/lemma decomposition (5-10 named lemmas) you would build,
bottom-up, to close d1ge_L2_hAtV_explicit.
</task>

<output_contract>
Answer Q1..Q5 in order, each ≤ 12 lines. For Q1 and Q2 give the concrete Mathlib v4.29 lemma names /
construction you'd use (flag any you are unsure exist). End with a single "LEANEST DECOMPOSITION" section:
an ordered list of ≤10 lemma signatures (informal types OK) that closes the target, annotated with
[banked]/[build] and a one-word risk tag (low/med/high). Be concrete; prefer naming a real Mathlib lemma
over hand-waving. If you think a step is actually FALSE or a hidden wall (not mere labour), say so loudly.
</output_contract>

<grounding_rules>
Distinguish (i) Mathlib lemmas you are CONFIDENT exist at v4.29 from (ii) ones you are INFERRING should
exist — tag the latter "(verify)". Do not invent lemma names silently. If a construction needs a lemma
Mathlib likely lacks, say so and give the fallback build. The math (Schur factorisation, dimension count,
det J) is already numerically de-risked — focus on the Lean route, not re-deriving the math.
</grounding_rules>
