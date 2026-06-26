<task>
I am formalising in Lean 4 / Mathlib a "diffeo bridge" lemma for the RLCT (real log-canonical
threshold) of a deep-linear-network square loss. I have a design cert that says the bridge needs a
heavy "joint (T1,Y1) reparametrization Ψ" (2-3 tides). I want you to RED-TEAM whether a SHORTER route
exists, given the bricks I ALREADY have banked (sorry-free), before I spend the compute on the full Ψ.

THE GOAL (call it hstep2):
  rlctAtOn Φscore wstar = rlctAtOn Φcore wstar
where wstar is a fixed basepoint in flat coordinates ℝ^N, and (for x : ℝ^N):
  Φscore x = reg(x) + Score x
  Φcore  x = reg(x) + deepestCoreF (coreAbsorb (split x)).2.1
  reg(x)   = ∑ i, (regStraighten (split x)).1 i ^ 2          -- SHARED, identical syntactic term
Here `split x` is an affine iso ℝ^N → (Reg × (Core × Spec)); `coreAbsorb` is a homeomorphism that adds
a "cutoff Schur shift" to the Core slot and FIXES Reg and Spec slots.

`rlctAtOn F wstar` is a germ invariant (depends only on F near wstar). I have two transport lemmas:
  (A) rlctAtOn_germ_local : F =ᶠ[𝓝 wstar] G → rlctAtOn F wstar = rlctAtOn G wstar.
  (B) rlctAtOn_comp_localDiffeo : if Psi is ContDiff⊤, HasStrictFDerivAt Psi (e:≃L) wstar, Psi wstar=wstar,
      then rlctAtOn (F∘Psi) wstar = rlctAtOn F wstar.

BANKED BRICKS (all sorry-free):
  (1) deepestCoreF_coreAbsorb_eq_prodSchur : for q in the inner ball (χ=1),
        deepestCoreF (coreAbsorb q).2.1 = frobSq( prod_M ( λ s. core_s(q) + correction_s(q) ) )
      where core_s(q) = (paramsEquivFlat.symm q.2.1) s   (the per-layer Core read),
            correction_s(q) = -Z_s(1+X_s)⁻¹ Y_s          (X_s,Y_s,Z_s read from q's Reg+Spec slots),
            prod_M = product over the L-layer reduced chain, frobSq = ∑∑ entry².
  (2) deepest_loss_squeeze (axiom-clean): a TRUE two-sided sandwich c1·(reg+Score) ≤ dlnLoss∘symm ≤
      c2·(reg+Score) on a 𝓝 — this is what makes Score the RIGHT core quantity. Already used to prove
      hstep1: rlctAt(dlnLoss) = rlctAtOn Φscore wstar.
  (3) rcore_schur_factor_of_corner_split (LDU): for matrices with Mhat = G0·G1 and a corner split,
        Schur(Mw) = Schur(G0) · (1 − K) · Schur(G1),  K = G1₂₁·(M̂₁₁)⁻¹·G0₁₂.
      Score x = frobSq(Schur(Mw(x))) where Mw(x) = reindex(P0·(prod(symm x) − B)·QL).
  (4) split is now a smooth affine chart: ContDiff⊤, HasStrictFDerivAt = a CLE, both directions. (banked)

THE CERT'S Ψ (what I'm trying to avoid if possible): a joint (T1,Y1) action with closed form
  W := I + Z1·A1⁻¹·A0⁻¹·Y0 ; T1' := W⁻¹·[(1−K)S1 + Z1A1⁻¹Y1 + Z1A1⁻¹A0⁻¹Y0T1] ; Y1' := Y1 + A0⁻¹Y0(T1−T1')
cutoff-bumped for global ContDiff⊤ (needs NEW inverse-smoothness lemmas for W⁻¹ and ⅟P00 — flagged as
a watch-item). The cert says a CORE-ONLY Ψ fails because reg(x) reads the Core leak (confirmed:
(regStraighten (split x)).1 = deepestEFull(split x) which reads all three slots incl. Core).

<questions>
1. Is there a route to hstep2 that AVOIDS constructing the full joint (T1,Y1) Ψ with its W⁻¹ inverse?
   Specifically: since brick (2) is a TRUE sandwich and I already proved hstep1 = rlctAtOn Φscore via
   the squeeze, can I get rlctAtOn Φcore by ALSO squeezing dlnLoss against (reg + coreΦ) and using
   the SAME rlctAtOn_squeeze, rather than a diffeo between Φscore and Φcore? I.e. is the cleanest
   thing a SECOND sandwich c1'(reg+coreΦ) ≤ dlnLoss ≤ c2'(reg+coreΦ), giving rlctAtOn Φcore directly,
   so hstep2 follows from BOTH equalling rlctAt(dlnLoss)? What would that second sandwich need (and is
   it easier than the Ψ — e.g. does brick (1)+(3) give frobSq(prod) ~ frobSq(Schur) up to bounded
   factors on a nbhd, which is all a sandwich needs)?

2. If a sandwich route works: brick (1) gives coreΦ = frobSq(prod(core+correction)) on the inner ball,
   and Score = frobSq(Schur(Mw)) = frobSq(S0(1−K)S1) by (3). Are frobSq(prod(core+correction)) and
   frobSq(S0(1−K)S1) two-sided-bounded by each other on a 𝓝 of wstar (where 1−K → 1, the cores match)?
   Note rlctAtOn only needs equality of the RLCT, and rlctAtOn_squeeze needs c1·g ≤ f ≤ c2·g for the
   SAME g on a nbhd — so I need coreΦ and Score sandwiched by each other (both ~ the same g), NOT equal.
   Is THAT the shortcut: prove coreΦ and Score are mutually sandwiched (frobSq is "almost" multiplicative
   and (1−K)→1), bypassing the exact diffeo? Rank this vs the full Ψ for Lean tractability.

3. If NO shortcut (the Ψ is genuinely required), confirm it, and tell me the SINGLE highest-risk
   sub-lemma of the Ψ route (W⁻¹ inverse-smoothness? the LDU absorb S1'=(1−K)S1 through the flat
   paramsEquivFlat encoding? the reg-preservation E2?) so I sequence it first.
</questions>

<output_contract>
Answer in 3 numbered sections matching the 3 questions. For Q1/Q2: a clear YES/NO/MAYBE on the
sandwich shortcut, the precise inequality it would need, and a tractability ranking (sandwich vs Ψ) for
a Lean+Mathlib formalisation. For Q3: name the one riskiest sub-lemma. Be concrete and terse. Flag
explicitly any place you are INFERRING vs reasoning from the stated facts.
</output_contract>
