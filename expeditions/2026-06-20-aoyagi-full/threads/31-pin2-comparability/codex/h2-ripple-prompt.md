<task>
Confirm or refute a claim about RLCT (real log canonical threshold) invariance under replacing one
nonneg function by another that differs only on a thin (measure-zero) set. This decides whether a
known pointwise bug in an intermediate lemma propagates to a downstream RLCT result.
</task>

<setup>
L=2 DLN, deepest point. Three nonnegative real-analytic functions of the chart coordinates w (near w0=0):
  loss(w) = ‖∏ full layers − B‖²_F   (the true loss)
  Sreg(w) + Score(w),  Score = ‖Rcore‖²_F (Rcore = global (1,1)-Schur complement of the framed deviation)
  Sreg(w) + coreΦ(w),  coreΦ = ‖∏ per-layer reduced Schur cores S'_s‖²_F   (the reduced-chain loss core)

FACTS (established, exact):
 1. loss ≍ Sreg + Score is a GENUINE TWO-SIDED comparability near w0 (banked
    `dlnLoss_two_sided_of_frame`: ∃ constants k1,k2>0 with k1·(Sreg+Score) ≤ loss ≤ k2·(Sreg+Score) on a
    nbhd). Hence rlctAtOn(loss) = rlctAtOn(Sreg+Score).
 2. Sreg + coreΦ is NOT two-sided comparable to loss: there is a reachable thin curve (tilted kernel,
    r=1, M1=2) where loss=0, Sreg=0, but coreΦ=t⁸>0 — so coreΦ overcounts on the locus
    {loss=0, Sreg=0, ∏S'≠0}. Off this thin locus loss grows to match coreΦ (generic ratio →1).
 3. coreΦ and Score differ only on this thin tilted-kernel locus: Score=‖S0(I−K)S1‖², coreΦ=‖S0 S1‖²,
    K=Z1 P00⁻¹ Y0 = O(‖reads‖²); generically coreΦ ≈ Score, but on the tilted-kernel sub-fibre
    K cancels S0 S1 exactly so Score=0 while coreΦ>0.
 4. Numeric RLCT estimates (volume/CDF-slope, 6–8M samples) give, for both the (2,2,2) and (2,3,2)
    anchors, rlctAtOn(Sreg+Score) ≈ rlctAtOn(Sreg+coreΦ) ≈ rlctAtOn(loss) — all three agree to within
    estimator noise (uniform ~0.35 upward bias, identical across the three).
</setup>

<questions>
1. Is it TRUE in general that if f, g ≥ 0 are real-analytic, f ≍ h (two-sided) near 0, and g = f on the
   complement of a measure-zero analytic subset (g ≥ f everywhere, g > f only on that thin set), then
   rlctAtOn(g) = rlctAtOn(f) = rlctAtOn(h)? State the precise condition under which the RLCT is unchanged
   by modifying the function on a thin set. (Note: RLCT is a property of the ZERO SCHEME / the pole of
   ∫ g^{-s}; modifying g on a measure-zero set where g>0 cannot change ∫ g^{-s} — but here g and f differ
   on a set that touches the zero locus {f=0}. Is THAT the danger?)
2. The specific structure: {Sreg+Score = 0} = {loss = 0} (the fibre, since loss ≍ Sreg+Score).
   {Sreg+coreΦ = 0} = {Sreg=0} ∩ {∏S'=0} which is STRICTLY SMALLER than the fibre (it excludes the
   tilted-kernel points where ∏S'≠0 but loss=0). So Sreg+coreΦ has a SMALLER zero locus than loss.
   Does a smaller zero locus give a LARGER, EQUAL, or SMALLER RLCT? Standard theory: fewer zeros ⟹ the
   integral ∫(Sreg+coreΦ)^{-s} converges for MORE s ⟹ LARGER RLCT (less singular). So naively
   rlctAtOn(Sreg+coreΦ) ≥ rlctAtOn(loss), with EQUALITY iff the extra non-zeros are "thin enough" to not
   move the leading pole. Reconcile with the numeric agreement: is the tilted-kernel locus thin enough
   (high enough codimension) that the leading RLCT pole is unmoved?
3. BOTTOM LINE for the build: a downstream recursion R1 resolves rlctAtOn(dlnLoss(reduced chain)) =
   rlctAtOn(coreΦ-as-a-function) via its OWN reduced-chain recursion (NOT via the loss≍Sreg+coreΦ
   comparability — that comparability is only used to TRANSFER rlctAtOn(loss) → rlctAtOn(Sreg+coreΦ)).
   Given the bug is in that transfer (loss≍Sreg+coreΦ is false), but rlctAtOn(Sreg+coreΦ) numerically =
   rlctAtOn(loss): is the headline rlctAtOn(loss) = nReg/2 + rlctAtOn(reduced-chain core) SAFE if we
   re-derive the transfer via Sreg+Score (sound) and SEPARATELY confirm rlctAtOn(Sreg+Score) =
   rlctAtOn(Sreg+coreΦ)? Or is there a trap where the thin tilted-kernel locus DOES move the RLCT?
</questions>

<output_contract>
- Separate FACT (RLCT theory you can state precisely) from INFERENCE.
- Give a definite read on whether modifying loss→Sreg+coreΦ on the thin tilted-kernel locus changes the
  RLCT, with the codimension/thinness condition that makes it safe (or the obstruction if not).
- State whether the headline is SAFE under the Score-restatement + the rlctAtOn(Sreg+Score)=
  rlctAtOn(Sreg+coreΦ) confirmation, or whether the thin locus is a genuine RLCT hazard.
</output_contract>

<grounding_rules>
- RLCT = real log canonical threshold = the smallest pole of ∫_U g(w)^{-s} φ(w) dw (φ smooth bump),
  = the learning coefficient λ in Watanabe's theory. Smaller ⟹ more singular.
- The tilted-kernel locus {loss=0, ∏S'≠0} is where coreΦ>0=loss: it is a proper analytic subset of the
  fibre {loss=0}; estimate its codimension within the ambient and within the fibre.
- Do not assume the numeric agreement is conclusive; give the theoretical reason it should/shouldn't hold.
</grounding_rules>
