You are a decorrelated second opinion on a Lean 4 / Mathlib formalisation sub-problem (RLCT / singular learning theory, Watanabe). I need the CLEANEST proof STRUCTURE (not full Lean code) for a two-sided comparability ε-bound, and a realistic difficulty assessment.

SETTING. On a finite-dim real vector space M = DeepestSplit = R × (C × S) (reg × core × spec), near 0:
- R'(q) : M → R^n  ("reg residual", = deepestEFull q). Smooth (ContDiff ⊤). R'(0)=0.
- Θ : M → M a measure-preserving smooth homeomorphism, Θ0=0, that FIXES the reg slot (q.1) and the spec slot (q.2.2), and SHIFTS ONLY the core slot (q.2.1) by a smooth shift delta(q) that VANISHES at q=0 and is O(|q|²) (a Schur correction). So Θq and q differ only in the core component.
- C(q) : M → R, C ≥ 0 (it's frobSq of a matrix; a "core energy", degenerate/singular as a function of core but always ≥ 0). SAME on both sides below.
- Φ(q) = ∑ᵢ R'(q)ᵢ² + C(q)   ("unmoved")
- F(q) = ∑ᵢ R'(Θq)ᵢ² + C(q)   ("moved")

KEY STRUCTURAL FACTS (all available as lemmas):
1. ATOM (core-constancy on the reg=spec=0 slice): R'(0, c, 0) = R'(0, 0, 0) = 0 for ALL core c. I.e. R' restricted to {reg=0, spec=0} is constant (=0). [So R' reads the core only through cross-terms with reg/spec.]
2. Θ fixes reg+spec, shifts core; Θ0=0; delta(q) smooth, vanishes at 0.
3. PIN-1: the strict derivative dR'(0) : M → R^n, restricted to the reg subspace, is INVERTIBLE (an iso onto R^n via a CLM e). So ∑R'(q)² ≳ ‖reg(q)‖² near 0 (local lower bound from invertible derivative).

GOAL (the ε-bound): ∃ nbhd U of 0, ∀ q ∈ U:  0 ≤ Φ(q)  ∧  (1/2)·Φ(q) ≤ F(q)  ∧  F(q) ≤ (3/2)·Φ(q).
[Then a banked rlctAtOn_squeeze concludes rlctAtOn F 0 = rlctAtOn Φ 0.]

The intended mechanism (from a pen-and-paper cert): ΔR(q) := R'(Θq) − R'(q). Since Θq, q differ only in core, and R' is core-constant on {reg=spec=0} (atom), ΔR VANISHES when (reg,spec)=0, hence ΔR carries a (reg,spec) factor: ‖ΔR(q)‖ ≤ K·‖(reg,spec)(q)‖ near 0. Then F − Φ = ∑(2 R'(q)·ΔR + ΔR²); C cancels. Each term is bounded by ε·∑R'(q)² ≤ ε·Φ using PIN-1 domination (∑R'² ≳ ‖reg‖²) — PROVIDED ‖ΔR‖ is also controlled by ‖reg‖ (the spec part of the ΔR factor must also be dominated, OR ΔR vanishes on {reg=0} alone, not needing spec).

MY QUESTIONS:
(Q1) Is the mechanism sound? In particular: ΔR vanishes when (reg,spec)=0. But PIN-1 only dominates the REG directions (∑R'² ≳ ‖reg‖², not ‖spec‖). If ΔR carries a SPEC factor (not just reg), then ‖ΔR‖ ≤ K‖spec‖ is NOT dominated by ∑R'² (spec is a free direction, R'(0,0,s)=? — by atom only reg=spec=0 forced; what about reg=0, spec≠0?). Does the bound still close, or is there a gap when spec≠0, reg=0? (At reg=0, ∑R'(q)² may be small but ΔR may be nonzero via spec → F could exceed (3/2)Φ. Is this a real obstruction?)
(Q2) What is the cleanest Lean PROOF STRUCTURE? Specifically: (a) how to get ‖ΔR‖ ≤ K‖reg‖ (or ‖(reg,spec)‖) from "R' smooth + R' constant on a subspace" — is this a Hadamard-lemma / `Convex.norm_image_sub_le_of_norm_fderiv_le` mean-value application, or is there a slicker route? (b) the PIN-1 lower bound ∑R'² ≳ ‖reg‖² from an invertible strict derivative — what Mathlib lemma (e.g. `HasStrictFDerivAt` + `ContinuousLinearEquiv` antilipschitz)? (c) assembling the two-sided ratio bound with FIXED constants 1/2, 3/2 on a small enough nbhd.
(Q3) Realistic difficulty: is this a ~1-day or ~multi-day Lean build? What's the single hardest step?

Be skeptical and precise. If the mechanism has a gap (Q1), say so plainly — that's the most valuable output.
