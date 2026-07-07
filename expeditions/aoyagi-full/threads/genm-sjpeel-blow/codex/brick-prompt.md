# Consult: tightest reachable Lean brick for the R1-UPPER (S,J) boundary peel

You are a decorrelated second model on a Lean 4 + Mathlib (v4.29) formalisation. I need a
scope/design read, NOT Lean code. Answer crisply.

## Context
We formalise Aoyagi's general-L R1-UPPER box-finiteness. The load-bearing open lemma is
`sjBoundaryPeel`:

  For a width vector M : Fin(L+3)→ℕ and c' < ½·minAdm M, ∃ finite C with
    routeMLayerBoxIntegral M c' 1  ≤  ∑_{t=0}^{min(M0,M1)} C · jointPeelIntegral M t c'.

The OUTER reduction is already CLOSED (measure-preserving front-split): 
  routeMLayerBoxIntegral M c' 1 = ∫_{A'∈box(tail)} ∫_{A0∈matBox(M0,M1,1)} frobSq(A0·Q)^{-c'},
  Q := prod(tailChain M) A'   (Q is M1×M_L).
And
  jointPeelIntegral M t c' = ∫_{A'∈box(tail)} P_tail_t(Q)^{-(c'-a/2)} · P_full(Q)^{-a/2},
  where a=(M0-t)(M1-t), P_tail_t(Q)=‖top t rows of Q‖² (=frobSqTopRows t Q),
  P_full(Q)=‖Q‖²(=frobSq Q). Note P_full ≥ P_tail. Integrands via Real.rpow inside ENNReal.ofReal
  (so 0^{neg}=0).

## What's BANKED (reusable, sorry-free) 
1. `radial_morse_residual_power_le`: for w>0, c'>(m+1)/2, T>0:
     ∫_{[-T,T]^{m+1}} (∑_i Pᵢ² + w)^{-c'} dP ≤ ofReal(Cresid(m+1) c' · w^{-(c'-(m+1)/2)}).
   (finite-cutoff residual-power; Cresid(n)c' = ∫_{ℝ^n}(‖Q‖²+1)^{-c'} <∞ iff c'>n/2)
2. `integral_core_full_eq`: ∫_{ℝ^n}(‖P‖²+w)^{-c'} = w^{n/2-c'}·Cresid n c'  (w>0).
3. c.o.v. base (RouteMSJPivotChart): schur_cov (Q₁·[[A,B],[C,D]]·Q₂ = diag(A,Γ), Γ=D-CA⁻¹B, det Q=1),
   pivotLocus_eq_iUnion ({A|t≤rank A}=⋃ pivot charts), measurePreserving_shearSub (block shear (x,D)↦(x,D-Kx) is MP).
4. L=2 fibre engine `fibre_lintegral_mul_le`: ∫_{X∈matBox}frobSq(XY)^{-c'} ≤ fibreConst·frobSq(Y)^{-c'}
   (exponent-PRESERVING, undershoots — NOT the shifted residual).

## The math I've verified numerically (exact, ratio 1.0)
- After a pivot chart (t×t block of A0 invertible), Schur c.o.v. exposes corank Γ:(M0-t)×(M1-t),
  ‖A0 Q‖² ≍ ‖Q_top‖² + ‖Γ·Q_bot‖²-type quadratic form. Radial Γ=zV gives ‖A0Q‖²≍ g²+z²h²,
  g=‖Q_top‖, h=‖V Q_bot‖.
- 1-D finite cutoff: ∫₀^R(g²+z²h²)^{-c'}z^{a-1}dz = g^{a-2c'}h^{-a}Φ(Rh/g), Φ(T)=∫₀^T u^{a-1}(1+u²)^{-c'}du.
- ISOTROPIC case (Q_bot isotropic, ‖ΓQ_bot‖²=‖Γ‖²·s²): ∫_{Γ box}(g²+‖Γ‖²s²)^{-c'}dΓ reduces to
  radial_morse_residual_power_le (flatten Γ to Fin a, w=g²=P_tail after s-scaling) → C·P_tail^{-(c'-a/2)}.
  But the ANISOTROPIC ‖ΓQ_bot‖² (general Q_bot) does NOT reduce to ∑Γᵢ²+w; the det/anisotropy of the
  quadratic form is what turns h^{-a} into the finite-cutoff-corrected P_full^{-a/2}.

## Questions (answer each)
1. CONFIRM or REFUTE: fully closing `sjBoundaryPeel` in Lean is a multi-tide effort because the tight
   RHS integrand P_tail^{-(c'-a/2)}·P_full^{-a/2} requires integrating the ANISOTROPIC quadratic form
   ‖Γ·Q_bot‖² over the corank block Γ (coupling to Q_bot's singular values), plus assembling over the
   pivotLocus cover with lintegral_mono_ae on the null degenerate locus — i.e. it is genuinely the
   (S,J) resolution content, not bounded plumbing atop the banked isotropic residual-power bound.
2. Given the banked pieces, what is the SINGLE cleanest, self-contained, genuinely-REUSABLE Lean lemma
   I should land THIS tide as bedrock toward the peel — one that the eventual assembly provably consumes?
   Candidates: (A) an isotropic matrix-fibre residual wrapper ∫_{D∈matBox p q 1}(w+frobSq D)^{-c'}dD ≤
   ofReal(C·w^{-(c'-pq/2)}) reducing to radial_morse_residual_power_le; (B) the anisotropic quadratic-form
   residual bound ∫_{Γ}(g²+‖ΓW‖²)^{-c'}dΓ ≤ C(W)·g^{-(2c'-a)} with C(W) tied to P_full; (C) the polar/1-D
   Beta finiteness ∫₀^R(g²+z²h²)^{-c'}z^{a-1}dz<∞. Which is the RIGHT brick (reused by the assembly, not a
   dead-end), and why? For (A): is the matrix-block→Fin(p*q) flatten + w-scaling to radial_morse_residual_power_le
   a clean ~80-150 line reduction, or are there hidden Mathlib snags (frobSq vs EuclideanSpace norm, the
   box→ball enclosure already handled in the banked lemma)?
3. Any trap in the a.e./null-locus handling (P_tail=0 vs P_full=0, the Real.rpow 0^{neg}=0 convention)
   that changes which brick is safe to state as an unconditional (non-a.e.) reusable lemma?

Be concrete and skeptical. If (A) is a clean win, say so; if it's a dead-end that the assembly won't
actually consume (because the anisotropy is unavoidable), say that plainly and name the brick that IS reused.
