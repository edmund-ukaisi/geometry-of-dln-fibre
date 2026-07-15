<task>
Real-analysis adjudication for a change-of-variables finiteness proof (deep linear networks,
RLCT geometry). Withheld conclusion; argue whichever way the mathematics points. This gates a
Lean formalisation: if the ratio below is UNIFORM I build the domination link; if NOT uniform I
STOP and report a sub-gap.

SETUP. A layer chain M = (M₀,M₁,M₂,…,M_last), arity L. At a BINDING cut u = t★+j (t★ = argmin of
the layer recursion, strict shell 1 ≤ j < r = min(M₀−t★, M₁−t★)), set a=M₀−u, b=M₁−u,
ρ = deepTailMin M = min(M₂,…,M_last), n = M_last. The deep factor Z = Z_deep(z_tail) is an M₂×n
product of the deep layers; generically rank Z = ρ, dropping on a measure-zero exceptional set.

The front-charge integral (already reduced, sorry-free up to here) is a fibration over z_tail:
  I := ∫_{z_tail} K(z_tail) dz_tail,  where
  K(z_tail) := ∫_{z0,A_cor,x} frontChargeIntegrand(z_tail, ·)
with q = c' − ab/2 the exponent, ab/2 < c' < T1 := ½·minAdm(M), i.e. 0 < q < T1_q := (minAdm(M)−ab)/2.

The modules (ii)+(iii) resolve the INNER integral per fixed GENERIC z_tail (rank Z = ρ), giving
  K(z_tail) ≤ K₀ · (monomial in the singular values σ₁≥…≥σ_ρ of the rank factor S̃ of Z),
and the effective tail Jacobian carries a factor ≈ (det S̃ᵀS̃)^{−(u+b)/2} = (∏σᵢ²)^{−(u+b)/2}, which
BLOWS UP as z_tail → {rank Z < ρ} (some σᵢ → 0).

The comparator is cornerComparator(redChain u M) with integrand ~ (commonDivisor(z)²·‖Q_p‖²_F)^{−q},
Q_p = z0·Z; its integral is FINITE by the outer induction hypothesis (IH on the one-shorter chain
redChain u M, threshold minAdm(redChain u M)/2 ≥ T1_q). Its loss degenerates at the SAME {rank Z < ρ}.

THE DEEP-DEGENERATION STRATA (independently established, "gap>0" cuts): near {rank Z = ρ−1} (one
deep singular value t := σ_ρ(Z) → 0, codim κ in z_tail, κ=1 for a square bottleneck = worst case),
the leaf loss degenerates as
  loss ≈ |y|² + t²·‖W_lost‖²,  y ∈ ℝ^{ub+u(d−1)} (d=ρ−b), W_lost ∈ ℝ^u,
with RLCT ½(ub + u(d−1) + min(κ,u)) = ½(u(ρ−1)+κ) = ½(C_{s=u}(ρ) − u + κ), and this
codim = minAdm(M) − ab = 2·T1_q EXACTLY (tight, binds at T1_q, verified on probes M=(3,3,3,3),
M=(4,4,4,4)). So finiteness holds for q < T1_q, and DIVERGES for q ∈ (T1_q, ½·min C_{ℓ,s}).

THE QUESTION. Define the matched ratio (integrated over z_tail, NOT pointwise):
  K_{j,c'} := I / cornerComparator(redChain u M).integral(q).
Is K_{j,c'} UNIFORMLY BOUNDED — i.e. is there a finite K_{j,c'} < ∞ (allowed to blow up like
~ 1/(T1−c') as c'↑T1, i.e. ~ 1/(T1_q − q)) that dominates I by K_{j,c'}·(comparator integral),
with the SAME power-law behaviour across the deep-degeneration strata (all rank-drop depths
{rank Z = ρ−1}, {ρ−2}, …, and all κ)? Specifically:
  (Q1) Does the front-charge tail-Jacobian blow-up (∏σᵢ²)^{−(u+b)/2} get DOMINATED by the
       comparator's own {rank Z<ρ} degeneration, stratum-by-stratum, with a ratio that is bounded
       uniformly over the degeneration (only the endpoint pole 1/(T1_q−q) allowed)?
  (Q2) Or is there a rank-drop stratum (some depth, some κ) where the front-charge blows up
       STRICTLY FASTER than the comparator (ratio → ∞ even for fixed q < T1_q) — a genuine
       non-uniformity / sub-gap?
Consider especially: deeper drops rank Z = ρ−2, …; interior-layer bottlenecks; κ > 1; and the
mismatch that the front carries exponent (u+b) in the Jacobian while the comparator carries u only.

<output_contract>
Three sections, terse and decisive:
1. VERDICT: UNIFORM (ratio bounded, only endpoint pole) or NON-UNIFORM (a stratum where front
   out-blows comparator at fixed q<T1_q). One word + one sentence.
2. THE DECIDING COMPUTATION: the stratum-by-stratum codim/RLCT comparison of the two sides at a
   rank-drop of depth (ρ−m), codim κ. Give the exponent of the front-charge blow-up vs the
   comparator blow-up in the small parameter (the vanishing singular value t or the polar radius),
   and whether front ≤ comparator + q-dependent-const uniformly. Show the arithmetic.
3. THE RISK / where a Lean build would break if I proceed assuming UNIFORM.
</output_contract>

<grounding_rules>
Flag inference vs. established fact. If the answer depends on an unstated normalisation of the
comparator, say which normalisation makes it UNIFORM vs NON-UNIFORM. Do not assume the conclusion I
want — I have withheld it deliberately.
</grounding_rules>
