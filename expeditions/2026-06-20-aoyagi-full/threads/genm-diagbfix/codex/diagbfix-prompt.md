<task>
A finiteness question about a matrix integral arising in a deep-linear-network RLCT computation.
Decide whether a specific box integral is FINITE or +∞, and adjudicate a claimed divergence mechanism.
Argue whichever way the math goes; I have withheld my own conclusion.

SETUP (a concrete instance, "uniform width").  Fix integers u=3, a=1, b=1.  Deep matrix
  Z := A2  ∈ ℝ^{4×4}  (entries in the box [-1,1]).
Peeled corank block  A_cor ∈ ℝ^{b×4} = ℝ^{1×4}  (box [-1,1]).
Reduced first layer   A0' ∈ ℝ^{u×4} = ℝ^{3×4}  (box [-1,1]).
Front block           P ∈ ℝ^{3×3} (invertible, box), B ∈ ℝ^{3×1} (box), C ∈ ℝ^{1×3} (box).

Derived:
  Q_p = A0' · Z      (3×4)          "pivot rows"
  Q_b = A_cor · Z    (1×4)          "corank rows"
  charge  = det(Q_b Q_bᵀ)^{-a/2} = ‖Q_b‖^{-1}        (a=b=1; Q_bQ_bᵀ is 1×1)
  Qt      = Q_p + P^{-1} B Q_b                        (3×4)
  E_top   = ‖P·Q_p + B·Q_b‖_F^2                       (3×4)
  Π⊥      = I4 - Q_bᵀ (Q_b Q_bᵀ)^{-1} Q_b            (rank-3 projection off row(Q_b))
  E_tr    = ‖(C·Qt)·Π⊥‖_F^2                           (1×4)
  loss    = E_top + E_tr
  integrand(all vars) = charge · loss^{-q}

THE OBJECT:
  I(q) := ∫ over the full box (A0', Z, A_cor, P, B, C)  charge · loss^{-q}   dvol.

Relevant threshold: the "minimal admissible codimension" of this chain (4,4,4,4) is minAdm = 11;
the claimed finiteness threshold is  q < (minAdm - a·b)/2 = (11-1)/2 = 5.

THE DISPUTED CLAIM (a colleague's, which I am asking you to adjudicate, not endorse):
"I(q) = +∞ for ALL q>0 (even tiny q), because of the deep rank-drop of Z."
Their mechanism: change variables A_cor ↦ Q_b = A_cor·Z (Jacobian dQ_b = |det Z| dA_cor,
so dA_cor = det(ZZᵀ)^{-b/2} dQ_b, the 'coarea prefactor').  They then bound the A_cor-integral of the
charge by a Z-independent 'leaf' integral times this prefactor, obtaining
  ∫_{A_cor box} charge dA_cor  ≤  K · det(ZZᵀ)^{-b/2} · (leaf const),
and observe det(ZZᵀ)^{-b/2} = |det Z|^{-1} is NON-integrable over Z near {det Z = 0} (log-divergent in
codim 1).  They assert (to get divergence, not just a useless upper bound) that this is also a LOWER
bound "needing only inf(fibre volume) > 0 locally", hence I(q) = +∞.

FACTS you may use (each is exact / standard):
(F1) The map A_cor ↦ Q_b = A_cor·Z is linear with Jacobian |det Z| (Z is 4×4). So the honest
     A_cor-box charge integral is
        J(Z) := ∫_{A_cor ∈ [-1,1]^4} ‖A_cor·Z‖^{-1} dA_cor
              = |det Z|^{-1} ∫_{y ∈ Ω_Z} ‖y‖^{-1} dy,   Ω_Z := Zᵀ·[-1,1]^4  (image parallelepiped).
(F2) The scaling identity (exact, homogeneity): under Z = t·Z0 (t→0, full scaling),
        J(t Z0) = |t|^{-a b} J(Z0) = |t|^{-1} J(Z0),
     whereas  det((tZ0)(tZ0)ᵀ)^{-b/2} = |t|^{-b·k} det(Z0 Z0ᵀ)^{-b/2} = |t|^{-4} (·const),  k = 4.
(F3) det(Z Zᵀ)^{-b/2} = |det Z|^{-1} → ∞ in codim 1 as det Z → 0 (one singular value σ→0).

QUESTIONS (answer each, with the discriminating computation):
Q1. Compute the asymptotics of J(Z) = |det Z|^{-1} ∫_{Ω_Z} ‖y‖^{-1} dy as Z → a rank-3 matrix
    (one singular value σ→0, the others O(1)).  Does J(Z) blow up like |det Z|^{-1}, or stay bounded?
    (Hint: Ω_Z is a thin slab of thickness ~σ; ‖y‖^{-1} is integrable in ℝ^4.)
Q2. Is the colleague's LOWER bound (I ≥ c·det(ZZᵀ)^{-b/2}, c=inf fibre vol > 0) valid?  Use F2:
    if J ~ t^{-ab}=t^{-1} but det(ZZᵀ)^{-b/2} ~ t^{-bk}=t^{-4}, what does the "fibre volume"
    L := J / det(ZZᵀ)^{-b/2} do as t→0?  Is inf L > 0?
Q3. THEREFORE: is "det(ZZᵀ)^{-b/2} non-integrable ⟹ I(q)=+∞" a valid inference, or does it only show
    the naive UPPER bound is useless (+∞)?  Distinguish "the naive descent bound is vacuous" from
    "the object diverges".
Q4. Independently of the above, estimate: does I(q) converge for small q (say q=0.5)?  Give the local
    model near the deep rank-drop {rank Z = 3} (codim 1): charge exponent, loss behaviour, deep measure,
    and the resulting radial integral ∫ r^{C-1-2q} dr — is C ≥ 1 there (so finite for small q)?
</task>

<output_contract>
Answer Q1–Q4 in order.  For each: the exact computation/exponent, then a one-line VERDICT.
End with: is the disputed claim "I(q)=+∞ for uniform width" TRUE or FALSE, and the single sharpest
reason.  Be concrete with exponents; do not hedge.  Mark each statement [FACT] (proved/standard) or
[INFERENCE].
</output_contract>

<grounding_rules>
Use only the setup + facts above; you have no repo access.  If you need an assumption, state it.
Distinguish an upper bound (≤) from a lower bound (≥): a divergence proof needs a lower bound.
</grounding_rules>
