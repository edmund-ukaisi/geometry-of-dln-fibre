<task>
Adjudicate whether one step of a recursive matrix-integral finiteness proof is WELL-POSED. Give an
independent verdict on 3 sub-questions with exact reasoning. I withhold my conclusion deliberately.
</task>

<setup>
We prove ∀ chains M, box-finiteness `∫_{param box} frobSq(prod M)^{-c'} < ⊤` for c' < ½·minAdm(M), by
strong induction on chain length. The inductive STEP ("one peel") for a chain M = (M0,M1,...,M_L) with
≥3 nodes, GIVEN box-finiteness of every SHORTER chain (the plain IH), must show box-finiteness of M.

The peel (verified banked identities): pivot-chart the leading factor A0 at rank t; Schur-split;
free the corank block Γ (size a×b, a=M0−t, b=M1−t). This rewrites the per-chart integral as
   ∫_{A' = tail params} ∫_{x = (P pivot, B12, C) outer} ∫_{Γ} (freedSchurLoss x Γ Q)^{-c'}
where Q = prod(tailChain M) A'  (the DEEP FACTOR = product of the deeper layers, a (t+b)×q matrix),
Q_b = the b corank rows of Q, Q_p = the t pivot rows, and
   freedSchurLoss = frobSq(P·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b),  Q̃_p = Q_p + P⁻¹·B12·Q_b.

The banked corank atom integrates the inner Γ (over ℝ^{a×b}) EXACTLY, giving, for c' > ab/2 and Q_b of
full row rank (Q_b Q_bᵀ PosDef):
   ∫_Γ (freedSchurLoss)^{-c'} dΓ
     = det(Q_b Q_bᵀ)^{-p/2} · C(ab) · ( w + ‖A·Q̃_p‖² + ‖C·Q̃_p·(I−Π)‖² )^{-(c'−ab/2)},
   p = a,  w = frobSq(P·Q̃_p) > 0,  Π = Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b  (projection onto Q_b's row space).
So the exponent drops by ab/2 (= ½·peelCharge, peelCharge=(M0−t)(M1−t)), landing on the reduced chain
redChain t M (one node shorter). Banked fact: minAdm M ≤ ab + minAdm(redChain t M), so
c'−ab/2 < ½·minAdm(redChain t M) whenever c'<½·minAdm(M) (STRICT). The intended finish: the plain IH
(box-finiteness of redChain t M below its threshold) closes the outer ∫_{A'}∫_x.

Two hypotheses the atom needs FAIL POINTWISE for fixed A': hpiv (w=frobSq(P·Q̃_p)>0) fails where the
deep product degenerates; hG (Q_b Q_bᵀ PosDef) fails on {rank Q_b < b} (the deep factor drops rank).
A separate branch handles c' ≤ ab/2 (bounded, needs only hpiv + finite measure).
</setup>

<questions>
Q1 (is the coupling Jacobian absorbed?). The atom output carries det(Q_b Q_bᵀ)^{-p/2} — a PERSISTENT
   residual weight in A' (Q_b depends on A'). For the plain IH to close the outer ∫_{A'}, this output
   must be ≤ (or =) the redChain-t-M box integrand at exponent c'−ab/2. IS it? Concretely: is
   det(Q_b Q_bᵀ)^{-p/2}·(w+‖A·Q̃_p‖²+‖C·Q̃_p(I−Π)‖²)^{-(c'−ab/2)} equal to (a change-of-variables of)
   frobSq(prod(redChain t M) ·)^{-(c'−ab/2)}, so the det factor is the CoV Jacobian and is absorbed — or
   is det(Q_b Q_bᵀ)^{-p/2} an EXTRA weight the plain box IH does not contain? Reason from the dimensions
   (Γ is a×b, Q_b is b×q with q possibly > b, so Γ↦Γ·Q_b is a projection not a bijection).

Q2 (soundness on the rank-drop locus — the watch-point). The CoV degenerates on {rank Q_b < b}
   (measure-zero in A', but det(Q_b Q_bᵀ)^{-p/2}→∞ there). "hG holds a.e." is TRUE. Is a.e.-holding
   SUFFICIENT for the outer ∫_{A'} to be finite, or is it necessary-not-sufficient (the weight is
   UNBOUNDED near the null locus, so a.e. does not control the integral)? If the deepest layer itself
   drops rank (call it A2-rank-drop, a sub-locus of {rank Q_b<b}), must this be split to a
   higher-codimension ("higher-Mval") branch, or can the recursion's IH on redChain absorb it? Where
   would an RLCT-collapse (loss of the true threshold to a smaller "min-caricature" value) hide if the
   split is done wrong?

Q3 (regime + borderline). regime A needs c'>ab/2, regime B (bounded) covers c'≤ab/2. Is the log-
   borderline c'=ab/2 ever the BINDING finiteness threshold, or is it always strictly interior to
   c'<½·minAdm(M) (so it is handled by the A/B switch, never by the final threshold)? Use
   minAdm M ≤ ab + minAdm(redChain) with minAdm(redChain) ≥ 1.
</questions>

<output_contract>
For each Q1–Q3: a direct answer + "FACT" vs "INFERENCE". End with: is this peel step WELL-POSED (the
atom's a.e. hypotheses = exactly what the outer resolution supplies, and the det coupling is absorbed by
the plain IH) — or does the persistent det(Q_b Q_bᵀ)^{-p/2} coupling require an ANISOTROPIC carrier
(a non-scalar weight tracking the shared divisor) rather than the plain box IH? Isolate the minimal gap.
</output_contract>

<grounding_rules>
Exact algebra / dimension counting. Keep "the majorant/atom-output integral" separate from "the true
integral". If the CoV-Jacobian absorption holds, say so plainly (it makes the step well-posed); if it is
an extra weight, isolate exactly what the plain IH cannot absorb.
