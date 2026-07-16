<task>
A soundness question about an inductive integral-finiteness proof (deep-linear-network RLCT).

SETUP. A chain M=(M0,…,M_last). minAdm(M) = min over t∈[0,min(M0,M1)] of
[peelCharge(t) + minAdm(redChain t M)], where peelCharge(t)=(M0−t)(M1−t) and redChain t M=(t,M2,…,M_last)
is a strictly shorter chain. deepTailMin(M)=min(M2,…,M_last).

A recursion proves "box-finiteness below threshold ½·minAdm(M)" for M, GIVEN it holds for EVERY strictly
shorter chain (a strong IH over all one-shorter chains). The step-proof, to establish M, performs ONE
peel at some cut u: it lands the integrand on redChain u M at the shifted threshold
½·minAdm(M) − ½·peelCharge(u), then closes by the IH on redChain u M. The IH closes iff
½·minAdm(M) − ½·peelCharge(u) ≤ ½·minAdm(redChain u M), i.e. minAdm(M) ≤ peelCharge(u)+minAdm(redChain u M)
— which holds for EVERY u (min ≤ any term). So the threshold closes at any legal cut.

BUT the peel is decomposed into "shells" j∈[0,r], r=min(M0−u_outer, M1−u_outer), and each shell's bound
requires an auxiliary fact `b ≤ deepTailMin(M)`, where b = M1 − (u_outer + j). This auxiliary fact is
KNOWN to hold when u_outer is an ARGMIN of the recursion (minAdm(M) = peelCharge(u_outer)+minAdm(redChain
u_outer M)), but can FAIL at a non-argmin u_outer (for chains of ≥5 widths — a counterexample exists).

The proof HAS a constructor `exists_binding_cut : ∃ u ≤ min(M0,M1), minAdm(M)=peelCharge(u)+minAdm(redChain
u M)` (the argmin), and defines bindingCut(M) = least such u.

QUESTIONS:
 Q1. Is it SOUND for the step-proof to CHOOSE u_outer = bindingCut(M) (the argmin), given the strong IH is
     over ALL one-shorter chains (so redChain u M is a valid IH target for any u)? Any obstruction to this
     free choice?
 Q2. Does choosing u_outer = argmin RECOVER the auxiliary fact `b ≤ deepTailMin(M)` at every shell j (i.e.
     is the argmin property the right and sufficient source)? Argue from: argmin ⟹ minAdm(M) ≤
     peelCharge(u_outer+1)+minAdm(redChain (u_outer+1) M), the algebra peelCharge(u)−peelCharge(u+1) =
     (M0−u)+(M1−u)−1, and the marginal bound minAdm(redChain (u+1) M)−minAdm(redChain u M) ≤ deepTailMin.
 Q3. If a shell-lemma is STATED for a general cut u (no argmin hypothesis) but its conclusion can be
     vacuous/false at non-argmin cuts for ≥5-width chains, and the CONSUMER only ever instantiates it at
     u = argmin — is that a real soundness gap, or a signature-hygiene issue (over-permissive hypotheses)?
     What is the clean fix?
</task>

<output_contract>
Q1: SOUND/UNSOUND + one-line reason. Q2: YES/NO + the derivation (b ≤ deepTailMin at shells). Q3:
real-gap vs hygiene-issue + the clean fix. Label [FACT]/[INFERENCE]. Under 350 words.
</output_contract>

<grounding_rules>
Reason from the stated recursion; do not assume a repo. Flag any step you cannot justify as [INFERENCE].
</grounding_rules>
