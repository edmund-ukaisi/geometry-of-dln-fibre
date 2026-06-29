# CERTIFICATE: both pi-tilde strict-derivs invertible isos at wstar. (exact, Codex-confirmed)
# Dπ̃(0) = regStraightenTotalCLM2(D_E_full) ∘ D(coreAbsorb.symm)(0).
#  - regStraightenTotalCLM2(L): δ↦(Lδ,δ.2) has block matrix [[L_R,L_C,L_S],[0,I,0],[0,0,I]],
#    det = det(L_R); core/spec columns IRRELEVANT.
#  - D_E_full|reg = D_E|reg - D_E|core·∂g/∂r.  ATOM (D_E|core=0) => = D_E|reg = F.
#  - F = ∂deepestEFull/∂reg(0) = I_3 (PIN-1; verified below).  => regStraightenTotalCLM2 invertible.
#  - D(coreAbsorb.symm)(0) unipotent (det 1) => iso (needs ∂g(0) to exist).
#  => Dπ̃(0) = iso.  SOUND for BOTH bare (g=schurCorrection) and conj (g=schurCorrectionConj) legs.
# CAVEAT: strict-deriv iso is NOT sufficient for ContDiff π̃; that needs g ContDiff:
#   bare: schurCorrection ContDiff (rational, pivot 1) — clean.
#   conj: schurCorrectionConj ContDiff = the CONJ-SMOOTH STACK, holds under hDA (pivot deepBlkA unit).
import sympy as sp
u,v,w,p,q,x,T0,T1=sp.symbols('u v w p q x T0 T1',real=True)
A0=sp.Matrix([[1+u,p],[w,T0]]); A1=sp.Matrix([[1+x,v],[q,T1]]); P=sp.expand(A0*A1)
R=[P[0,0]-1,P[0,1],P[1,0]]; reg=[u,v,w]
F=sp.Matrix([[sp.diff(Ri,rj).subs({k:0 for k in [u,v,w,p,q,x,T0,T1]}) for rj in reg] for Ri in R])
print("F = ∂deepestEFull/∂reg(0) =", F.tolist(), " det =", F.det(), " (invertible:", F.det()!=0, ")")
print("ATOM check ∂deepestEFull/∂core(0):", [[sp.diff(Ri,cj).subs({k:0 for k in [u,v,w,p,q,x,T0,T1]}) for cj in [T0,T1]] for Ri in R], "(all 0 => atom holds)")
